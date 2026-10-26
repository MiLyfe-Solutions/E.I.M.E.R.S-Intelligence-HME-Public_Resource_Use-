import V185TrunkScan20Chunk016

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_102174 : List Nat := [4, 3, 2, 2, 2, 1, 1, 3, 2]
def baseStart_102174 : Nat := 118140960795 + 102174 * 2 ^ 59
def prefixEnd_102174 : Nat := 4983230072969 + 3 ^ 40 * 102174 * 2
def baseEnd_102174 : Nat := 46634997682300868848993

theorem tailTrace_102174 : CollatzResearch.WordTrace tailWord_102174 prefixEnd_102174 46634997682300868848993 := by
  unfold tailWord_102174
  simp only [CollatzResearch.WordTrace]
  refine ⟨465823991481065346881197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2484394621232348516699717 465823991481065346881197)
  ·
    refine ⟨174683996805399505080449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 465823991481065346881197 174683996805399505080449)
    ·
      refine ⟨131012997604049628810337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174683996805399505080449 131012997604049628810337)
      ·
        refine ⟨98259748203037221607753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131012997604049628810337 98259748203037221607753)
        ·
          refine ⟨73694811152277916205815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98259748203037221607753 73694811152277916205815)
          ·
            refine ⟨110542216728416874308723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73694811152277916205815 110542216728416874308723)
            ·
              refine ⟨165813325092625311463085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110542216728416874308723 165813325092625311463085)
              ·
                refine ⟨62179996909734491798657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165813325092625311463085 62179996909734491798657)
                ·
                  refine ⟨46634997682300868848993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62179996909734491798657 46634997682300868848993)
                  ·
                    rfl

theorem cell20_102174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_102174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102174 prefixEnd_102174 := by exact prefixLift 102174
  have htrace : WordTrace (prefixWord ++ tailWord_102174) baseStart_102174 baseEnd_102174 := by
    simpa [prefixWord, tailWord_102174, baseEnd_102174] using wordTrace_append hprefix tailTrace_102174
  have hstable : (prefixWord ++ tailWord_102174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102174).length < 2 ^ (prefixWord ++ tailWord_102174).sum := by decide
  have hdescent : baseEnd_102174 < baseStart_102174 := by decide
  rcases family_descends (prefixWord ++ tailWord_102174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102193 : List Nat := [1, 2, 2, 3, 2, 2, 8]
def baseStart_102193 : Nat := 118140960795 + 102193 * 2 ^ 59
def prefixEnd_102193 : Nat := 4983230072969 + 3 ^ 40 * 102193 * 2
def baseEnd_102193 : Nat := 5182629977780138579509

theorem tailTrace_102193 : CollatzResearch.WordTrace tailWord_102193 prefixEnd_102193 5182629977780138579509 := by
  unfold tailWord_102193
  simp only [CollatzResearch.WordTrace]
  refine ⟨3727284918779689019991233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2484856612519792679994155 3727284918779689019991233)
  ·
    refine ⟨2795463689084766764993425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3727284918779689019991233 2795463689084766764993425)
    ·
      refine ⟨2096597766813575073745069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2795463689084766764993425 2096597766813575073745069)
      ·
        refine ⟨786224162555090652654401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2096597766813575073745069 786224162555090652654401)
        ·
          refine ⟨589668121916317989490801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 786224162555090652654401 589668121916317989490801)
          ·
            refine ⟨442251091437238492118101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 589668121916317989490801 442251091437238492118101)
            ·
              refine ⟨5182629977780138579509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 442251091437238492118101 5182629977780138579509)
              ·
                rfl

theorem cell20_102193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 8].length) (baseStart_102193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102193 prefixEnd_102193 := by exact prefixLift 102193
  have htrace : WordTrace (prefixWord ++ tailWord_102193) baseStart_102193 baseEnd_102193 := by
    simpa [prefixWord, tailWord_102193, baseEnd_102193] using wordTrace_append hprefix tailTrace_102193
  have hstable : (prefixWord ++ tailWord_102193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102193).length < 2 ^ (prefixWord ++ tailWord_102193).sum := by decide
  have hdescent : baseEnd_102193 < baseStart_102193 := by decide
  rcases family_descends (prefixWord ++ tailWord_102193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102196 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 5]
def baseStart_102196 : Nat := 118140960795 + 102196 * 2 ^ 59
def prefixEnd_102196 : Nat := 4983230072969 + 3 ^ 40 * 102196 * 2
def baseEnd_102196 : Nat := 46645039081766570115569

theorem tailTrace_102196 : CollatzResearch.WordTrace tailWord_102196 prefixEnd_102196 46645039081766570115569 := by
  unfold tailWord_102196
  simp only [CollatzResearch.WordTrace]
  refine ⟨1863697168884410266175221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2484929558512547021566961 1863697168884410266175221)
  ·
    refine ⟨174721609582913462453927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1863697168884410266175221 174721609582913462453927)
    ·
      refine ⟨262082414374370193680891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174721609582913462453927 262082414374370193680891)
      ·
        refine ⟨393123621561555290521337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262082414374370193680891 393123621561555290521337)
        ·
          refine ⟨294842716171166467891003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393123621561555290521337 294842716171166467891003)
          ·
            refine ⟨442264074256749701836505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294842716171166467891003 442264074256749701836505)
            ·
              refine ⟨331698055692562276377379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442264074256749701836505 331698055692562276377379)
              ·
                refine ⟨497547083538843414566069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331698055692562276377379 497547083538843414566069)
                ·
                  refine ⟨46645039081766570115569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 497547083538843414566069 46645039081766570115569)
                  ·
                    rfl

theorem cell20_102196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_102196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102196 prefixEnd_102196 := by exact prefixLift 102196
  have htrace : WordTrace (prefixWord ++ tailWord_102196) baseStart_102196 baseEnd_102196 := by
    simpa [prefixWord, tailWord_102196, baseEnd_102196] using wordTrace_append hprefix tailTrace_102196
  have hstable : (prefixWord ++ tailWord_102196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102196).length < 2 ^ (prefixWord ++ tailWord_102196).sum := by decide
  have hdescent : baseEnd_102196 < baseStart_102196 := by decide
  rcases family_descends (prefixWord ++ tailWord_102196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102217 : List Nat := [1, 2, 1, 1, 2, 4, 3, 3, 3]
def baseStart_102217 : Nat := 118140960795 + 102217 * 2 ^ 59
def prefixEnd_102217 : Nat := 4983230072969 + 3 ^ 40 * 102217 * 2
def baseEnd_102217 : Nat := 46654624053983830415483

theorem tailTrace_102217 : CollatzResearch.WordTrace tailWord_102217 prefixEnd_102217 46654624053983830415483 := by
  unfold tailWord_102217
  simp only [CollatzResearch.WordTrace]
  refine ⟨3728160270692741118864905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2485440180461827412576603 3728160270692741118864905)
  ·
    refine ⟨2796120203019555839148679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3728160270692741118864905 2796120203019555839148679)
    ·
      refine ⟨4194180304529333758723019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2796120203019555839148679 4194180304529333758723019)
      ·
        refine ⟨6291270456794000638084529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4194180304529333758723019 6291270456794000638084529)
        ·
          refine ⟨4718452842595500478563397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6291270456794000638084529 4718452842595500478563397)
          ·
            refine ⟨884709907986656339730637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4718452842595500478563397 884709907986656339730637)
            ·
              refine ⟨331766215494996127398989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 884709907986656339730637 331766215494996127398989)
              ·
                refine ⟨124412330810623547774621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331766215494996127398989 124412330810623547774621)
                ·
                  refine ⟨46654624053983830415483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124412330810623547774621 46654624053983830415483)
                  ·
                    rfl

theorem cell20_102217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_102217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102217 prefixEnd_102217 := by exact prefixLift 102217
  have htrace : WordTrace (prefixWord ++ tailWord_102217) baseStart_102217 baseEnd_102217 := by
    simpa [prefixWord, tailWord_102217, baseEnd_102217] using wordTrace_append hprefix tailTrace_102217
  have hstable : (prefixWord ++ tailWord_102217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102217).length < 2 ^ (prefixWord ++ tailWord_102217).sum := by decide
  have hdescent : baseEnd_102217 < baseStart_102217 := by decide
  rcases family_descends (prefixWord ++ tailWord_102217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102241 : List Nat := [1, 2, 3, 1, 1, 1, 4, 5, 2]
def baseStart_102241 : Nat := 118140960795 + 102241 * 2 ^ 59
def prefixEnd_102241 : Nat := 4983230072969 + 3 ^ 40 * 102241 * 2
def baseEnd_102241 : Nat := 46665578307946413615385

theorem tailTrace_102241 : CollatzResearch.WordTrace tailWord_102241 prefixEnd_102241 46665578307946413615385 := by
  unfold tailWord_102241
  simp only [CollatzResearch.WordTrace]
  refine ⟨3729035622605793217738577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2486023748403862145159051 3729035622605793217738577)
  ·
    refine ⟨2796776716954344913303933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3729035622605793217738577 2796776716954344913303933)
    ·
      refine ⟨1048791268857879342488975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2796776716954344913303933 1048791268857879342488975)
      ·
        refine ⟨1573186903286819013733463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1048791268857879342488975 1573186903286819013733463)
        ·
          refine ⟨2359780354930228520600195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1573186903286819013733463 2359780354930228520600195)
          ·
            refine ⟨3539670532395342780900293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2359780354930228520600195 3539670532395342780900293)
            ·
              refine ⟨663688224824126771418805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3539670532395342780900293 663688224824126771418805)
              ·
                refine ⟨62220771077261884820513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 663688224824126771418805 62220771077261884820513)
                ·
                  refine ⟨46665578307946413615385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62220771077261884820513 46665578307946413615385)
                  ·
                    rfl

theorem cell20_102241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 2].length) (baseStart_102241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102241 prefixEnd_102241 := by exact prefixLift 102241
  have htrace : WordTrace (prefixWord ++ tailWord_102241) baseStart_102241 baseEnd_102241 := by
    simpa [prefixWord, tailWord_102241, baseEnd_102241] using wordTrace_append hprefix tailTrace_102241
  have hstable : (prefixWord ++ tailWord_102241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102241).length < 2 ^ (prefixWord ++ tailWord_102241).sum := by decide
  have hdescent : baseEnd_102241 < baseStart_102241 := by decide
  rcases family_descends (prefixWord ++ tailWord_102241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102254 : List Nat := [4, 1, 2, 3, 1, 3, 2, 2, 2]
def baseStart_102254 : Nat := 118140960795 + 102254 * 2 ^ 59
def prefixEnd_102254 : Nat := 4983230072969 + 3 ^ 40 * 102254 * 2
def baseEnd_102254 : Nat := 46671511862176146181999

theorem tailTrace_102254 : CollatzResearch.WordTrace tailWord_102254 prefixEnd_102254 46671511862176146181999 := by
  unfold tailWord_102254
  simp only [CollatzResearch.WordTrace]
  refine ⟨466188721444837054745227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2486339847705797625307877 466188721444837054745227)
  ·
    refine ⟨699283082167255582117841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 466188721444837054745227 699283082167255582117841)
    ·
      refine ⟨524462311625441686588381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 699283082167255582117841 524462311625441686588381)
      ·
        refine ⟨196673366859540632470643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 524462311625441686588381 196673366859540632470643)
        ·
          refine ⟨295010050289310948705965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196673366859540632470643 295010050289310948705965)
          ·
            refine ⟨110628768858491605764737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295010050289310948705965 110628768858491605764737)
            ·
              refine ⟨82971576643868704323553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110628768858491605764737 82971576643868704323553)
              ·
                refine ⟨62228682482901528242665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82971576643868704323553 62228682482901528242665)
                ·
                  refine ⟨46671511862176146181999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62228682482901528242665 46671511862176146181999)
                  ·
                    rfl

theorem cell20_102254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_102254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102254 prefixEnd_102254 := by exact prefixLift 102254
  have htrace : WordTrace (prefixWord ++ tailWord_102254) baseStart_102254 baseEnd_102254 := by
    simpa [prefixWord, tailWord_102254, baseEnd_102254] using wordTrace_append hprefix tailTrace_102254
  have hstable : (prefixWord ++ tailWord_102254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102254).length < 2 ^ (prefixWord ++ tailWord_102254).sum := by decide
  have hdescent : baseEnd_102254 < baseStart_102254 := by decide
  rcases family_descends (prefixWord ++ tailWord_102254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102279 : List Nat := [1, 1, 4, 2, 4, 1, 1, 2, 4]
def baseStart_102279 : Nat := 118140960795 + 102279 * 2 ^ 59
def prefixEnd_102279 : Nat := 4983230072969 + 3 ^ 40 * 102279 * 2
def baseEnd_102279 : Nat := 46682922543387170348563

theorem tailTrace_102279 : CollatzResearch.WordTrace tailWord_102279 prefixEnd_102279 46682922543387170348563 := by
  unfold tailWord_102279
  simp only [CollatzResearch.WordTrace]
  refine ⟨3730421596468125707621891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2486947730978750471747927 3730421596468125707621891)
  ·
    refine ⟨5595632394702188561432837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3730421596468125707621891 5595632394702188561432837)
    ·
      refine ⟨1049181074006660355268657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5595632394702188561432837 1049181074006660355268657)
      ·
        refine ⟨786885805504995266451493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1049181074006660355268657 786885805504995266451493)
        ·
          refine ⟨147541088532186612459655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 786885805504995266451493 147541088532186612459655)
          ·
            refine ⟨221311632798279918689483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147541088532186612459655 221311632798279918689483)
            ·
              refine ⟨331967449197419878034225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221311632798279918689483 331967449197419878034225)
              ·
                refine ⟨248975586898064908525669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331967449197419878034225 248975586898064908525669)
                ·
                  refine ⟨46682922543387170348563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248975586898064908525669 46682922543387170348563)
                  ·
                    rfl

theorem cell20_102279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 4].length) (baseStart_102279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102279 prefixEnd_102279 := by exact prefixLift 102279
  have htrace : WordTrace (prefixWord ++ tailWord_102279) baseStart_102279 baseEnd_102279 := by
    simpa [prefixWord, tailWord_102279, baseEnd_102279] using wordTrace_append hprefix tailTrace_102279
  have hstable : (prefixWord ++ tailWord_102279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102279).length < 2 ^ (prefixWord ++ tailWord_102279).sum := by decide
  have hdescent : baseEnd_102279 < baseStart_102279 := by decide
  rcases family_descends (prefixWord ++ tailWord_102279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102306 : List Nat := [3, 3, 1, 2, 4, 1, 1, 2, 3]
def baseStart_102306 : Nat := 118140960795 + 102306 * 2 ^ 59
def prefixEnd_102306 : Nat := 4983230072969 + 3 ^ 40 * 102306 * 2
def baseEnd_102306 : Nat := 46695246079095076448453

theorem tailTrace_102306 : CollatzResearch.WordTrace tailWord_102306 prefixEnd_102306 46695246079095076448453 := by
  unfold tailWord_102306
  simp only [CollatzResearch.WordTrace]
  refine ⟨932851591842577329713693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2487604244913539545903181 932851591842577329713693)
  ·
    refine ⟨349819346940966498642635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 932851591842577329713693 349819346940966498642635)
    ·
      refine ⟨524729020411449747963953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349819346940966498642635 524729020411449747963953)
      ·
        refine ⟨393546765308587310972965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524729020411449747963953 393546765308587310972965)
        ·
          refine ⟨73790018495360120807431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 393546765308587310972965 73790018495360120807431)
          ·
            refine ⟨110685027743040181211147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73790018495360120807431 110685027743040181211147)
            ·
              refine ⟨166027541614560271816721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110685027743040181211147 166027541614560271816721)
              ·
                refine ⟨124520656210920203862541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166027541614560271816721 124520656210920203862541)
                ·
                  refine ⟨46695246079095076448453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124520656210920203862541 46695246079095076448453)
                  ·
                    rfl

theorem cell20_102306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_102306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102306 prefixEnd_102306 := by exact prefixLift 102306
  have htrace : WordTrace (prefixWord ++ tailWord_102306) baseStart_102306 baseEnd_102306 := by
    simpa [prefixWord, tailWord_102306, baseEnd_102306] using wordTrace_append hprefix tailTrace_102306
  have hstable : (prefixWord ++ tailWord_102306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102306).length < 2 ^ (prefixWord ++ tailWord_102306).sum := by decide
  have hdescent : baseEnd_102306 < baseStart_102306 := by decide
  rcases family_descends (prefixWord ++ tailWord_102306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102352 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 5]
def baseStart_102352 : Nat := 118140960795 + 102352 * 2 ^ 59
def prefixEnd_102352 : Nat := 4983230072969 + 3 ^ 40 * 102352 * 2
def baseEnd_102352 : Nat := 46716241732523360914931

theorem tailTrace_102352 : CollatzResearch.WordTrace tailWord_102352 prefixEnd_102352 46716241732523360914931 := by
  unfold tailWord_102352
  simp only [CollatzResearch.WordTrace]
  refine ⟨1866542062601829587514655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2488722750135772783352873 1866542062601829587514655)
  ·
    refine ⟨2799813093902744381271983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1866542062601829587514655 2799813093902744381271983)
    ·
      refine ⟨4199719640854116571907975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2799813093902744381271983 4199719640854116571907975)
      ·
        refine ⟨6299579461281174857861963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4199719640854116571907975 6299579461281174857861963)
        ·
          refine ⟨9449369191921762286792945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6299579461281174857861963 9449369191921762286792945)
          ·
            refine ⟨7087026893941321715094709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9449369191921762286792945 7087026893941321715094709)
            ·
              refine ⟨664408771306998910790129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7087026893941321715094709 664408771306998910790129)
              ·
                refine ⟨498306578480249183092597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 664408771306998910790129 498306578480249183092597)
                ·
                  refine ⟨46716241732523360914931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 498306578480249183092597 46716241732523360914931)
                  ·
                    rfl

theorem cell20_102352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_102352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102352 prefixEnd_102352 := by exact prefixLift 102352
  have htrace : WordTrace (prefixWord ++ tailWord_102352) baseStart_102352 baseEnd_102352 := by
    simpa [prefixWord, tailWord_102352, baseEnd_102352] using wordTrace_append hprefix tailTrace_102352
  have hstable : (prefixWord ++ tailWord_102352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102352).length < 2 ^ (prefixWord ++ tailWord_102352).sum := by decide
  have hdescent : baseEnd_102352 < baseStart_102352 := by decide
  rcases family_descends (prefixWord ++ tailWord_102352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102358 : List Nat := [5, 2, 1, 1, 4, 1, 6]
def baseStart_102358 : Nat := 118140960795 + 102358 * 2 ^ 59
def prefixEnd_102358 : Nat := 4983230072969 + 3 ^ 40 * 102358 * 2
def baseEnd_102358 : Nat := 5190997810668222968323

theorem tailTrace_102358 : CollatzResearch.WordTrace tailWord_102358 prefixEnd_102358 5190997810668222968323 := by
  unfold tailWord_102358
  simp only [CollatzResearch.WordTrace]
  refine ⟨233331435198870137484233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2488868642121281466498485 233331435198870137484233)
  ·
    refine ⟨174998576399152603113175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233331435198870137484233 174998576399152603113175)
    ·
      refine ⟨262497864598728904669763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174998576399152603113175 262497864598728904669763)
      ·
        refine ⟨393746796898093357004645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262497864598728904669763 393746796898093357004645)
        ·
          refine ⟨73827524418392504438371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 393746796898093357004645 73827524418392504438371)
          ·
            refine ⟨110741286627588756657557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73827524418392504438371 110741286627588756657557)
            ·
              refine ⟨5190997810668222968323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110741286627588756657557 5190997810668222968323)
              ·
                rfl

theorem cell20_102358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 6].length) (baseStart_102358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102358 prefixEnd_102358 := by exact prefixLift 102358
  have htrace : WordTrace (prefixWord ++ tailWord_102358) baseStart_102358 baseEnd_102358 := by
    simpa [prefixWord, tailWord_102358, baseEnd_102358] using wordTrace_append hprefix tailTrace_102358
  have hstable : (prefixWord ++ tailWord_102358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102358).length < 2 ^ (prefixWord ++ tailWord_102358).sum := by decide
  have hdescent : baseEnd_102358 < baseStart_102358 := by decide
  rcases family_descends (prefixWord ++ tailWord_102358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102362 : List Nat := [3, 1, 1, 2, 5, 2, 6]
def baseStart_102362 : Nat := 118140960795 + 102362 * 2 ^ 59
def prefixEnd_102362 : Nat := 4983230072969 + 3 ^ 40 * 102362 * 2
def baseEnd_102362 : Nat := 5191200667223085620173

theorem tailTrace_102362 : CollatzResearch.WordTrace tailWord_102362 prefixEnd_102362 5191200667223085620173 := by
  unfold tailWord_102362
  simp only [CollatzResearch.WordTrace]
  refine ⟨933362213791857720723335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2488965903444953921928893 933362213791857720723335)
  ·
    refine ⟨1400043320687786581085003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 933362213791857720723335 1400043320687786581085003)
    ·
      refine ⟨2100064981031679871627505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1400043320687786581085003 2100064981031679871627505)
      ·
        refine ⟨1575048735773759903720629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2100064981031679871627505 1575048735773759903720629)
        ·
          refine ⟨147660818978789990973809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1575048735773759903720629 147660818978789990973809)
          ·
            refine ⟨110745614234092493230357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147660818978789990973809 110745614234092493230357)
            ·
              refine ⟨5191200667223085620173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110745614234092493230357 5191200667223085620173)
              ·
                rfl

theorem cell20_102362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 6].length) (baseStart_102362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102362 prefixEnd_102362 := by exact prefixLift 102362
  have htrace : WordTrace (prefixWord ++ tailWord_102362) baseStart_102362 baseEnd_102362 := by
    simpa [prefixWord, tailWord_102362, baseEnd_102362] using wordTrace_append hprefix tailTrace_102362
  have hstable : (prefixWord ++ tailWord_102362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102362).length < 2 ^ (prefixWord ++ tailWord_102362).sum := by decide
  have hdescent : baseEnd_102362 < baseStart_102362 := by decide
  rcases family_descends (prefixWord ++ tailWord_102362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102372 : List Nat := [2, 3, 1, 1, 1, 1, 7, 2, 2]
def baseStart_102372 : Nat := 118140960795 + 102372 * 2 ^ 59
def prefixEnd_102372 : Nat := 4983230072969 + 3 ^ 40 * 102372 * 2
def baseEnd_102372 : Nat := 46725370277492180248183

theorem tailTrace_102372 : CollatzResearch.WordTrace tailWord_102372 prefixEnd_102372 46725370277492180248183 := by
  unfold tailWord_102372
  simp only [CollatzResearch.WordTrace]
  refine ⟨1866906792565601295378685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2489209056754135060504913 1866906792565601295378685)
  ·
    refine ⟨700090047212100485767007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1866906792565601295378685 700090047212100485767007)
    ·
      refine ⟨1050135070818150728650511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 700090047212100485767007 1050135070818150728650511)
      ·
        refine ⟨1575202606227226092975767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1050135070818150728650511 1575202606227226092975767)
        ·
          refine ⟨2362803909340839139463651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1575202606227226092975767 2362803909340839139463651)
          ·
            refine ⟨3544205864011258709195477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2362803909340839139463651 3544205864011258709195477)
            ·
              refine ⟨83067324937763875996769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3544205864011258709195477 83067324937763875996769)
              ·
                refine ⟨62300493703322906997577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83067324937763875996769 62300493703322906997577)
                ·
                  refine ⟨46725370277492180248183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62300493703322906997577 46725370277492180248183)
                  ·
                    rfl

theorem cell20_102372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_102372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102372 prefixEnd_102372 := by exact prefixLift 102372
  have htrace : WordTrace (prefixWord ++ tailWord_102372) baseStart_102372 baseEnd_102372 := by
    simpa [prefixWord, tailWord_102372, baseEnd_102372] using wordTrace_append hprefix tailTrace_102372
  have hstable : (prefixWord ++ tailWord_102372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102372).length < 2 ^ (prefixWord ++ tailWord_102372).sum := by decide
  have hdescent : baseEnd_102372 < baseStart_102372 := by decide
  rcases family_descends (prefixWord ++ tailWord_102372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102383 : List Nat := [1, 1, 2, 1, 4, 2, 4, 5]
def baseStart_102383 : Nat := 118140960795 + 102383 * 2 ^ 59
def prefixEnd_102383 : Nat := 4983230072969 + 3 ^ 40 * 102383 * 2
def baseEnd_102383 : Nat := 15576796992408343627157

theorem tailTrace_102383 : CollatzResearch.WordTrace tailWord_102383 prefixEnd_102383 15576796992408343627157 := by
  unfold tailWord_102383
  simp only [CollatzResearch.WordTrace]
  refine ⟨3734214788091351469407803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2489476525394234312938535 3734214788091351469407803)
  ·
    refine ⟨5601322182137027204111705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3734214788091351469407803 5601322182137027204111705)
    ·
      refine ⟨4200991636602770403083779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5601322182137027204111705 4200991636602770403083779)
      ·
        refine ⟨6301487454904155604625669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4200991636602770403083779 6301487454904155604625669)
        ·
          refine ⟨1181528897794529175867313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6301487454904155604625669 1181528897794529175867313)
          ·
            refine ⟨886146673345896881900485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1181528897794529175867313 886146673345896881900485)
            ·
              refine ⟨166152501252355665356341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 886146673345896881900485 166152501252355665356341)
              ·
                refine ⟨15576796992408343627157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166152501252355665356341 15576796992408343627157)
                ·
                  rfl

theorem cell20_102383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 5].length) (baseStart_102383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102383 prefixEnd_102383 := by exact prefixLift 102383
  have htrace : WordTrace (prefixWord ++ tailWord_102383) baseStart_102383 baseEnd_102383 := by
    simpa [prefixWord, tailWord_102383, baseEnd_102383] using wordTrace_append hprefix tailTrace_102383
  have hstable : (prefixWord ++ tailWord_102383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102383).length < 2 ^ (prefixWord ++ tailWord_102383).sum := by decide
  have hdescent : baseEnd_102383 < baseStart_102383 := by decide
  rcases family_descends (prefixWord ++ tailWord_102383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102420 : List Nat := [2, 4, 3, 2, 1, 1, 2, 2, 3]
def baseStart_102420 : Nat := 118140960795 + 102420 * 2 ^ 59
def prefixEnd_102420 : Nat := 4983230072969 + 3 ^ 40 * 102420 * 2
def baseEnd_102420 : Nat := 46747278785417346647987

theorem tailTrace_102420 : CollatzResearch.WordTrace tailWord_102420 prefixEnd_102420 46747278785417346647987 := by
  unfold tailWord_102420
  simp only [CollatzResearch.WordTrace]
  refine ⟨1867782144478653394252357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2490376192638204525669809 1867782144478653394252357)
  ·
    refine ⟨350209152089747511422317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1867782144478653394252357 350209152089747511422317)
    ·
      refine ⟨131328432033655316783369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350209152089747511422317 131328432033655316783369)
      ·
        refine ⟨98496324025241487587527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131328432033655316783369 98496324025241487587527)
        ·
          refine ⟨147744486037862231381291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98496324025241487587527 147744486037862231381291)
          ·
            refine ⟨221616729056793347071937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147744486037862231381291 221616729056793347071937)
            ·
              refine ⟨166212546792595010303953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221616729056793347071937 166212546792595010303953)
              ·
                refine ⟨124659410094446257727965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166212546792595010303953 124659410094446257727965)
                ·
                  refine ⟨46747278785417346647987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124659410094446257727965 46747278785417346647987)
                  ·
                    rfl

theorem cell20_102420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_102420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102420 prefixEnd_102420 := by exact prefixLift 102420
  have htrace : WordTrace (prefixWord ++ tailWord_102420) baseStart_102420 baseEnd_102420 := by
    simpa [prefixWord, tailWord_102420, baseEnd_102420] using wordTrace_append hprefix tailTrace_102420
  have hstable : (prefixWord ++ tailWord_102420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102420).length < 2 ^ (prefixWord ++ tailWord_102420).sum := by decide
  have hdescent : baseEnd_102420 < baseStart_102420 := by decide
  rcases family_descends (prefixWord ++ tailWord_102420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102421 : List Nat := [1, 3, 2, 1, 5, 8]
def baseStart_102421 : Nat := 118140960795 + 102421 * 2 ^ 59
def prefixEnd_102421 : Nat := 4983230072969 + 3 ^ 40 * 102421 * 2
def baseEnd_102421 : Nat := 1731397600469103244987

theorem tailTrace_102421 : CollatzResearch.WordTrace tailWord_102421 prefixEnd_102421 1731397600469103244987 := by
  unfold tailWord_102421
  simp only [CollatzResearch.WordTrace]
  refine ⟨3735600761953683959291117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2490400507969122639527411 3735600761953683959291117)
  ·
    refine ⟨1400850285732631484734169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3735600761953683959291117 1400850285732631484734169)
    ·
      refine ⟨1050637714299473613550627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1400850285732631484734169 1050637714299473613550627)
      ·
        refine ⟨1575956571449210420325941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1050637714299473613550627 1575956571449210420325941)
        ·
          refine ⟨147745928573363476905557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1575956571449210420325941 147745928573363476905557)
          ·
            refine ⟨1731397600469103244987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 147745928573363476905557 1731397600469103244987)
            ·
              rfl

theorem cell20_102421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 8].length) (baseStart_102421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102421 prefixEnd_102421 := by exact prefixLift 102421
  have htrace : WordTrace (prefixWord ++ tailWord_102421) baseStart_102421 baseEnd_102421 := by
    simpa [prefixWord, tailWord_102421, baseEnd_102421] using wordTrace_append hprefix tailTrace_102421
  have hstable : (prefixWord ++ tailWord_102421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102421).length < 2 ^ (prefixWord ++ tailWord_102421).sum := by decide
  have hdescent : baseEnd_102421 < baseStart_102421 := by decide
  rcases family_descends (prefixWord ++ tailWord_102421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102431 : List Nat := [1, 1, 2, 4, 1, 2, 3, 4, 2]
def baseStart_102431 : Nat := 118140960795 + 102431 * 2 ^ 59
def prefixEnd_102431 : Nat := 4983230072969 + 3 ^ 40 * 102431 * 2
def baseEnd_102431 : Nat := 46752299485150197281275

theorem tailTrace_102431 : CollatzResearch.WordTrace tailWord_102431 prefixEnd_102431 46752299485150197281275 := by
  unfold tailWord_102431
  simp only [CollatzResearch.WordTrace]
  refine ⟨3735965491917455667155147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2490643661278303778103431 3735965491917455667155147)
  ·
    refine ⟨5603948237876183500732721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3735965491917455667155147 5603948237876183500732721)
    ·
      refine ⟨4202961178407137625549541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5603948237876183500732721 4202961178407137625549541)
      ·
        refine ⟨788055220951338304790539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4202961178407137625549541 788055220951338304790539)
        ·
          refine ⟨1182082831427007457185809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 788055220951338304790539 1182082831427007457185809)
          ·
            refine ⟨886562123570255592889357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1182082831427007457185809 886562123570255592889357)
            ·
              refine ⟨332460796338845847333509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 886562123570255592889357 332460796338845847333509)
              ·
                refine ⟨62336399313533596375033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 332460796338845847333509 62336399313533596375033)
                ·
                  refine ⟨46752299485150197281275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62336399313533596375033 46752299485150197281275)
                  ·
                    rfl

theorem cell20_102431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 2].length) (baseStart_102431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102431 prefixEnd_102431 := by exact prefixLift 102431
  have htrace : WordTrace (prefixWord ++ tailWord_102431) baseStart_102431 baseEnd_102431 := by
    simpa [prefixWord, tailWord_102431, baseEnd_102431] using wordTrace_append hprefix tailTrace_102431
  have hstable : (prefixWord ++ tailWord_102431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102431).length < 2 ^ (prefixWord ++ tailWord_102431).sum := by decide
  have hdescent : baseEnd_102431 < baseStart_102431 := by decide
  rcases family_descends (prefixWord ++ tailWord_102431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102473 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 6]
def baseStart_102473 : Nat := 118140960795 + 102473 * 2 ^ 59
def prefixEnd_102473 : Nat := 4983230072969 + 3 ^ 40 * 102473 * 2
def baseEnd_102473 : Nat := 46771469429584717881103

theorem tailTrace_102473 : CollatzResearch.WordTrace tailWord_102473 prefixEnd_102473 46771469429584717881103 := by
  unfold tailWord_102473
  simp only [CollatzResearch.WordTrace]
  refine ⟨3737497357765296840184073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2491664905176864560122715 3737497357765296840184073)
  ·
    refine ⟨2803123018323972630138055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3737497357765296840184073 2803123018323972630138055)
    ·
      refine ⟨4204684527485958945207083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2803123018323972630138055 4204684527485958945207083)
      ·
        refine ⟨6307026791228938417810625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4204684527485958945207083 6307026791228938417810625)
        ·
          refine ⟨4730270093421703813357969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6307026791228938417810625 4730270093421703813357969)
          ·
            refine ⟨3547702570066277860018477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4730270093421703813357969 3547702570066277860018477)
            ·
              refine ⟨1330388463774854197506929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3547702570066277860018477 1330388463774854197506929)
              ·
                refine ⟨997791347831140648130197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1330388463774854197506929 997791347831140648130197)
                ·
                  refine ⟨46771469429584717881103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 997791347831140648130197 46771469429584717881103)
                  ·
                    rfl

theorem cell20_102473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_102473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102473 prefixEnd_102473 := by exact prefixLift 102473
  have htrace : WordTrace (prefixWord ++ tailWord_102473) baseStart_102473 baseEnd_102473 := by
    simpa [prefixWord, tailWord_102473, baseEnd_102473] using wordTrace_append hprefix tailTrace_102473
  have hstable : (prefixWord ++ tailWord_102473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102473).length < 2 ^ (prefixWord ++ tailWord_102473).sum := by decide
  have hdescent : baseEnd_102473 < baseStart_102473 := by decide
  rcases family_descends (prefixWord ++ tailWord_102473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102486 : List Nat := [5, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_102486 : Nat := 118140960795 + 102486 * 2 ^ 59
def prefixEnd_102486 : Nat := 4983230072969 + 3 ^ 40 * 102486 * 2
def baseEnd_102486 : Nat := 46777402983814450447717

theorem tailTrace_102486 : CollatzResearch.WordTrace tailWord_102486 prefixEnd_102486 46777402983814450447717 := by
  unfold tailWord_102486
  simp only [CollatzResearch.WordTrace]
  refine ⟨233623219169887503775457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2491981004478800040271541 233623219169887503775457)
  ·
    refine ⟨175217414377415627831593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233623219169887503775457 175217414377415627831593)
    ·
      refine ⟨131413060783061720873695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175217414377415627831593 131413060783061720873695)
      ·
        refine ⟨197119591174592581310543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131413060783061720873695 197119591174592581310543)
        ·
          refine ⟨295679386761888871965815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197119591174592581310543 295679386761888871965815)
          ·
            refine ⟨443519080142833307948723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295679386761888871965815 443519080142833307948723)
            ·
              refine ⟨665278620214249961923085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443519080142833307948723 665278620214249961923085)
              ·
                refine ⟨249479482580343735721157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 665278620214249961923085 249479482580343735721157)
                ·
                  refine ⟨46777402983814450447717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 249479482580343735721157 46777402983814450447717)
                  ·
                    rfl

theorem cell20_102486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_102486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102486 prefixEnd_102486 := by exact prefixLift 102486
  have htrace : WordTrace (prefixWord ++ tailWord_102486) baseStart_102486 baseEnd_102486 := by
    simpa [prefixWord, tailWord_102486, baseEnd_102486] using wordTrace_append hprefix tailTrace_102486
  have hstable : (prefixWord ++ tailWord_102486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102486).length < 2 ^ (prefixWord ++ tailWord_102486).sum := by decide
  have hdescent : baseEnd_102486 < baseStart_102486 := by decide
  rcases family_descends (prefixWord ++ tailWord_102486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102490 : List Nat := [3, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_102490 : Nat := 118140960795 + 102490 * 2 ^ 59
def prefixEnd_102490 : Nat := 4983230072969 + 3 ^ 40 * 102490 * 2
def baseEnd_102490 : Nat := 46779228692808214314367

theorem tailTrace_102490 : CollatzResearch.WordTrace tailWord_102490 prefixEnd_102490 46779228692808214314367 := by
  unfold tailWord_102490
  simp only [CollatzResearch.WordTrace]
  refine ⟨934529349675927185888231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2492078265802472495701949 934529349675927185888231)
  ·
    refine ⟨1401794024513890778832347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 934529349675927185888231 1401794024513890778832347)
    ·
      refine ⟨2102691036770836168248521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1401794024513890778832347 2102691036770836168248521)
      ·
        refine ⟨1577018277578127126186391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2102691036770836168248521 1577018277578127126186391)
        ·
          refine ⟨2365527416367190689279587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1577018277578127126186391 2365527416367190689279587)
          ·
            refine ⟨3548291124550786033919381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2365527416367190689279587 3548291124550786033919381)
            ·
              refine ⟨166326146463318095339971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3548291124550786033919381 166326146463318095339971)
              ·
                refine ⟨249489219694977143009957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166326146463318095339971 249489219694977143009957)
                ·
                  refine ⟨46779228692808214314367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 249489219694977143009957 46779228692808214314367)
                  ·
                    rfl

theorem cell20_102490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_102490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102490 prefixEnd_102490 := by exact prefixLift 102490
  have htrace : WordTrace (prefixWord ++ tailWord_102490) baseStart_102490 baseEnd_102490 := by
    simpa [prefixWord, tailWord_102490, baseEnd_102490] using wordTrace_append hprefix tailTrace_102490
  have hstable : (prefixWord ++ tailWord_102490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102490).length < 2 ^ (prefixWord ++ tailWord_102490).sum := by decide
  have hdescent : baseEnd_102490 < baseStart_102490 := by decide
  rcases family_descends (prefixWord ++ tailWord_102490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102514 : List Nat := [3, 2, 1, 2, 2, 2, 4, 4]
def baseStart_102514 : Nat := 118140960795 + 102514 * 2 ^ 59
def prefixEnd_102514 : Nat := 4983230072969 + 3 ^ 40 * 102514 * 2
def baseEnd_102514 : Nat := 15596727648923599171423

theorem tailTrace_102514 : CollatzResearch.WordTrace tailWord_102514 prefixEnd_102514 15596727648923599171423 := by
  unfold tailWord_102514
  simp only [CollatzResearch.WordTrace]
  refine ⟨934748187654190210606649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2492661833744507228284397 934748187654190210606649)
  ·
    refine ⟨701061140740642657954987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 934748187654190210606649 701061140740642657954987)
    ·
      refine ⟨1051591711110963986932481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 701061140740642657954987 1051591711110963986932481)
      ·
        refine ⟨788693783333222990199361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1051591711110963986932481 788693783333222990199361)
        ·
          refine ⟨591520337499917242649521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 788693783333222990199361 591520337499917242649521)
          ·
            refine ⟨443640253124937931987141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 591520337499917242649521 443640253124937931987141)
            ·
              refine ⟨83182547460925862247589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 443640253124937931987141 83182547460925862247589)
              ·
                refine ⟨15596727648923599171423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83182547460925862247589 15596727648923599171423)
                ·
                  rfl

theorem cell20_102514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_102514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102514 prefixEnd_102514 := by exact prefixLift 102514
  have htrace : WordTrace (prefixWord ++ tailWord_102514) baseStart_102514 baseEnd_102514 := by
    simpa [prefixWord, tailWord_102514, baseEnd_102514] using wordTrace_append hprefix tailTrace_102514
  have hstable : (prefixWord ++ tailWord_102514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102514).length < 2 ^ (prefixWord ++ tailWord_102514).sum := by decide
  have hdescent : baseEnd_102514 < baseStart_102514 := by decide
  rcases family_descends (prefixWord ++ tailWord_102514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102524 : List Nat := [2, 2, 2, 1, 1, 6, 1, 3, 2]
def baseStart_102524 : Nat := 118140960795 + 102524 * 2 ^ 59
def prefixEnd_102524 : Nat := 4983230072969 + 3 ^ 40 * 102524 * 2
def baseEnd_102524 : Nat := 46794747219255207180895

theorem tailTrace_102524 : CollatzResearch.WordTrace tailWord_102524 prefixEnd_102524 46794747219255207180895 := by
  unfold tailWord_102524
  simp only [CollatzResearch.WordTrace]
  refine ⟨1869678740290266275145313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2492904987053688366860417 1869678740290266275145313)
  ·
    refine ⟨1402259055217699706358985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1869678740290266275145313 1402259055217699706358985)
    ·
      refine ⟨1051694291413274779769239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1402259055217699706358985 1051694291413274779769239)
      ·
        refine ⟨1577541437119912169653859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1051694291413274779769239 1577541437119912169653859)
        ·
          refine ⟨2366312155679868254480789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1577541437119912169653859 2366312155679868254480789)
          ·
            refine ⟨110920882297493824428787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2366312155679868254480789 110920882297493824428787)
            ·
              refine ⟨166381323446240736643181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110920882297493824428787 166381323446240736643181)
              ·
                refine ⟨62392996292340276241193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166381323446240736643181 62392996292340276241193)
                ·
                  refine ⟨46794747219255207180895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62392996292340276241193 46794747219255207180895)
                  ·
                    rfl

theorem cell20_102524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_102524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102524 prefixEnd_102524 := by exact prefixLift 102524
  have htrace : WordTrace (prefixWord ++ tailWord_102524) baseStart_102524 baseEnd_102524 := by
    simpa [prefixWord, tailWord_102524, baseEnd_102524] using wordTrace_append hprefix tailTrace_102524
  have hstable : (prefixWord ++ tailWord_102524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102524).length < 2 ^ (prefixWord ++ tailWord_102524).sum := by decide
  have hdescent : baseEnd_102524 < baseStart_102524 := by decide
  rcases family_descends (prefixWord ++ tailWord_102524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102552 : List Nat := [2, 1, 2, 4, 3, 1, 2, 5]
def baseStart_102552 : Nat := 118140960795 + 102552 * 2 ^ 59
def prefixEnd_102552 : Nat := 4983230072969 + 3 ^ 40 * 102552 * 2
def baseEnd_102552 : Nat := 15602509060737184749149

theorem tailTrace_102552 : CollatzResearch.WordTrace tailWord_102552 prefixEnd_102552 15602509060737184749149 := by
  unfold tailWord_102552
  simp only [CollatzResearch.WordTrace]
  refine ⟨1870189362239546666154955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2493585816319395554873273 1870189362239546666154955)
  ·
    refine ⟨2805284043359319999232433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1870189362239546666154955 2805284043359319999232433)
    ·
      refine ⟨2103963032519489999424325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2805284043359319999232433 2103963032519489999424325)
      ·
        refine ⟨394493068597404374892061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2103963032519489999424325 394493068597404374892061)
        ·
          refine ⟨147934900724026640584523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394493068597404374892061 147934900724026640584523)
          ·
            refine ⟨221902351086039960876785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147934900724026640584523 221902351086039960876785)
            ·
              refine ⟨166426763314529970657589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221902351086039960876785 166426763314529970657589)
              ·
                refine ⟨15602509060737184749149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166426763314529970657589 15602509060737184749149)
                ·
                  rfl

theorem cell20_102552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_102552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102552 prefixEnd_102552 := by exact prefixLift 102552
  have htrace : WordTrace (prefixWord ++ tailWord_102552) baseStart_102552 baseEnd_102552 := by
    simpa [prefixWord, tailWord_102552, baseEnd_102552] using wordTrace_append hprefix tailTrace_102552
  have hstable : (prefixWord ++ tailWord_102552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102552).length < 2 ^ (prefixWord ++ tailWord_102552).sum := by decide
  have hdescent : baseEnd_102552 < baseStart_102552 := by decide
  rcases family_descends (prefixWord ++ tailWord_102552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102590 : List Nat := [4, 2, 1, 1, 5, 7]
def baseStart_102590 : Nat := 118140960795 + 102590 * 2 ^ 59
def prefixEnd_102590 : Nat := 4983230072969 + 3 ^ 40 * 102590 * 2
def baseEnd_102590 : Nat := 1734254496950085591875

theorem tailTrace_102590 : CollatzResearch.WordTrace tailWord_102590 prefixEnd_102590 1734254496950085591875 := by
  unfold tailWord_102590
  simp only [CollatzResearch.WordTrace]
  refine ⟨467720587292678227774153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2494509798894283881462149 467720587292678227774153)
  ·
    refine ⟨350790440469508670830615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 467720587292678227774153 350790440469508670830615)
    ·
      refine ⟨526185660704263006245923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350790440469508670830615 526185660704263006245923)
      ·
        refine ⟨789278491056394509368885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526185660704263006245923 789278491056394509368885)
        ·
          refine ⟨73994858536536985253333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 789278491056394509368885 73994858536536985253333)
          ·
            refine ⟨1734254496950085591875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 73994858536536985253333 1734254496950085591875)
            ·
              rfl

theorem cell20_102590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 7].length) (baseStart_102590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102590 prefixEnd_102590 := by exact prefixLift 102590
  have htrace : WordTrace (prefixWord ++ tailWord_102590) baseStart_102590 baseEnd_102590 := by
    simpa [prefixWord, tailWord_102590, baseEnd_102590] using wordTrace_append hprefix tailTrace_102590
  have hstable : (prefixWord ++ tailWord_102590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102590).length < 2 ^ (prefixWord ++ tailWord_102590).sum := by decide
  have hdescent : baseEnd_102590 < baseStart_102590 := by decide
  rcases family_descends (prefixWord ++ tailWord_102590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102593 : List Nat := [1, 2, 6, 1, 2, 1, 2, 2, 3]
def baseStart_102593 : Nat := 118140960795 + 102593 * 2 ^ 59
def prefixEnd_102593 : Nat := 4983230072969 + 3 ^ 40 * 102593 * 2
def baseEnd_102593 : Nat := 46826240699397633880613

theorem tailTrace_102593 : CollatzResearch.WordTrace tailWord_102593 prefixEnd_102593 46826240699397633880613 := by
  unfold tailWord_102593
  simp only [CollatzResearch.WordTrace]
  refine ⟨3741874117330557334552433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2494582744887038223034955 3741874117330557334552433)
  ·
    refine ⟨2806405587997918000914325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3741874117330557334552433 2806405587997918000914325)
    ·
      refine ⟨131550261937402406292859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2806405587997918000914325 131550261937402406292859)
      ·
        refine ⟨197325392906103609439289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131550261937402406292859 197325392906103609439289)
        ·
          refine ⟨147994044679577707079467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197325392906103609439289 147994044679577707079467)
          ·
            refine ⟨221991067019366560619201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147994044679577707079467 221991067019366560619201)
            ·
              refine ⟨166493300264524920464401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221991067019366560619201 166493300264524920464401)
              ·
                refine ⟨124869975198393690348301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166493300264524920464401 124869975198393690348301)
                ·
                  refine ⟨46826240699397633880613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124869975198393690348301 46826240699397633880613)
                  ·
                    rfl

theorem cell20_102593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_102593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102593 prefixEnd_102593 := by exact prefixLift 102593
  have htrace : WordTrace (prefixWord ++ tailWord_102593) baseStart_102593 baseEnd_102593 := by
    simpa [prefixWord, tailWord_102593, baseEnd_102593] using wordTrace_append hprefix tailTrace_102593
  have hstable : (prefixWord ++ tailWord_102593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102593).length < 2 ^ (prefixWord ++ tailWord_102593).sum := by decide
  have hdescent : baseEnd_102593 < baseStart_102593 := by decide
  rcases family_descends (prefixWord ++ tailWord_102593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102621 : List Nat := [1, 4, 3, 2, 1, 2, 1, 2, 4]
def baseStart_102621 : Nat := 118140960795 + 102621 * 2 ^ 59
def prefixEnd_102621 : Nat := 4983230072969 + 3 ^ 40 * 102621 * 2
def baseEnd_102621 : Nat := 46839020662353980947165

theorem tailTrace_102621 : CollatzResearch.WordTrace tailWord_102621 prefixEnd_102621 46839020662353980947165 := by
  unfold tailWord_102621
  simp only [CollatzResearch.WordTrace]
  refine ⟨3742895361229118116571717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2495263574152745411047811 3742895361229118116571717)
  ·
    refine ⟨701792880230459646857197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3742895361229118116571717 701792880230459646857197)
    ·
      refine ⟨263172330086422367571449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 701792880230459646857197 263172330086422367571449)
      ·
        refine ⟨197379247564816775678587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263172330086422367571449 197379247564816775678587)
        ·
          refine ⟨296068871347225163517881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197379247564816775678587 296068871347225163517881)
          ·
            refine ⟨222051653510418872638411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296068871347225163517881 222051653510418872638411)
            ·
              refine ⟨333077480265628308957617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222051653510418872638411 333077480265628308957617)
              ·
                refine ⟨249808110199221231718213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333077480265628308957617 249808110199221231718213)
                ·
                  refine ⟨46839020662353980947165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 249808110199221231718213 46839020662353980947165)
                  ·
                    rfl

theorem cell20_102621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_102621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102621 prefixEnd_102621 := by exact prefixLift 102621
  have htrace : WordTrace (prefixWord ++ tailWord_102621) baseStart_102621 baseEnd_102621 := by
    simpa [prefixWord, tailWord_102621, baseEnd_102621] using wordTrace_append hprefix tailTrace_102621
  have hstable : (prefixWord ++ tailWord_102621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102621).length < 2 ^ (prefixWord ++ tailWord_102621).sum := by decide
  have hdescent : baseEnd_102621 < baseStart_102621 := by decide
  rcases family_descends (prefixWord ++ tailWord_102621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102652 : List Nat := [2, 2, 2, 1, 4, 3, 1, 2, 3]
def baseStart_102652 : Nat := 118140960795 + 102652 * 2 ^ 59
def prefixEnd_102652 : Nat := 4983230072969 + 3 ^ 40 * 102652 * 2
def baseEnd_102652 : Nat := 46853169907055650913705

theorem tailTrace_102652 : CollatzResearch.WordTrace tailWord_102652 prefixEnd_102652 46853169907055650913705 := by
  unfold tailWord_102652
  simp only [CollatzResearch.WordTrace]
  refine ⟨1872013012058405205475105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2496017349411206940633473 1872013012058405205475105)
  ·
    refine ⟨1404009759043803904106329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1872013012058405205475105 1404009759043803904106329)
    ·
      refine ⟨1053007319282852928079747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1404009759043803904106329 1053007319282852928079747)
      ·
        refine ⟨1579510978924279392119621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1053007319282852928079747 1579510978924279392119621)
        ·
          refine ⟨296158308548302386022429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1579510978924279392119621 296158308548302386022429)
          ·
            refine ⟨111059365705613394758411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296158308548302386022429 111059365705613394758411)
            ·
              refine ⟨166589048558420092137617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111059365705613394758411 166589048558420092137617)
              ·
                refine ⟨124941786418815069103213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166589048558420092137617 124941786418815069103213)
                ·
                  refine ⟨46853169907055650913705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124941786418815069103213 46853169907055650913705)
                  ·
                    rfl

theorem cell20_102652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_102652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102652 prefixEnd_102652 := by exact prefixLift 102652
  have htrace : WordTrace (prefixWord ++ tailWord_102652) baseStart_102652 baseEnd_102652 := by
    simpa [prefixWord, tailWord_102652, baseEnd_102652] using wordTrace_append hprefix tailTrace_102652
  have hstable : (prefixWord ++ tailWord_102652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102652).length < 2 ^ (prefixWord ++ tailWord_102652).sum := by decide
  have hdescent : baseEnd_102652 < baseStart_102652 := by decide
  rcases family_descends (prefixWord ++ tailWord_102652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102687 : List Nat := [1, 1, 2, 4, 3, 2, 1, 6]
def baseStart_102687 : Nat := 118140960795 + 102687 * 2 ^ 59
def prefixEnd_102687 : Nat := 4983230072969 + 3 ^ 40 * 102687 * 2
def baseEnd_102687 : Nat := 15623048286917028248965

theorem tailTrace_102687 : CollatzResearch.WordTrace tailWord_102687 prefixEnd_102687 15623048286917028248965 := by
  unfold tailWord_102687
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745302578990011388474315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2496868385993340925649543 3745302578990011388474315)
  ·
    refine ⟨5617953868485017082711473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3745302578990011388474315 5617953868485017082711473)
    ·
      refine ⟨4213465401363762812033605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5617953868485017082711473 4213465401363762812033605)
      ·
        refine ⟨790024762755705527256301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4213465401363762812033605 790024762755705527256301)
        ·
          refine ⟨296259286033389572721113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 790024762755705527256301 296259286033389572721113)
          ·
            refine ⟨222194464525042179540835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296259286033389572721113 222194464525042179540835)
            ·
              refine ⟨333291696787563269311253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222194464525042179540835 333291696787563269311253)
              ·
                refine ⟨15623048286917028248965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 333291696787563269311253 15623048286917028248965)
                ·
                  rfl

theorem cell20_102687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 6].length) (baseStart_102687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102687 prefixEnd_102687 := by exact prefixLift 102687
  have htrace : WordTrace (prefixWord ++ tailWord_102687) baseStart_102687 baseEnd_102687 := by
    simpa [prefixWord, tailWord_102687, baseEnd_102687] using wordTrace_append hprefix tailTrace_102687
  have hstable : (prefixWord ++ tailWord_102687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102687).length < 2 ^ (prefixWord ++ tailWord_102687).sum := by decide
  have hdescent : baseEnd_102687 < baseStart_102687 := by decide
  rcases family_descends (prefixWord ++ tailWord_102687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102693 : List Nat := [1, 3, 1, 2, 6, 1, 1, 3, 2]
def baseStart_102693 : Nat := 118140960795 + 102693 * 2 ^ 59
def prefixEnd_102693 : Nat := 4983230072969 + 3 ^ 40 * 102693 * 2
def baseEnd_102693 : Nat := 46871883424241730546871

theorem tailTrace_102693 : CollatzResearch.WordTrace tailWord_102693 prefixEnd_102693 46871883424241730546871 := by
  unfold tailWord_102693
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745521416968274413192733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2497014277978849608795155 3745521416968274413192733)
  ·
    refine ⟨1404570531363102904947275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3745521416968274413192733 1404570531363102904947275)
    ·
      refine ⟨2106855797044654357420913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1404570531363102904947275 2106855797044654357420913)
      ·
        refine ⟨1580141847783490768065685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2106855797044654357420913 1580141847783490768065685)
        ·
          refine ⟨74069149114851129753079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1580141847783490768065685 74069149114851129753079)
          ·
            refine ⟨111103723672276694629619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74069149114851129753079 111103723672276694629619)
            ·
              refine ⟨166655585508415041944429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111103723672276694629619 166655585508415041944429)
              ·
                refine ⟨62495844565655640729161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166655585508415041944429 62495844565655640729161)
                ·
                  refine ⟨46871883424241730546871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62495844565655640729161 46871883424241730546871)
                  ·
                    rfl

theorem cell20_102693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_102693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102693 prefixEnd_102693 := by exact prefixLift 102693
  have htrace : WordTrace (prefixWord ++ tailWord_102693) baseStart_102693 baseEnd_102693 := by
    simpa [prefixWord, tailWord_102693, baseEnd_102693] using wordTrace_append hprefix tailTrace_102693
  have hstable : (prefixWord ++ tailWord_102693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102693).length < 2 ^ (prefixWord ++ tailWord_102693).sum := by decide
  have hdescent : baseEnd_102693 < baseStart_102693 := by decide
  rcases family_descends (prefixWord ++ tailWord_102693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102714 : List Nat := [3, 1, 1, 1, 4, 3, 3, 2, 2]
def baseStart_102714 : Nat := 118140960795 + 102714 * 2 ^ 59
def prefixEnd_102714 : Nat := 4983230072969 + 3 ^ 40 * 102714 * 2
def baseEnd_102714 : Nat := 46881468396458990846785

theorem tailTrace_102714 : CollatzResearch.WordTrace tailWord_102714 prefixEnd_102714 46881468396458990846785 := by
  unfold tailWord_102714
  simp only [CollatzResearch.WordTrace]
  refine ⟨936571837473048749926799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2497524899928129999804797 936571837473048749926799)
  ·
    refine ⟨1404857756209573124890199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 936571837473048749926799 1404857756209573124890199)
    ·
      refine ⟨2107286634314359687335299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1404857756209573124890199 2107286634314359687335299)
      ·
        refine ⟨3160929951471539531002949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2107286634314359687335299 3160929951471539531002949)
        ·
          refine ⟨592674365900913662063053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3160929951471539531002949 592674365900913662063053)
          ·
            refine ⟨222252887212842623273645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 592674365900913662063053 222252887212842623273645)
            ·
              refine ⟨83344832704815983727617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222252887212842623273645 83344832704815983727617)
              ·
                refine ⟨62508624528611987795713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83344832704815983727617 62508624528611987795713)
                ·
                  refine ⟨46881468396458990846785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62508624528611987795713 46881468396458990846785)
                  ·
                    rfl

theorem cell20_102714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_102714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102714 prefixEnd_102714 := by exact prefixLift 102714
  have htrace : WordTrace (prefixWord ++ tailWord_102714) baseStart_102714 baseEnd_102714 := by
    simpa [prefixWord, tailWord_102714, baseEnd_102714] using wordTrace_append hprefix tailTrace_102714
  have hstable : (prefixWord ++ tailWord_102714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102714).length < 2 ^ (prefixWord ++ tailWord_102714).sum := by decide
  have hdescent : baseEnd_102714 < baseStart_102714 := by decide
  rcases family_descends (prefixWord ++ tailWord_102714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102724 : List Nat := [2, 3, 4, 1, 2, 2, 2, 1, 3]
def baseStart_102724 : Nat := 118140960795 + 102724 * 2 ^ 59
def prefixEnd_102724 : Nat := 4983230072969 + 3 ^ 40 * 102724 * 2
def baseEnd_102724 : Nat := 46886032668943400513411

theorem tailTrace_102724 : CollatzResearch.WordTrace tailWord_102724 prefixEnd_102724 46886032668943400513411 := by
  unfold tailWord_102724
  simp only [CollatzResearch.WordTrace]
  refine ⟨1873326039927983353785613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2497768053237311138380817 1873326039927983353785613)
  ·
    refine ⟨702497264972993757669605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1873326039927983353785613 702497264972993757669605)
    ·
      refine ⟨131718237182436329563051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 702497264972993757669605 131718237182436329563051)
      ·
        refine ⟨197577355773654494344577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131718237182436329563051 197577355773654494344577)
        ·
          refine ⟨148183016830240870758433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197577355773654494344577 148183016830240870758433)
          ·
            refine ⟨111137262622680653068825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148183016830240870758433 111137262622680653068825)
            ·
              refine ⟨83352946967010489801619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111137262622680653068825 83352946967010489801619)
              ·
                refine ⟨125029420450515734702429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83352946967010489801619 125029420450515734702429)
                ·
                  refine ⟨46886032668943400513411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125029420450515734702429 46886032668943400513411)
                  ·
                    rfl

theorem cell20_102724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_102724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102724 prefixEnd_102724 := by exact prefixLift 102724
  have htrace : WordTrace (prefixWord ++ tailWord_102724) baseStart_102724 baseEnd_102724 := by
    simpa [prefixWord, tailWord_102724, baseEnd_102724] using wordTrace_append hprefix tailTrace_102724
  have hstable : (prefixWord ++ tailWord_102724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102724).length < 2 ^ (prefixWord ++ tailWord_102724).sum := by decide
  have hdescent : baseEnd_102724 < baseStart_102724 := by decide
  rcases family_descends (prefixWord ++ tailWord_102724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102777 : List Nat := [1, 2, 1, 3, 2, 1, 1, 5, 4]
def baseStart_102777 : Nat := 118140960795 + 102777 * 2 ^ 59
def prefixEnd_102777 : Nat := 4983230072969 + 3 ^ 40 * 102777 * 2
def baseEnd_102777 : Nat := 46910223313110771746527

theorem tailTrace_102777 : CollatzResearch.WordTrace tailWord_102777 prefixEnd_102777 46910223313110771746527 := by
  unfold tailWord_102777
  simp only [CollatzResearch.WordTrace]
  refine ⟨3748585148663956759250585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2499056765775971172833723 3748585148663956759250585)
  ·
    refine ⟨2811438861497967569437939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3748585148663956759250585 2811438861497967569437939)
    ·
      refine ⟨4217158292246951354156909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2811438861497967569437939 4217158292246951354156909)
      ·
        refine ⟨1581434359592606757808841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4217158292246951354156909 1581434359592606757808841)
        ·
          refine ⟨1186075769694455068356631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1581434359592606757808841 1186075769694455068356631)
          ·
            refine ⟨1779113654541682602534947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186075769694455068356631 1779113654541682602534947)
            ·
              refine ⟨2668670481812523903802421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1779113654541682602534947 2668670481812523903802421)
              ·
                refine ⟨250187857669924115981477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2668670481812523903802421 250187857669924115981477)
                ·
                  refine ⟨46910223313110771746527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 250187857669924115981477 46910223313110771746527)
                  ·
                    rfl

theorem cell20_102777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_102777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102777 prefixEnd_102777 := by exact prefixLift 102777
  have htrace : WordTrace (prefixWord ++ tailWord_102777) baseStart_102777 baseEnd_102777 := by
    simpa [prefixWord, tailWord_102777, baseEnd_102777] using wordTrace_append hprefix tailTrace_102777
  have hstable : (prefixWord ++ tailWord_102777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102777).length < 2 ^ (prefixWord ++ tailWord_102777).sum := by decide
  have hdescent : baseEnd_102777 < baseStart_102777 := by decide
  rcases family_descends (prefixWord ++ tailWord_102777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102815 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 6]
def baseStart_102815 : Nat := 118140960795 + 102815 * 2 ^ 59
def prefixEnd_102815 : Nat := 4983230072969 + 3 ^ 40 * 102815 * 2
def baseEnd_102815 : Nat := 46927567548551528479705

theorem tailTrace_102815 : CollatzResearch.WordTrace tailWord_102815 prefixEnd_102815 46927567548551528479705 := by
  unfold tailWord_102815
  simp only [CollatzResearch.WordTrace]
  refine ⟨3749971122526289249133899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2499980748350859499422599 3749971122526289249133899)
  ·
    refine ⟨5624956683789433873700849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3749971122526289249133899 5624956683789433873700849)
    ·
      refine ⟨4218717512842075405275637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5624956683789433873700849 4218717512842075405275637)
      ·
        refine ⟨395504766828944569244591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4218717512842075405275637 395504766828944569244591)
        ·
          refine ⟨593257150243416853866887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395504766828944569244591 593257150243416853866887)
          ·
            refine ⟨889885725365125280800331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593257150243416853866887 889885725365125280800331)
            ·
              refine ⟨1334828588047687921200497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889885725365125280800331 1334828588047687921200497)
              ·
                refine ⟨1001121441035765940900373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1334828588047687921200497 1001121441035765940900373)
                ·
                  refine ⟨46927567548551528479705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1001121441035765940900373 46927567548551528479705)
                  ·
                    rfl

theorem cell20_102815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_102815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102815 prefixEnd_102815 := by exact prefixLift 102815
  have htrace : WordTrace (prefixWord ++ tailWord_102815) baseStart_102815 baseEnd_102815 := by
    simpa [prefixWord, tailWord_102815, baseEnd_102815] using wordTrace_append hprefix tailTrace_102815
  have hstable : (prefixWord ++ tailWord_102815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102815).length < 2 ^ (prefixWord ++ tailWord_102815).sum := by decide
  have hdescent : baseEnd_102815 < baseStart_102815 := by decide
  rcases family_descends (prefixWord ++ tailWord_102815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102852 : List Nat := [2, 3, 3, 2, 3, 1, 2, 4]
def baseStart_102852 : Nat := 118140960795 + 102852 * 2 ^ 59
def prefixEnd_102852 : Nat := 4983230072969 + 3 ^ 40 * 102852 * 2
def baseEnd_102852 : Nat := 15648151785581281415407

theorem tailTrace_102852 : CollatzResearch.WordTrace tailWord_102852 prefixEnd_102852 15648151785581281415407 := by
  unfold tailWord_102852
  simp only [CollatzResearch.WordTrace]
  refine ⟨1875660311696122284115405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2500880415594829712153873 1875660311696122284115405)
  ·
    refine ⟨703372616886045856543277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1875660311696122284115405 703372616886045856543277)
    ·
      refine ⟨263764731332267196203729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 703372616886045856543277 263764731332267196203729)
      ·
        refine ⟨197823548499200397152797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263764731332267196203729 197823548499200397152797)
        ·
          refine ⟨74183830687200148932299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197823548499200397152797 74183830687200148932299)
          ·
            refine ⟨111275746030800223398449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74183830687200148932299 111275746030800223398449)
            ·
              refine ⟨83456809523100167548837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111275746030800223398449 83456809523100167548837)
              ·
                refine ⟨15648151785581281415407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83456809523100167548837 15648151785581281415407)
                ·
                  rfl

theorem cell20_102852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 4].length) (baseStart_102852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102852 prefixEnd_102852 := by exact prefixLift 102852
  have htrace : WordTrace (prefixWord ++ tailWord_102852) baseStart_102852 baseEnd_102852 := by
    simpa [prefixWord, tailWord_102852, baseEnd_102852] using wordTrace_append hprefix tailTrace_102852
  have hstable : (prefixWord ++ tailWord_102852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102852).length < 2 ^ (prefixWord ++ tailWord_102852).sum := by decide
  have hdescent : baseEnd_102852 < baseStart_102852 := by decide
  rcases family_descends (prefixWord ++ tailWord_102852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102856 : List Nat := [2, 1, 3, 1, 3, 4, 2, 4]
def baseStart_102856 : Nat := 118140960795 + 102856 * 2 ^ 59
def prefixEnd_102856 : Nat := 4983230072969 + 3 ^ 40 * 102856 * 2
def baseEnd_102856 : Nat := 15648760355245869370957

theorem tailTrace_102856 : CollatzResearch.WordTrace tailWord_102856 prefixEnd_102856 15648760355245869370957 := by
  unfold tailWord_102856
  simp only [CollatzResearch.WordTrace]
  refine ⟨1875733257688876625688211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2500977676918502167584281 1875733257688876625688211)
  ·
    refine ⟨2813599886533314938532317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1875733257688876625688211 2813599886533314938532317)
    ·
      refine ⟨1055099957449993101949619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2813599886533314938532317 1055099957449993101949619)
      ·
        refine ⟨1582649936174989652924429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055099957449993101949619 1582649936174989652924429)
        ·
          refine ⟨593493726065621119846661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1582649936174989652924429 593493726065621119846661)
          ·
            refine ⟨111280073637303959971249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 593493726065621119846661 111280073637303959971249)
            ·
              refine ⟨83460055227977969978437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111280073637303959971249 83460055227977969978437)
              ·
                refine ⟨15648760355245869370957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83460055227977969978437 15648760355245869370957)
                ·
                  rfl

theorem cell20_102856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_102856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102856 prefixEnd_102856 := by exact prefixLift 102856
  have htrace : WordTrace (prefixWord ++ tailWord_102856) baseStart_102856 baseEnd_102856 := by
    simpa [prefixWord, tailWord_102856, baseEnd_102856] using wordTrace_append hprefix tailTrace_102856
  have hstable : (prefixWord ++ tailWord_102856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102856).length < 2 ^ (prefixWord ++ tailWord_102856).sum := by decide
  have hdescent : baseEnd_102856 < baseStart_102856 := by decide
  rcases family_descends (prefixWord ++ tailWord_102856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102936 : List Nat := [2, 1, 2, 3, 3, 9]
def baseStart_102936 : Nat := 118140960795 + 102936 * 2 ^ 59
def prefixEnd_102936 : Nat := 4983230072969 + 3 ^ 40 * 102936 * 2
def baseEnd_102936 : Nat := 1740103527615292053551

theorem tailTrace_102936 : CollatzResearch.WordTrace tailWord_102936 prefixEnd_102936 1740103527615292053551 := by
  unfold tailWord_102936
  simp only [CollatzResearch.WordTrace]
  refine ⟨1877192177543963457144331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2502922903391951276192441 1877192177543963457144331)
  ·
    refine ⟨2815788266315945185716497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1877192177543963457144331 2815788266315945185716497)
    ·
      refine ⟨2111841199736958889287373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2815788266315945185716497 2111841199736958889287373)
      ·
        refine ⟨791940449901359583482765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2111841199736958889287373 791940449901359583482765)
        ·
          refine ⟨296977668713009843806037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 791940449901359583482765 296977668713009843806037)
          ·
            refine ⟨1740103527615292053551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 296977668713009843806037 1740103527615292053551)
            ·
              rfl

theorem cell20_102936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 9].length) (baseStart_102936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102936 prefixEnd_102936 := by exact prefixLift 102936
  have htrace : WordTrace (prefixWord ++ tailWord_102936) baseStart_102936 baseEnd_102936 := by
    simpa [prefixWord, tailWord_102936, baseEnd_102936] using wordTrace_append hprefix tailTrace_102936
  have hstable : (prefixWord ++ tailWord_102936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102936).length < 2 ^ (prefixWord ++ tailWord_102936).sum := by decide
  have hdescent : baseEnd_102936 < baseStart_102936 := by decide
  rcases family_descends (prefixWord ++ tailWord_102936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102960 : List Nat := [2, 1, 1, 1, 2, 3, 4, 3, 3]
def baseStart_102960 : Nat := 118140960795 + 102960 * 2 ^ 59
def prefixEnd_102960 : Nat := 4983230072969 + 3 ^ 40 * 102960 * 2
def baseEnd_102960 : Nat := 46993749499575468645779

theorem tailTrace_102960 : CollatzResearch.WordTrace tailWord_102960 prefixEnd_102960 46993749499575468645779 := by
  unfold tailWord_102960
  simp only [CollatzResearch.WordTrace]
  refine ⟨1877629853500489506581167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2503506471333986008774889 1877629853500489506581167)
  ·
    refine ⟨2816444780250734259871751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1877629853500489506581167 2816444780250734259871751)
    ·
      refine ⟨4224667170376101389807627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2816444780250734259871751 4224667170376101389807627)
      ·
        refine ⟨6337000755564152084711441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4224667170376101389807627 6337000755564152084711441)
        ·
          refine ⟨4752750566673114063533581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6337000755564152084711441 4752750566673114063533581)
          ·
            refine ⟨1782281462502417773825093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4752750566673114063533581 1782281462502417773825093)
            ·
              refine ⟨334177774219203332592205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1782281462502417773825093 334177774219203332592205)
              ·
                refine ⟨125316665332201249722077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334177774219203332592205 125316665332201249722077)
                ·
                  refine ⟨46993749499575468645779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125316665332201249722077 46993749499575468645779)
                  ·
                    rfl

theorem cell20_102960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_102960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102960 prefixEnd_102960 := by exact prefixLift 102960
  have htrace : WordTrace (prefixWord ++ tailWord_102960) baseStart_102960 baseEnd_102960 := by
    simpa [prefixWord, tailWord_102960, baseEnd_102960] using wordTrace_append hprefix tailTrace_102960
  have hstable : (prefixWord ++ tailWord_102960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102960).length < 2 ^ (prefixWord ++ tailWord_102960).sum := by decide
  have hdescent : baseEnd_102960 < baseStart_102960 := by decide
  rcases family_descends (prefixWord ++ tailWord_102960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102967 : List Nat := [1, 1, 3, 1, 2, 3, 3, 2, 4]
def baseStart_102967 : Nat := 118140960795 + 102967 * 2 ^ 59
def prefixEnd_102967 : Nat := 4983230072969 + 3 ^ 40 * 102967 * 2
def baseEnd_102967 : Nat := 46996944490314555412417

theorem tailTrace_102967 : CollatzResearch.WordTrace tailWord_102967 prefixEnd_102967 46996944490314555412417 := by
  unfold tailWord_102967
  simp only [CollatzResearch.WordTrace]
  refine ⟨3755515017975619208667155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2503676678650412805778103 3755515017975619208667155)
  ·
    refine ⟨5633272526963428813000733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3755515017975619208667155 5633272526963428813000733)
    ·
      refine ⟨2112477197611285804875275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5633272526963428813000733 2112477197611285804875275)
      ·
        refine ⟨3168715796416928707312913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2112477197611285804875275 3168715796416928707312913)
        ·
          refine ⟨2376536847312696530484685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3168715796416928707312913 2376536847312696530484685)
          ·
            refine ⟨891201317742261198931757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2376536847312696530484685 891201317742261198931757)
            ·
              refine ⟨334200494153347949599409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 891201317742261198931757 334200494153347949599409)
              ·
                refine ⟨250650370615010962199557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334200494153347949599409 250650370615010962199557)
                ·
                  refine ⟨46996944490314555412417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 250650370615010962199557 46996944490314555412417)
                  ·
                    rfl

theorem cell20_102967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_102967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_102967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_102967 prefixEnd_102967 := by exact prefixLift 102967
  have htrace : WordTrace (prefixWord ++ tailWord_102967) baseStart_102967 baseEnd_102967 := by
    simpa [prefixWord, tailWord_102967, baseEnd_102967] using wordTrace_append hprefix tailTrace_102967
  have hstable : (prefixWord ++ tailWord_102967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102967).length < 2 ^ (prefixWord ++ tailWord_102967).sum := by decide
  have hdescent : baseEnd_102967 < baseStart_102967 := by decide
  rcases family_descends (prefixWord ++ tailWord_102967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103012 : List Nat := [2, 3, 1, 1, 2, 2, 2, 7]
def baseStart_103012 : Nat := 118140960795 + 103012 * 2 ^ 59
def prefixEnd_103012 : Nat := 4983230072969 + 3 ^ 40 * 103012 * 2
def baseEnd_103012 : Nat := 15672494572164799637411

theorem tailTrace_103012 : CollatzResearch.WordTrace tailWord_103012 prefixEnd_103012 15672494572164799637411 := by
  unfold tailWord_103012
  simp only [CollatzResearch.WordTrace]
  refine ⟨1878578151406295947027645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2504770868541727929370193 1878578151406295947027645)
  ·
    refine ⟨704466806777360980135367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1878578151406295947027645 704466806777360980135367)
    ·
      refine ⟨1056700210166041470203051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 704466806777360980135367 1056700210166041470203051)
      ·
        refine ⟨1585050315249062205304577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1056700210166041470203051 1585050315249062205304577)
        ·
          refine ⟨1188787736436796653978433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1585050315249062205304577 1188787736436796653978433)
          ·
            refine ⟨891590802327597490483825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1188787736436796653978433 891590802327597490483825)
            ·
              refine ⟨668693101745698117862869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891590802327597490483825 668693101745698117862869)
              ·
                refine ⟨15672494572164799637411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 668693101745698117862869 15672494572164799637411)
                ·
                  rfl

theorem cell20_103012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_103012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103012 prefixEnd_103012 := by exact prefixLift 103012
  have htrace : WordTrace (prefixWord ++ tailWord_103012) baseStart_103012 baseEnd_103012 := by
    simpa [prefixWord, tailWord_103012, baseEnd_103012] using wordTrace_append hprefix tailTrace_103012
  have hstable : (prefixWord ++ tailWord_103012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103012).length < 2 ^ (prefixWord ++ tailWord_103012).sum := by decide
  have hdescent : baseEnd_103012 < baseStart_103012 := by decide
  rcases family_descends (prefixWord ++ tailWord_103012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103022 : List Nat := [4, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_103022 : Nat := 118140960795 + 103022 * 2 ^ 59
def prefixEnd_103022 : Nat := 4983230072969 + 3 ^ 40 * 103022 * 2
def baseEnd_103022 : Nat := 47022047988978808578859

theorem tailTrace_103022 : CollatzResearch.WordTrace tailWord_103022 prefixEnd_103022 47022047988978808578859 := by
  unfold tailWord_103022
  simp only [CollatzResearch.WordTrace]
  refine ⟨469690129097045450239915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2505014021850909067946213 469690129097045450239915)
  ·
    refine ⟨704535193645568175359873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 469690129097045450239915 704535193645568175359873)
    ·
      refine ⟨528401395234176131519905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 704535193645568175359873 528401395234176131519905)
      ·
        refine ⟨396301046425632098639929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528401395234176131519905 396301046425632098639929)
        ·
          refine ⟨297225784819224073979947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396301046425632098639929 297225784819224073979947)
          ·
            refine ⟨445838677228836110969921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297225784819224073979947 445838677228836110969921)
            ·
              refine ⟨334379007921627083227441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445838677228836110969921 334379007921627083227441)
              ·
                refine ⟨250784255941220312420581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334379007921627083227441 250784255941220312420581)
                ·
                  refine ⟨47022047988978808578859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 250784255941220312420581 47022047988978808578859)
                  ·
                    rfl

theorem cell20_103022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_103022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103022 prefixEnd_103022 := by exact prefixLift 103022
  have htrace : WordTrace (prefixWord ++ tailWord_103022) baseStart_103022 baseEnd_103022 := by
    simpa [prefixWord, tailWord_103022, baseEnd_103022] using wordTrace_append hprefix tailTrace_103022
  have hstable : (prefixWord ++ tailWord_103022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103022).length < 2 ^ (prefixWord ++ tailWord_103022).sum := by decide
  have hdescent : baseEnd_103022 < baseStart_103022 := by decide
  rcases family_descends (prefixWord ++ tailWord_103022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103042 : List Nat := [3, 4, 3, 1, 1, 2, 6]
def baseStart_103042 : Nat := 118140960795 + 103042 * 2 ^ 59
def prefixEnd_103042 : Nat := 4983230072969 + 3 ^ 40 * 103042 * 2
def baseEnd_103042 : Nat := 5225686281549736434679

theorem tailTrace_103042 : CollatzResearch.WordTrace tailWord_103042 prefixEnd_103042 5225686281549736434679 := by
  unfold tailWord_103042
  simp only [CollatzResearch.WordTrace]
  refine ⟨939562623175976754411845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2505500328469271345098253 939562623175976754411845)
  ·
    refine ⟨176167991845495641452221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 939562623175976754411845 176167991845495641452221)
    ·
      refine ⟨66062996942060865544583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176167991845495641452221 66062996942060865544583)
      ·
        refine ⟨99094495413091298316875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66062996942060865544583 99094495413091298316875)
        ·
          refine ⟨148641743119636947475313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99094495413091298316875 148641743119636947475313)
          ·
            refine ⟨111481307339727710606485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148641743119636947475313 111481307339727710606485)
            ·
              refine ⟨5225686281549736434679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111481307339727710606485 5225686281549736434679)
              ·
                rfl

theorem cell20_103042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 6].length) (baseStart_103042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103042 prefixEnd_103042 := by exact prefixLift 103042
  have htrace : WordTrace (prefixWord ++ tailWord_103042) baseStart_103042 baseEnd_103042 := by
    simpa [prefixWord, tailWord_103042, baseEnd_103042] using wordTrace_append hprefix tailTrace_103042
  have hstable : (prefixWord ++ tailWord_103042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103042).length < 2 ^ (prefixWord ++ tailWord_103042).sum := by decide
  have hdescent : baseEnd_103042 < baseStart_103042 := by decide
  rcases family_descends (prefixWord ++ tailWord_103042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103066 : List Nat := [3, 1, 1, 6, 2, 1, 2, 1, 3]
def baseStart_103066 : Nat := 118140960795 + 103066 * 2 ^ 59
def prefixEnd_103066 : Nat := 4983230072969 + 3 ^ 40 * 103066 * 2
def baseEnd_103066 : Nat := 47042130787910211112013

theorem tailTrace_103066 : CollatzResearch.WordTrace tailWord_103066 prefixEnd_103066 47042130787910211112013 := by
  unfold tailWord_103066
  simp only [CollatzResearch.WordTrace]
  refine ⟨939781461154239779130263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2506083896411306077680701 939781461154239779130263)
  ·
    refine ⟨1409672191731359668695395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 939781461154239779130263 1409672191731359668695395)
    ·
      refine ⟨2114508287597039503043093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1409672191731359668695395 2114508287597039503043093)
      ·
        refine ⟨99117575981111226705145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2114508287597039503043093 99117575981111226705145)
        ·
          refine ⟨74338181985833420028859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99117575981111226705145 74338181985833420028859)
          ·
            refine ⟨111507272978750130043289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74338181985833420028859 111507272978750130043289)
            ·
              refine ⟨83630454734062597532467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111507272978750130043289 83630454734062597532467)
              ·
                refine ⟨125445682101093896298701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83630454734062597532467 125445682101093896298701)
                ·
                  refine ⟨47042130787910211112013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125445682101093896298701 47042130787910211112013)
                  ·
                    rfl

theorem cell20_103066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_103066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103066 prefixEnd_103066 := by exact prefixLift 103066
  have htrace : WordTrace (prefixWord ++ tailWord_103066) baseStart_103066 baseEnd_103066 := by
    simpa [prefixWord, tailWord_103066, baseEnd_103066] using wordTrace_append hprefix tailTrace_103066
  have hstable : (prefixWord ++ tailWord_103066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103066).length < 2 ^ (prefixWord ++ tailWord_103066).sum := by decide
  have hdescent : baseEnd_103066 < baseStart_103066 := by decide
  rcases family_descends (prefixWord ++ tailWord_103066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103098 : List Nat := [3, 1, 1, 1, 2, 3, 2, 5, 2]
def baseStart_103098 : Nat := 118140960795 + 103098 * 2 ^ 59
def prefixEnd_103098 : Nat := 4983230072969 + 3 ^ 40 * 103098 * 2
def baseEnd_103098 : Nat := 47056736459860322045215

theorem tailTrace_103098 : CollatzResearch.WordTrace tailWord_103098 prefixEnd_103098 47056736459860322045215 := by
  unfold tailWord_103098
  simp only [CollatzResearch.WordTrace]
  refine ⟨940073245125257145421487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2506861987000685721123965 940073245125257145421487)
  ·
    refine ⟨1410109867687885718132231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 940073245125257145421487 1410109867687885718132231)
    ·
      refine ⟨2115164801531828577198347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1410109867687885718132231 2115164801531828577198347)
      ·
        refine ⟨3172747202297742865797521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2115164801531828577198347 3172747202297742865797521)
        ·
          refine ⟨2379560401723307149348141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3172747202297742865797521 2379560401723307149348141)
          ·
            refine ⟨892335150646240181005553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2379560401723307149348141 892335150646240181005553)
            ·
              refine ⟨669251362984680135754165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892335150646240181005553 669251362984680135754165)
              ·
                refine ⟨62742315279813762726953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 669251362984680135754165 62742315279813762726953)
                ·
                  refine ⟨47056736459860322045215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62742315279813762726953 47056736459860322045215)
                  ·
                    rfl

theorem cell20_103098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_103098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103098 prefixEnd_103098 := by exact prefixLift 103098
  have htrace : WordTrace (prefixWord ++ tailWord_103098) baseStart_103098 baseEnd_103098 := by
    simpa [prefixWord, tailWord_103098, baseEnd_103098] using wordTrace_append hprefix tailTrace_103098
  have hstable : (prefixWord ++ tailWord_103098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103098).length < 2 ^ (prefixWord ++ tailWord_103098).sum := by decide
  have hdescent : baseEnd_103098 < baseStart_103098 := by decide
  rcases family_descends (prefixWord ++ tailWord_103098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103105 : List Nat := [1, 2, 6, 2, 9]
def baseStart_103105 : Nat := 118140960795 + 103105 * 2 ^ 59
def prefixEnd_103105 : Nat := 4983230072969 + 3 ^ 40 * 103105 * 2
def baseEnd_103105 : Nat := 580986808032091466813

theorem tailTrace_103105 : CollatzResearch.WordTrace tailWord_103105 prefixEnd_103105 580986808032091466813 := by
  unfold tailWord_103105
  simp only [CollatzResearch.WordTrace]
  refine ⟨3760548291475668777190769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2507032194317112518127179 3760548291475668777190769)
  ·
    refine ⟨2820411218606751582893077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3760548291475668777190769 2820411218606751582893077)
    ·
      refine ⟨132206775872191480448113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2820411218606751582893077 132206775872191480448113)
      ·
        refine ⟨99155081904143610336085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132206775872191480448113 99155081904143610336085)
        ·
          refine ⟨580986808032091466813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 99155081904143610336085 580986808032091466813)
          ·
            rfl

theorem cell20_103105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 9].length) (baseStart_103105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103105 prefixEnd_103105 := by exact prefixLift 103105
  have htrace : WordTrace (prefixWord ++ tailWord_103105) baseStart_103105 baseEnd_103105 := by
    simpa [prefixWord, tailWord_103105, baseEnd_103105] using wordTrace_append hprefix tailTrace_103105
  have hstable : (prefixWord ++ tailWord_103105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103105).length < 2 ^ (prefixWord ++ tailWord_103105).sum := by decide
  have hdescent : baseEnd_103105 < baseStart_103105 := by decide
  rcases family_descends (prefixWord ++ tailWord_103105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103112 : List Nat := [2, 1, 3, 1, 2, 3, 1, 4, 3]
def baseStart_103112 : Nat := 118140960795 + 103112 * 2 ^ 59
def prefixEnd_103112 : Nat := 4983230072969 + 3 ^ 40 * 103112 * 2
def baseEnd_103112 : Nat := 47063126441338495578491

theorem tailTrace_103112 : CollatzResearch.WordTrace tailWord_103112 prefixEnd_103112 47063126441338495578491 := by
  unfold tailWord_103112
  simp only [CollatzResearch.WordTrace]
  refine ⟨1880401801225154486347795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2507202401633539315130393 1880401801225154486347795)
  ·
    refine ⟨2820602701837731729521693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1880401801225154486347795 2820602701837731729521693)
    ·
      refine ⟨1057726013189149398570635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2820602701837731729521693 1057726013189149398570635)
      ·
        refine ⟨1586589019783724097855953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1057726013189149398570635 1586589019783724097855953)
        ·
          refine ⟨1189941764837793073391965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1586589019783724097855953 1189941764837793073391965)
          ·
            refine ⟨446228161814172402521987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1189941764837793073391965 446228161814172402521987)
            ·
              refine ⟨669342242721258603782981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446228161814172402521987 669342242721258603782981)
              ·
                refine ⟨125501670510235988209309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 669342242721258603782981 125501670510235988209309)
                ·
                  refine ⟨47063126441338495578491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125501670510235988209309 47063126441338495578491)
                  ·
                    rfl

theorem cell20_103112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_103112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103112 prefixEnd_103112 := by exact prefixLift 103112
  have htrace : WordTrace (prefixWord ++ tailWord_103112) baseStart_103112 baseEnd_103112 := by
    simpa [prefixWord, tailWord_103112, baseEnd_103112] using wordTrace_append hprefix tailTrace_103112
  have hstable : (prefixWord ++ tailWord_103112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103112).length < 2 ^ (prefixWord ++ tailWord_103112).sum := by decide
  have hdescent : baseEnd_103112 < baseStart_103112 := by decide
  rcases family_descends (prefixWord ++ tailWord_103112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103122 : List Nat := [3, 2, 2, 2, 3, 2, 1, 5]
def baseStart_103122 : Nat := 118140960795 + 103122 * 2 ^ 59
def prefixEnd_103122 : Nat := 4983230072969 + 3 ^ 40 * 103122 * 2
def baseEnd_103122 : Nat := 15689230237940968415039

theorem tailTrace_103122 : CollatzResearch.WordTrace tailWord_103122 prefixEnd_103122 15689230237940968415039 := by
  unfold tailWord_103122
  simp only [CollatzResearch.WordTrace]
  refine ⟨940292083103520170139905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2507445554942720453706413 940292083103520170139905)
  ·
    refine ⟨705219062327640127604929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 940292083103520170139905 705219062327640127604929)
    ·
      refine ⟨528914296745730095703697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 705219062327640127604929 528914296745730095703697)
      ·
        refine ⟨396685722559297571777773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528914296745730095703697 396685722559297571777773)
        ·
          refine ⟨148757145959736589416665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 396685722559297571777773 148757145959736589416665)
          ·
            refine ⟨111567859469802442062499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148757145959736589416665 111567859469802442062499)
            ·
              refine ⟨167351789204703663093749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111567859469802442062499 167351789204703663093749)
              ·
                refine ⟨15689230237940968415039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167351789204703663093749 15689230237940968415039)
                ·
                  rfl

theorem cell20_103122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_103122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103122 prefixEnd_103122 := by exact prefixLift 103122
  have htrace : WordTrace (prefixWord ++ tailWord_103122) baseStart_103122 baseEnd_103122 := by
    simpa [prefixWord, tailWord_103122, baseEnd_103122] using wordTrace_append hprefix tailTrace_103122
  have hstable : (prefixWord ++ tailWord_103122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103122).length < 2 ^ (prefixWord ++ tailWord_103122).sum := by decide
  have hdescent : baseEnd_103122 < baseStart_103122 := by decide
  rcases family_descends (prefixWord ++ tailWord_103122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103164 : List Nat := [2, 2, 2, 1, 3, 3, 7]
def baseStart_103164 : Nat := 118140960795 + 103164 * 2 ^ 59
def prefixEnd_103164 : Nat := 4983230072969 + 3 ^ 40 * 103164 * 2
def baseEnd_103164 : Nat := 5231873406473047316105

theorem tailTrace_103164 : CollatzResearch.WordTrace tailWord_103164 prefixEnd_103164 5231873406473047316105 := by
  unfold tailWord_103164
  simp only [CollatzResearch.WordTrace]
  refine ⟨1881350099130960926794273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2508466798841281235725697 1881350099130960926794273)
  ·
    refine ⟨1411012574348220695095705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1881350099130960926794273 1411012574348220695095705)
    ·
      refine ⟨1058259430761165521321779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1411012574348220695095705 1058259430761165521321779)
      ·
        refine ⟨1587389146141748281982669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1058259430761165521321779 1587389146141748281982669)
        ·
          refine ⟨595270929803155605743501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1587389146141748281982669 595270929803155605743501)
          ·
            refine ⟨223226598676183352153813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 595270929803155605743501 223226598676183352153813)
            ·
              refine ⟨5231873406473047316105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 223226598676183352153813 5231873406473047316105)
              ·
                rfl

theorem cell20_103164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 7].length) (baseStart_103164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103164 prefixEnd_103164 := by exact prefixLift 103164
  have htrace : WordTrace (prefixWord ++ tailWord_103164) baseStart_103164 baseEnd_103164 := by
    simpa [prefixWord, tailWord_103164, baseEnd_103164] using wordTrace_append hprefix tailTrace_103164
  have hstable : (prefixWord ++ tailWord_103164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103164).length < 2 ^ (prefixWord ++ tailWord_103164).sum := by decide
  have hdescent : baseEnd_103164 < baseStart_103164 := by decide
  rcases family_descends (prefixWord ++ tailWord_103164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103216 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 6]
def baseStart_103216 : Nat := 118140960795 + 103216 * 2 ^ 59
def prefixEnd_103216 : Nat := 4983230072969 + 3 ^ 40 * 103216 * 2
def baseEnd_103216 : Nat := 47110594875176356111399

theorem tailTrace_103216 : CollatzResearch.WordTrace tailWord_103216 prefixEnd_103216 47110594875176356111399 := by
  unfold tailWord_103216
  simp only [CollatzResearch.WordTrace]
  refine ⟨1882298397036767367240751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2509731196049023156321001 1882298397036767367240751)
  ·
    refine ⟨2823447595555151050861127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1882298397036767367240751 2823447595555151050861127)
    ·
      refine ⟨4235171393332726576291691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2823447595555151050861127 4235171393332726576291691)
      ·
        refine ⟨6352757089999089864437537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4235171393332726576291691 6352757089999089864437537)
        ·
          refine ⟨4764567817499317398328153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6352757089999089864437537 4764567817499317398328153)
          ·
            refine ⟨3573425863124488048746115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4764567817499317398328153 3573425863124488048746115)
            ·
              refine ⟨5360138794686732073119173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3573425863124488048746115 5360138794686732073119173)
              ·
                refine ⟨1005026024003762263709845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5360138794686732073119173 1005026024003762263709845)
                ·
                  refine ⟨47110594875176356111399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1005026024003762263709845 47110594875176356111399)
                  ·
                    rfl

theorem cell20_103216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_103216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103216 prefixEnd_103216 := by exact prefixLift 103216
  have htrace : WordTrace (prefixWord ++ tailWord_103216) baseStart_103216 baseEnd_103216 := by
    simpa [prefixWord, tailWord_103216, baseEnd_103216] using wordTrace_append hprefix tailTrace_103216
  have hstable : (prefixWord ++ tailWord_103216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103216).length < 2 ^ (prefixWord ++ tailWord_103216).sum := by decide
  have hdescent : baseEnd_103216 < baseStart_103216 := by decide
  rcases family_descends (prefixWord ++ tailWord_103216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103229 : List Nat := [1, 4, 1, 4, 2, 2, 1, 1, 4]
def baseStart_103229 : Nat := 118140960795 + 103229 * 2 ^ 59
def prefixEnd_103229 : Nat := 4983230072969 + 3 ^ 40 * 103229 * 2
def baseEnd_103229 : Nat := 47116528429406088678013

theorem tailTrace_103229 : CollatzResearch.WordTrace tailWord_103229 prefixEnd_103229 47116528429406088678013 := by
  unfold tailWord_103229
  simp only [CollatzResearch.WordTrace]
  refine ⟨3765070943026437954704741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2510047295350958636469827 3765070943026437954704741)
  ·
    refine ⟨705950801817457116507139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3765070943026437954704741 705950801817457116507139)
    ·
      refine ⟨1058926202726185674760709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 705950801817457116507139 1058926202726185674760709)
      ·
        refine ⟨198548663011159814017633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1058926202726185674760709 198548663011159814017633)
        ·
          refine ⟨148911497258369860513225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198548663011159814017633 148911497258369860513225)
          ·
            refine ⟨111683622943777395384919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148911497258369860513225 111683622943777395384919)
            ·
              refine ⟨167525434415666093077379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111683622943777395384919 167525434415666093077379)
              ·
                refine ⟨251288151623499139616069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167525434415666093077379 251288151623499139616069)
                ·
                  refine ⟨47116528429406088678013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251288151623499139616069 47116528429406088678013)
                  ·
                    rfl

theorem cell20_103229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_103229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103229 prefixEnd_103229 := by exact prefixLift 103229
  have htrace : WordTrace (prefixWord ++ tailWord_103229) baseStart_103229 baseEnd_103229 := by
    simpa [prefixWord, tailWord_103229, baseEnd_103229] using wordTrace_append hprefix tailTrace_103229
  have hstable : (prefixWord ++ tailWord_103229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103229).length < 2 ^ (prefixWord ++ tailWord_103229).sum := by decide
  have hdescent : baseEnd_103229 < baseStart_103229 := by decide
  rcases family_descends (prefixWord ++ tailWord_103229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103240 : List Nat := [2, 1, 3, 1, 1, 3, 4, 5]
def baseStart_103240 : Nat := 118140960795 + 103240 * 2 ^ 59
def prefixEnd_103240 : Nat := 4983230072969 + 3 ^ 40 * 103240 * 2
def baseEnd_103240 : Nat := 15707183043046313103767

theorem tailTrace_103240 : CollatzResearch.WordTrace tailWord_103240 prefixEnd_103240 15707183043046313103767 := by
  unfold tailWord_103240
  simp only [CollatzResearch.WordTrace]
  refine ⟨1882736072993293416677587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2510314763991057888903449 1882736072993293416677587)
  ·
    refine ⟨2824104109489940125016381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1882736072993293416677587 2824104109489940125016381)
    ·
      refine ⟨1059039041058727546881143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2824104109489940125016381 1059039041058727546881143)
      ·
        refine ⟨1588558561588091320321715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1059039041058727546881143 1588558561588091320321715)
        ·
          refine ⟨2382837842382136980482573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1588558561588091320321715 2382837842382136980482573)
          ·
            refine ⟨893564190893301367680965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2382837842382136980482573 893564190893301367680965)
            ·
              refine ⟨167543285792494006440181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 893564190893301367680965 167543285792494006440181)
              ·
                refine ⟨15707183043046313103767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167543285792494006440181 15707183043046313103767)
                ·
                  rfl

theorem cell20_103240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_103240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103240 prefixEnd_103240 := by exact prefixLift 103240
  have htrace : WordTrace (prefixWord ++ tailWord_103240) baseStart_103240 baseEnd_103240 := by
    simpa [prefixWord, tailWord_103240, baseEnd_103240] using wordTrace_append hprefix tailTrace_103240
  have hstable : (prefixWord ++ tailWord_103240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103240).length < 2 ^ (prefixWord ++ tailWord_103240).sum := by decide
  have hdescent : baseEnd_103240 < baseStart_103240 := by decide
  rcases family_descends (prefixWord ++ tailWord_103240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103278 : List Nat := [4, 1, 2, 3, 10]
def baseStart_103278 : Nat := 118140960795 + 103278 * 2 ^ 59
def prefixEnd_103278 : Nat := 4983230072969 + 3 ^ 40 * 103278 * 2
def baseEnd_103278 : Nat := 581961646476292543759

theorem tailTrace_103278 : CollatzResearch.WordTrace tailWord_103278 prefixEnd_103278 581961646476292543759 := by
  unfold tailWord_103278
  simp only [CollatzResearch.WordTrace]
  refine ⟨470857264981114915404811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2511238746565946215492325 470857264981114915404811)
  ·
    refine ⟨706285897471672373107217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 470857264981114915404811 706285897471672373107217)
    ·
      refine ⟨529714423103754279830413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 706285897471672373107217 529714423103754279830413)
      ·
        refine ⟨198642908663907854936405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 529714423103754279830413 198642908663907854936405)
        ·
          refine ⟨581961646476292543759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 198642908663907854936405 581961646476292543759)
          ·
            rfl

theorem cell20_103278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 10].length) (baseStart_103278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103278 prefixEnd_103278 := by exact prefixLift 103278
  have htrace : WordTrace (prefixWord ++ tailWord_103278) baseStart_103278 baseEnd_103278 := by
    simpa [prefixWord, tailWord_103278, baseEnd_103278] using wordTrace_append hprefix tailTrace_103278
  have hstable : (prefixWord ++ tailWord_103278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103278).length < 2 ^ (prefixWord ++ tailWord_103278).sum := by decide
  have hdescent : baseEnd_103278 < baseStart_103278 := by decide
  rcases family_descends (prefixWord ++ tailWord_103278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103292 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 8]
def baseStart_103292 : Nat := 118140960795 + 103292 * 2 ^ 59
def prefixEnd_103292 : Nat := 4983230072969 + 3 ^ 40 * 103292 * 2
def baseEnd_103292 : Nat := 47145283346057869577755

theorem tailTrace_103292 : CollatzResearch.WordTrace tailWord_103292 prefixEnd_103292 47145283346057869577755 := by
  unfold tailWord_103292
  simp only [CollatzResearch.WordTrace]
  refine ⟨1883684370899099857124065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2511579161198799809498753 1883684370899099857124065)
  ·
    refine ⟨1412763278174324892843049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1883684370899099857124065 1412763278174324892843049)
    ·
      refine ⟨1059572458630743669632287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1412763278174324892843049 1059572458630743669632287)
      ·
        refine ⟨1589358687946115504448431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1059572458630743669632287 1589358687946115504448431)
        ·
          refine ⟨2384038031919173256672647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1589358687946115504448431 2384038031919173256672647)
          ·
            refine ⟨3576057047878759885008971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2384038031919173256672647 3576057047878759885008971)
            ·
              refine ⟨5364085571818139827513457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3576057047878759885008971 5364085571818139827513457)
              ·
                refine ⟨4023064178863604870635093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5364085571818139827513457 4023064178863604870635093)
                ·
                  refine ⟨47145283346057869577755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4023064178863604870635093 47145283346057869577755)
                  ·
                    rfl

theorem cell20_103292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_103292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103292 prefixEnd_103292 := by exact prefixLift 103292
  have htrace : WordTrace (prefixWord ++ tailWord_103292) baseStart_103292 baseEnd_103292 := by
    simpa [prefixWord, tailWord_103292, baseEnd_103292] using wordTrace_append hprefix tailTrace_103292
  have hstable : (prefixWord ++ tailWord_103292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103292).length < 2 ^ (prefixWord ++ tailWord_103292).sum := by decide
  have hdescent : baseEnd_103292 < baseStart_103292 := by decide
  rcases family_descends (prefixWord ++ tailWord_103292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103337 : List Nat := [1, 2, 1, 1, 1, 1, 13]
def baseStart_103337 : Nat := 118140960795 + 103337 * 2 ^ 59
def prefixEnd_103337 : Nat := 4983230072969 + 3 ^ 40 * 103337 * 2
def baseEnd_103337 : Nat := 5240646952470857008619

theorem tailTrace_103337 : CollatzResearch.WordTrace tailWord_103337 prefixEnd_103337 5240646952470857008619 := by
  unfold tailWord_103337
  simp only [CollatzResearch.WordTrace]
  refine ⟨3769010026635172399636265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2512673351090114933090843 3769010026635172399636265)
  ·
    refine ⟨2826757519976379299727199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3769010026635172399636265 2826757519976379299727199)
    ·
      refine ⟨4240136279964568949590799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2826757519976379299727199 4240136279964568949590799)
      ·
        refine ⟨6360204419946853424386199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4240136279964568949590799 6360204419946853424386199)
        ·
          refine ⟨9540306629920280136579299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6360204419946853424386199 9540306629920280136579299)
          ·
            refine ⟨14310459944880420204868949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9540306629920280136579299 14310459944880420204868949)
            ·
              refine ⟨5240646952470857008619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 14310459944880420204868949 5240646952470857008619)
              ·
                rfl

theorem cell20_103337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 13].length) (baseStart_103337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103337 prefixEnd_103337 := by exact prefixLift 103337
  have htrace : WordTrace (prefixWord ++ tailWord_103337) baseStart_103337 baseEnd_103337 := by
    simpa [prefixWord, tailWord_103337, baseEnd_103337] using wordTrace_append hprefix tailTrace_103337
  have hstable : (prefixWord ++ tailWord_103337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103337).length < 2 ^ (prefixWord ++ tailWord_103337).sum := by decide
  have hdescent : baseEnd_103337 < baseStart_103337 := by decide
  rcases family_descends (prefixWord ++ tailWord_103337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103371 : List Nat := [1, 1, 1, 1, 3, 7, 2, 4]
def baseStart_103371 : Nat := 118140960795 + 103371 * 2 ^ 59
def prefixEnd_103371 : Nat := 4983230072969 + 3 ^ 40 * 103371 * 2
def baseEnd_103371 : Nat := 15727113699561568648033

theorem tailTrace_103371 : CollatzResearch.WordTrace tailWord_103371 prefixEnd_103371 15727113699561568648033 := by
  unfold tailWord_103371
  simp only [CollatzResearch.WordTrace]
  refine ⟨3770250108511996206373967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2513500072341330804249311 3770250108511996206373967)
  ·
    refine ⟨5655375162767994309560951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3770250108511996206373967 5655375162767994309560951)
    ·
      refine ⟨8483062744151991464341427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5655375162767994309560951 8483062744151991464341427)
      ·
        refine ⟨12724594116227987196512141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8483062744151991464341427 12724594116227987196512141)
        ·
          refine ⟨4771722793585495198692053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12724594116227987196512141 4771722793585495198692053)
          ·
            refine ⟨111837252974660043719345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4771722793585495198692053 111837252974660043719345)
            ·
              refine ⟨83877939730995032789509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111837252974660043719345 83877939730995032789509)
              ·
                refine ⟨15727113699561568648033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83877939730995032789509 15727113699561568648033)
                ·
                  rfl

theorem cell20_103371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 4].length) (baseStart_103371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103371 prefixEnd_103371 := by exact prefixLift 103371
  have htrace : WordTrace (prefixWord ++ tailWord_103371) baseStart_103371 baseEnd_103371 := by
    simpa [prefixWord, tailWord_103371, baseEnd_103371] using wordTrace_append hprefix tailTrace_103371
  have hstable : (prefixWord ++ tailWord_103371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103371).length < 2 ^ (prefixWord ++ tailWord_103371).sum := by decide
  have hdescent : baseEnd_103371 < baseStart_103371 := by decide
  rcases family_descends (prefixWord ++ tailWord_103371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103373 : List Nat := [1, 6, 3, 1, 2, 1, 1, 3, 2]
def baseStart_103373 : Nat := 118140960795 + 103373 * 2 ^ 59
def prefixEnd_103373 : Nat := 4983230072969 + 3 ^ 40 * 103373 * 2
def baseEnd_103373 : Nat := 47182253953181587877425

theorem tailTrace_103373 : CollatzResearch.WordTrace tailWord_103373 prefixEnd_103373 47182253953181587877425 := by
  unfold tailWord_103373
  simp only [CollatzResearch.WordTrace]
  refine ⟨3770323054504750547946773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2513548703003167031964515 3770323054504750547946773)
  ·
    refine ⟨176733893179910181935005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3770323054504750547946773 176733893179910181935005)
    ·
      refine ⟨66275209942466318225627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176733893179910181935005 66275209942466318225627)
      ·
        refine ⟨99412814913699477338441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66275209942466318225627 99412814913699477338441)
        ·
          refine ⟨74559611185274608003831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99412814913699477338441 74559611185274608003831)
          ·
            refine ⟨111839416777911912005747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74559611185274608003831 111839416777911912005747)
            ·
              refine ⟨167759125166867868008621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111839416777911912005747 167759125166867868008621)
              ·
                refine ⟨62909671937575450503233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167759125166867868008621 62909671937575450503233)
                ·
                  refine ⟨47182253953181587877425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62909671937575450503233 47182253953181587877425)
                  ·
                    rfl

theorem cell20_103373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_103373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103373 prefixEnd_103373 := by exact prefixLift 103373
  have htrace : WordTrace (prefixWord ++ tailWord_103373) baseStart_103373 baseEnd_103373 := by
    simpa [prefixWord, tailWord_103373, baseEnd_103373] using wordTrace_append hprefix tailTrace_103373
  have hstable : (prefixWord ++ tailWord_103373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103373).length < 2 ^ (prefixWord ++ tailWord_103373).sum := by decide
  have hdescent : baseEnd_103373 < baseStart_103373 := by decide
  rcases family_descends (prefixWord ++ tailWord_103373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103378 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_103378 : Nat := 118140960795 + 103378 * 2 ^ 59
def prefixEnd_103378 : Nat := 4983230072969 + 3 ^ 40 * 103378 * 2
def baseEnd_103378 : Nat := 47184536089423792710737

theorem tailTrace_103378 : CollatzResearch.WordTrace tailWord_103378 prefixEnd_103378 47184536089423792710737 := by
  unfold tailWord_103378
  simp only [CollatzResearch.WordTrace]
  refine ⟨942626354871659100469697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2513670279657757601252525 942626354871659100469697)
  ·
    refine ⟨706969766153744325352273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 942626354871659100469697 706969766153744325352273)
    ·
      refine ⟨530227324615308244014205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 706969766153744325352273 530227324615308244014205)
      ·
        refine ⟨198835246730740591505327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 530227324615308244014205 198835246730740591505327)
        ·
          refine ⟨298252870096110887257991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198835246730740591505327 298252870096110887257991)
          ·
            refine ⟨447379305144166330886987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298252870096110887257991 447379305144166330886987)
            ·
              refine ⟨671068957716249496330481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447379305144166330886987 671068957716249496330481)
              ·
                refine ⟨503301718287187122247861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671068957716249496330481 503301718287187122247861)
                ·
                  refine ⟨47184536089423792710737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 503301718287187122247861 47184536089423792710737)
                  ·
                    rfl

theorem cell20_103378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_103378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103378 prefixEnd_103378 := by exact prefixLift 103378
  have htrace : WordTrace (prefixWord ++ tailWord_103378) baseStart_103378 baseEnd_103378 := by
    simpa [prefixWord, tailWord_103378, baseEnd_103378] using wordTrace_append hprefix tailTrace_103378
  have hstable : (prefixWord ++ tailWord_103378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103378).length < 2 ^ (prefixWord ++ tailWord_103378).sum := by decide
  have hdescent : baseEnd_103378 < baseStart_103378 := by decide
  rcases family_descends (prefixWord ++ tailWord_103378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103402 : List Nat := [3, 1, 3, 1, 2, 4, 1, 1, 4]
def baseStart_103402 : Nat := 118140960795 + 103402 * 2 ^ 59
def prefixEnd_103402 : Nat := 4983230072969 + 3 ^ 40 * 103402 * 2
def baseEnd_103402 : Nat := 47195490343386375910639

theorem tailTrace_103402 : CollatzResearch.WordTrace tailWord_103402 prefixEnd_103402 47195490343386375910639 := by
  unfold tailWord_103402
  simp only [CollatzResearch.WordTrace]
  refine ⟨942845192849922125188115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2514253847599792333834973 942845192849922125188115)
  ·
    refine ⟨1414267789274883187782173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 942845192849922125188115 1414267789274883187782173)
    ·
      refine ⟨530350420978081195418315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1414267789274883187782173 530350420978081195418315)
      ·
        refine ⟨795525631467121793127473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530350420978081195418315 795525631467121793127473)
        ·
          refine ⟨596644223600341344845605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 795525631467121793127473 596644223600341344845605)
          ·
            refine ⟨111870791925064002158551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 596644223600341344845605 111870791925064002158551)
            ·
              refine ⟨167806187887596003237827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111870791925064002158551 167806187887596003237827)
              ·
                refine ⟨251709281831394004856741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167806187887596003237827 251709281831394004856741)
                ·
                  refine ⟨47195490343386375910639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251709281831394004856741 47195490343386375910639)
                  ·
                    rfl

theorem cell20_103402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_103402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103402 prefixEnd_103402 := by exact prefixLift 103402
  have htrace : WordTrace (prefixWord ++ tailWord_103402) baseStart_103402 baseEnd_103402 := by
    simpa [prefixWord, tailWord_103402, baseEnd_103402] using wordTrace_append hprefix tailTrace_103402
  have hstable : (prefixWord ++ tailWord_103402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103402).length < 2 ^ (prefixWord ++ tailWord_103402).sum := by decide
  have hdescent : baseEnd_103402 < baseStart_103402 := by decide
  rcases family_descends (prefixWord ++ tailWord_103402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103453 : List Nat := [1, 4, 2, 2, 4, 1, 2, 2, 2]
def baseStart_103453 : Nat := 118140960795 + 103453 * 2 ^ 59
def prefixEnd_103453 : Nat := 4983230072969 + 3 ^ 40 * 103453 * 2
def baseEnd_103453 : Nat := 47218768133056865210431

theorem tailTrace_103453 : CollatzResearch.WordTrace tailWord_103453 prefixEnd_103453 47218768133056865210431 := by
  unfold tailWord_103453
  simp only [CollatzResearch.WordTrace]
  refine ⟨3773240894214924210859013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2515493929476616140572675 3773240894214924210859013)
  ·
    refine ⟨707482667665298289536065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3773240894214924210859013 707482667665298289536065)
    ·
      refine ⟨530612000748973717152049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 707482667665298289536065 530612000748973717152049)
      ·
        refine ⟨397959000561730287864037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 530612000748973717152049 397959000561730287864037)
        ·
          refine ⟨74617312605324428974507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 397959000561730287864037 74617312605324428974507)
          ·
            refine ⟨111925968907986643461761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74617312605324428974507 111925968907986643461761)
            ·
              refine ⟨83944476680989982596321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111925968907986643461761 83944476680989982596321)
              ·
                refine ⟨62958357510742486947241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83944476680989982596321 62958357510742486947241)
                ·
                  refine ⟨47218768133056865210431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62958357510742486947241 47218768133056865210431)
                  ·
                    rfl

theorem cell20_103453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_103453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103453 prefixEnd_103453 := by exact prefixLift 103453
  have htrace : WordTrace (prefixWord ++ tailWord_103453) baseStart_103453 baseEnd_103453 := by
    simpa [prefixWord, tailWord_103453, baseEnd_103453] using wordTrace_append hprefix tailTrace_103453
  have hstable : (prefixWord ++ tailWord_103453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103453).length < 2 ^ (prefixWord ++ tailWord_103453).sum := by decide
  have hdescent : baseEnd_103453 < baseStart_103453 := by decide
  rcases family_descends (prefixWord ++ tailWord_103453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103457 : List Nat := [1, 2, 3, 2, 3, 1, 4, 2, 2]
def baseStart_103457 : Nat := 118140960795 + 103457 * 2 ^ 59
def prefixEnd_103457 : Nat := 4983230072969 + 3 ^ 40 * 103457 * 2
def baseEnd_103457 : Nat := 47220593842050629077081

theorem tailTrace_103457 : CollatzResearch.WordTrace tailWord_103457 prefixEnd_103457 47220593842050629077081 := by
  unfold tailWord_103457
  simp only [CollatzResearch.WordTrace]
  refine ⟨3773386786200432894004625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2515591190800288596003083 3773386786200432894004625)
  ·
    refine ⟨2830040089650324670503469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3773386786200432894004625 2830040089650324670503469)
    ·
      refine ⟨1061265033618871751438801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2830040089650324670503469 1061265033618871751438801)
      ·
        refine ⟨795948775214153813579101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1061265033618871751438801 795948775214153813579101)
        ·
          refine ⟨298480790705307680092163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 795948775214153813579101 298480790705307680092163)
          ·
            refine ⟨447721186057961520138245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298480790705307680092163 447721186057961520138245)
            ·
              refine ⟨83947722385867785025921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 447721186057961520138245 83947722385867785025921)
              ·
                refine ⟨62960791789400838769441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83947722385867785025921 62960791789400838769441)
                ·
                  refine ⟨47220593842050629077081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62960791789400838769441 47220593842050629077081)
                  ·
                    rfl

theorem cell20_103457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 2].length) (baseStart_103457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103457 prefixEnd_103457 := by exact prefixLift 103457
  have htrace : WordTrace (prefixWord ++ tailWord_103457) baseStart_103457 baseEnd_103457 := by
    simpa [prefixWord, tailWord_103457, baseEnd_103457] using wordTrace_append hprefix tailTrace_103457
  have hstable : (prefixWord ++ tailWord_103457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103457).length < 2 ^ (prefixWord ++ tailWord_103457).sum := by decide
  have hdescent : baseEnd_103457 < baseStart_103457 := by decide
  rcases family_descends (prefixWord ++ tailWord_103457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103478 : List Nat := [5, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_103478 : Nat := 118140960795 + 103478 * 2 ^ 59
def prefixEnd_103478 : Nat := 4983230072969 + 3 ^ 40 * 103478 * 2
def baseEnd_103478 : Nat := 47230178814267889376995

theorem tailTrace_103478 : CollatzResearch.WordTrace tailWord_103478 prefixEnd_103478 47230178814267889376995 := by
  unfold tailWord_103478
  simp only [CollatzResearch.WordTrace]
  refine ⟨235884544945272092532443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2516101812749568987012725 235884544945272092532443)
  ·
    refine ⟨353826817417908138798665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235884544945272092532443 353826817417908138798665)
    ·
      refine ⟨265370113063431104098999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353826817417908138798665 265370113063431104098999)
      ·
        refine ⟨398055169595146656148499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265370113063431104098999 398055169595146656148499)
        ·
          refine ⟨597082754392719984222749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398055169595146656148499 597082754392719984222749)
          ·
            refine ⟨223906032897269994083531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 597082754392719984222749 223906032897269994083531)
            ·
              refine ⟨335859049345904991125297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223906032897269994083531 335859049345904991125297)
              ·
                refine ⟨251894287009428743343973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335859049345904991125297 251894287009428743343973)
                ·
                  refine ⟨47230178814267889376995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251894287009428743343973 47230178814267889376995)
                  ·
                    rfl

theorem cell20_103478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_103478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103478 prefixEnd_103478 := by exact prefixLift 103478
  have htrace : WordTrace (prefixWord ++ tailWord_103478) baseStart_103478 baseEnd_103478 := by
    simpa [prefixWord, tailWord_103478, baseEnd_103478] using wordTrace_append hprefix tailTrace_103478
  have hstable : (prefixWord ++ tailWord_103478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103478).length < 2 ^ (prefixWord ++ tailWord_103478).sum := by decide
  have hdescent : baseEnd_103478 < baseStart_103478 := by decide
  rcases family_descends (prefixWord ++ tailWord_103478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103482 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_103482 : Nat := 118140960795 + 103482 * 2 ^ 59
def prefixEnd_103482 : Nat := 4983230072969 + 3 ^ 40 * 103482 * 2
def baseEnd_103482 : Nat := 47232004523261653243645

theorem tailTrace_103482 : CollatzResearch.WordTrace tailWord_103482 prefixEnd_103482 47232004523261653243645 := by
  unfold tailWord_103482
  simp only [CollatzResearch.WordTrace]
  refine ⟨943574652777465540916175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2516199074073241442443133 943574652777465540916175)
  ·
    refine ⟨1415361979166198311374263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 943574652777465540916175 1415361979166198311374263)
    ·
      refine ⟨2123042968749297467061395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1415361979166198311374263 2123042968749297467061395)
      ·
        refine ⟨3184564453123946200592093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2123042968749297467061395 3184564453123946200592093)
        ·
          refine ⟨1194211669921479825222035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3184564453123946200592093 1194211669921479825222035)
          ·
            refine ⟨1791317504882219737833053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1194211669921479825222035 1791317504882219737833053)
            ·
              refine ⟨671744064330832401687395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1791317504882219737833053 671744064330832401687395)
              ·
                refine ⟨1007616096496248602531093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671744064330832401687395 1007616096496248602531093)
                ·
                  refine ⟨47232004523261653243645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1007616096496248602531093 47232004523261653243645)
                  ·
                    rfl

theorem cell20_103482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_103482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103482 prefixEnd_103482 := by exact prefixLift 103482
  have htrace : WordTrace (prefixWord ++ tailWord_103482) baseStart_103482 baseEnd_103482 := by
    simpa [prefixWord, tailWord_103482, baseEnd_103482] using wordTrace_append hprefix tailTrace_103482
  have hstable : (prefixWord ++ tailWord_103482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103482).length < 2 ^ (prefixWord ++ tailWord_103482).sum := by decide
  have hdescent : baseEnd_103482 < baseStart_103482 := by decide
  rcases family_descends (prefixWord ++ tailWord_103482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103485 : List Nat := [1, 4, 1, 3, 1, 3, 3, 4]
def baseStart_103485 : Nat := 118140960795 + 103485 * 2 ^ 59
def prefixEnd_103485 : Nat := 4983230072969 + 3 ^ 40 * 103485 * 2
def baseEnd_103485 : Nat := 15744457935002325381211

theorem tailTrace_103485 : CollatzResearch.WordTrace tailWord_103485 prefixEnd_103485 15744457935002325381211 := by
  unfold tailWord_103485
  simp only [CollatzResearch.WordTrace]
  refine ⟨3774408030098993676023909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2516272020065995784015939 3774408030098993676023909)
  ·
    refine ⟨707701505643561314254483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3774408030098993676023909 707701505643561314254483)
    ·
      refine ⟨1061552258465341971381725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 707701505643561314254483 1061552258465341971381725)
      ·
        refine ⟨398082096924503239268147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1061552258465341971381725 398082096924503239268147)
        ·
          refine ⟨597123145386754858902221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398082096924503239268147 597123145386754858902221)
          ·
            refine ⟨223921179520033072088333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 597123145386754858902221 223921179520033072088333)
            ·
              refine ⟨83970442320012402033125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223921179520033072088333 83970442320012402033125)
              ·
                refine ⟨15744457935002325381211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83970442320012402033125 15744457935002325381211)
                ·
                  rfl

theorem cell20_103485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 4].length) (baseStart_103485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103485 prefixEnd_103485 := by exact prefixLift 103485
  have htrace : WordTrace (prefixWord ++ tailWord_103485) baseStart_103485 baseEnd_103485 := by
    simpa [prefixWord, tailWord_103485, baseEnd_103485] using wordTrace_append hprefix tailTrace_103485
  have hstable : (prefixWord ++ tailWord_103485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103485).length < 2 ^ (prefixWord ++ tailWord_103485).sum := by decide
  have hdescent : baseEnd_103485 < baseStart_103485 := by decide
  rcases family_descends (prefixWord ++ tailWord_103485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103506 : List Nat := [3, 2, 2, 1, 3, 2, 7]
def baseStart_103506 : Nat := 118140960795 + 103506 * 2 ^ 59
def prefixEnd_103506 : Nat := 4983230072969 + 3 ^ 40 * 103506 * 2
def baseEnd_103506 : Nat := 5249217641913804049283

theorem tailTrace_103506 : CollatzResearch.WordTrace tailWord_103506 prefixEnd_103506 5249217641913804049283 := by
  unfold tailWord_103506
  simp only [CollatzResearch.WordTrace]
  refine ⟨943793490755728565634593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2516782642015276175025581 943793490755728565634593)
  ·
    refine ⟨707845118066796424225945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 943793490755728565634593 707845118066796424225945)
    ·
      refine ⟨530883838550097318169459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 707845118066796424225945 530883838550097318169459)
      ·
        refine ⟨796325757825145977254189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530883838550097318169459 796325757825145977254189)
        ·
          refine ⟨298622159184429741470321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 796325757825145977254189 298622159184429741470321)
          ·
            refine ⟨223966619388322306102741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298622159184429741470321 223966619388322306102741)
            ·
              refine ⟨5249217641913804049283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 223966619388322306102741 5249217641913804049283)
              ·
                rfl

theorem cell20_103506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 7].length) (baseStart_103506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103506 prefixEnd_103506 := by exact prefixLift 103506
  have htrace : WordTrace (prefixWord ++ tailWord_103506) baseStart_103506 baseEnd_103506 := by
    simpa [prefixWord, tailWord_103506, baseEnd_103506] using wordTrace_append hprefix tailTrace_103506
  have hstable : (prefixWord ++ tailWord_103506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103506).length < 2 ^ (prefixWord ++ tailWord_103506).sum := by decide
  have hdescent : baseEnd_103506 < baseStart_103506 := by decide
  rcases family_descends (prefixWord ++ tailWord_103506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103513 : List Nat := [1, 2, 1, 2, 2, 1, 2, 6, 3]
def baseStart_103513 : Nat := 118140960795 + 103513 * 2 ^ 59
def prefixEnd_103513 : Nat := 4983230072969 + 3 ^ 40 * 103513 * 2
def baseEnd_103513 : Nat := 47246153767963323210185

theorem tailTrace_103513 : CollatzResearch.WordTrace tailWord_103513 prefixEnd_103513 47246153767963323210185 := by
  unfold tailWord_103513
  simp only [CollatzResearch.WordTrace]
  refine ⟨3775429273997554458043193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2516952849331702972028795 3775429273997554458043193)
  ·
    refine ⟨2831571955498165843532395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3775429273997554458043193 2831571955498165843532395)
    ·
      refine ⟨4247357933247248765298593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2831571955498165843532395 4247357933247248765298593)
      ·
        refine ⟨3185518449935436573973945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4247357933247248765298593 3185518449935436573973945)
        ·
          refine ⟨2389138837451577430480459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3185518449935436573973945 2389138837451577430480459)
          ·
            refine ⟨3583708256177366145720689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389138837451577430480459 3583708256177366145720689)
            ·
              refine ⟨2687781192133024609290517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3583708256177366145720689 2687781192133024609290517)
              ·
                refine ⟨125989743381235528560493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2687781192133024609290517 125989743381235528560493)
                ·
                  refine ⟨47246153767963323210185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125989743381235528560493 47246153767963323210185)
                  ·
                    rfl

theorem cell20_103513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_103513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103513 prefixEnd_103513 := by exact prefixLift 103513
  have htrace : WordTrace (prefixWord ++ tailWord_103513) baseStart_103513 baseEnd_103513 := by
    simpa [prefixWord, tailWord_103513, baseEnd_103513] using wordTrace_append hprefix tailTrace_103513
  have hstable : (prefixWord ++ tailWord_103513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103513).length < 2 ^ (prefixWord ++ tailWord_103513).sum := by decide
  have hdescent : baseEnd_103513 < baseStart_103513 := by decide
  rcases family_descends (prefixWord ++ tailWord_103513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103516 : List Nat := [2, 2, 4, 1, 1, 1, 1, 6, 2]
def baseStart_103516 : Nat := 118140960795 + 103516 * 2 ^ 59
def prefixEnd_103516 : Nat := 4983230072969 + 3 ^ 40 * 103516 * 2
def baseEnd_103516 : Nat := 47247523049708646110173

theorem tailTrace_103516 : CollatzResearch.WordTrace tailWord_103516 prefixEnd_103516 47247523049708646110173 := by
  unfold tailWord_103516
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887769346493342985201201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2517025795324457313601601 1887769346493342985201201)
  ·
    refine ⟨1415827009870007238900901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1887769346493342985201201 1415827009870007238900901)
    ·
      refine ⟨265467564350626357293919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1415827009870007238900901 265467564350626357293919)
      ·
        refine ⟨398201346525939535940879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265467564350626357293919 398201346525939535940879)
        ·
          refine ⟨597302019788909303911319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398201346525939535940879 597302019788909303911319)
          ·
            refine ⟨895953029683363955866979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597302019788909303911319 895953029683363955866979)
            ·
              refine ⟨1343929544525045933800469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895953029683363955866979 1343929544525045933800469)
              ·
                refine ⟨62996697399611528146897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1343929544525045933800469 62996697399611528146897)
                ·
                  refine ⟨47247523049708646110173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62996697399611528146897 47247523049708646110173)
                  ·
                    rfl

theorem cell20_103516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_103516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103516 prefixEnd_103516 := by exact prefixLift 103516
  have htrace : WordTrace (prefixWord ++ tailWord_103516) baseStart_103516 baseEnd_103516 := by
    simpa [prefixWord, tailWord_103516, baseEnd_103516] using wordTrace_append hprefix tailTrace_103516
  have hstable : (prefixWord ++ tailWord_103516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103516).length < 2 ^ (prefixWord ++ tailWord_103516).sum := by decide
  have hdescent : baseEnd_103516 < baseStart_103516 := by decide
  rcases family_descends (prefixWord ++ tailWord_103516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103544 : List Nat := [2, 1, 2, 1, 1, 1, 8, 4]
def baseStart_103544 : Nat := 118140960795 + 103544 * 2 ^ 59
def prefixEnd_103544 : Nat := 4983230072969 + 3 ^ 40 * 103544 * 2
def baseEnd_103544 : Nat := 15753434337554997725575

theorem tailTrace_103544 : CollatzResearch.WordTrace tailWord_103544 prefixEnd_103544 15753434337554997725575 := by
  unfold tailWord_103544
  simp only [CollatzResearch.WordTrace]
  refine ⟨1888279968442623376210843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2517706624590164501614457 1888279968442623376210843)
  ·
    refine ⟨2832419952663935064316265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1888279968442623376210843 2832419952663935064316265)
    ·
      refine ⟨2124314964497951298237199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2832419952663935064316265 2124314964497951298237199)
      ·
        refine ⟨3186472446746926947355799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2124314964497951298237199 3186472446746926947355799)
        ·
          refine ⟨4779708670120390421033699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3186472446746926947355799 4779708670120390421033699)
          ·
            refine ⟨7169563005180585631550549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4779708670120390421033699 7169563005180585631550549)
            ·
              refine ⟨84018316466959987869733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 7169563005180585631550549 84018316466959987869733)
              ·
                refine ⟨15753434337554997725575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84018316466959987869733 15753434337554997725575)
                ·
                  rfl

theorem cell20_103544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_103544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103544 prefixEnd_103544 := by exact prefixLift 103544
  have htrace : WordTrace (prefixWord ++ tailWord_103544) baseStart_103544 baseEnd_103544 := by
    simpa [prefixWord, tailWord_103544, baseEnd_103544] using wordTrace_append hprefix tailTrace_103544
  have hstable : (prefixWord ++ tailWord_103544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103544).length < 2 ^ (prefixWord ++ tailWord_103544).sum := by decide
  have hdescent : baseEnd_103544 < baseStart_103544 := by decide
  rcases family_descends (prefixWord ++ tailWord_103544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103575 : List Nat := [1, 1, 3, 3, 3, 1, 3, 1, 4]
def baseStart_103575 : Nat := 118140960795 + 103575 * 2 ^ 59
def prefixEnd_103575 : Nat := 4983230072969 + 3 ^ 40 * 103575 * 2
def baseEnd_103575 : Nat := 47274452257366663143265

theorem tailTrace_103575 : CollatzResearch.WordTrace tailWord_103575 prefixEnd_103575 47274452257366663143265 := by
  unfold tailWord_103575
  simp only [CollatzResearch.WordTrace]
  refine ⟨3777690599772939046800179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2518460399848626031200119 3777690599772939046800179)
  ·
    refine ⟨5666535899659408570200269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3777690599772939046800179 5666535899659408570200269)
    ·
      refine ⟨2124950962372278213825101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5666535899659408570200269 2124950962372278213825101)
      ·
        refine ⟨796856610889604330184413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2124950962372278213825101 796856610889604330184413)
        ·
          refine ⟨298821229083601623819155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 796856610889604330184413 298821229083601623819155)
          ·
            refine ⟨448231843625402435728733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298821229083601623819155 448231843625402435728733)
            ·
              refine ⟨168086941359525913398275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 448231843625402435728733 168086941359525913398275)
              ·
                refine ⟨252130412039288870097413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168086941359525913398275 252130412039288870097413)
                ·
                  refine ⟨47274452257366663143265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 252130412039288870097413 47274452257366663143265)
                  ·
                    rfl

theorem cell20_103575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 4].length) (baseStart_103575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103575 prefixEnd_103575 := by exact prefixLift 103575
  have htrace : WordTrace (prefixWord ++ tailWord_103575) baseStart_103575 baseEnd_103575 := by
    simpa [prefixWord, tailWord_103575, baseEnd_103575] using wordTrace_append hprefix tailTrace_103575
  have hstable : (prefixWord ++ tailWord_103575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103575).length < 2 ^ (prefixWord ++ tailWord_103575).sum := by decide
  have hdescent : baseEnd_103575 < baseStart_103575 := by decide
  rcases family_descends (prefixWord ++ tailWord_103575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103603 : List Nat := [1, 1, 1, 2, 3, 2, 4, 6]
def baseStart_103603 : Nat := 118140960795 + 103603 * 2 ^ 59
def prefixEnd_103603 : Nat := 4983230072969 + 3 ^ 40 * 103603 * 2
def baseEnd_103603 : Nat := 15762410740107670069939

theorem tailTrace_103603 : CollatzResearch.WordTrace tailWord_103603 prefixEnd_103603 15762410740107670069939 := by
  unfold tailWord_103603
  simp only [CollatzResearch.WordTrace]
  refine ⟨3778711843671499828819463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2519141229114333219212975 3778711843671499828819463)
  ·
    refine ⟨5668067765507249743229195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3778711843671499828819463 5668067765507249743229195)
    ·
      refine ⟨8502101648260874614843793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5668067765507249743229195 8502101648260874614843793)
      ·
        refine ⟨6376576236195655961132845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8502101648260874614843793 6376576236195655961132845)
        ·
          refine ⟨2391216088573370985424817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6376576236195655961132845 2391216088573370985424817)
          ·
            refine ⟨1793412066430028239068613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2391216088573370985424817 1793412066430028239068613)
            ·
              refine ⟨336264762455630294825365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1793412066430028239068613 336264762455630294825365)
              ·
                refine ⟨15762410740107670069939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 336264762455630294825365 15762410740107670069939)
                ·
                  rfl

theorem cell20_103603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 6].length) (baseStart_103603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103603 prefixEnd_103603 := by exact prefixLift 103603
  have htrace : WordTrace (prefixWord ++ tailWord_103603) baseStart_103603 baseEnd_103603 := by
    simpa [prefixWord, tailWord_103603, baseEnd_103603] using wordTrace_append hprefix tailTrace_103603
  have hstable : (prefixWord ++ tailWord_103603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103603).length < 2 ^ (prefixWord ++ tailWord_103603).sum := by decide
  have hdescent : baseEnd_103603 < baseStart_103603 := by decide
  rcases family_descends (prefixWord ++ tailWord_103603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103620 : List Nat := [2, 3, 3, 1, 3, 8]
def baseStart_103620 : Nat := 118140960795 + 103620 * 2 ^ 59
def prefixEnd_103620 : Nat := 4983230072969 + 3 ^ 40 * 103620 * 2
def baseEnd_103620 : Nat := 1751666351242463209003

theorem tailTrace_103620 : CollatzResearch.WordTrace tailWord_103620 prefixEnd_103620 1751666351242463209003 := by
  unfold tailWord_103620
  simp only [CollatzResearch.WordTrace]
  refine ⟨1889665942304955866094157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2519554589739941154792209 1889665942304955866094157)
  ·
    refine ⟨708624728364358449785309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1889665942304955866094157 708624728364358449785309)
    ·
      refine ⟨265734273136634418669491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 708624728364358449785309 265734273136634418669491)
      ·
        refine ⟨398601409704951628004237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265734273136634418669491 398601409704951628004237)
        ·
          refine ⟨149475528639356860501589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398601409704951628004237 149475528639356860501589)
          ·
            refine ⟨1751666351242463209003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 149475528639356860501589 1751666351242463209003)
            ·
              rfl

theorem cell20_103620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 8].length) (baseStart_103620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103620 prefixEnd_103620 := by exact prefixLift 103620
  have htrace : WordTrace (prefixWord ++ tailWord_103620) baseStart_103620 baseEnd_103620 := by
    simpa [prefixWord, tailWord_103620, baseEnd_103620] using wordTrace_append hprefix tailTrace_103620
  have hstable : (prefixWord ++ tailWord_103620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103620).length < 2 ^ (prefixWord ++ tailWord_103620).sum := by decide
  have hdescent : baseEnd_103620 < baseStart_103620 := by decide
  rcases family_descends (prefixWord ++ tailWord_103620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103637 : List Nat := [1, 3, 2, 4, 1, 3, 1, 5]
def baseStart_103637 : Nat := 118140960795 + 103637 * 2 ^ 59
def prefixEnd_103637 : Nat := 4983230072969 + 3 ^ 40 * 103637 * 2
def baseEnd_103637 : Nat := 15767583582256667692115

theorem tailTrace_103637 : CollatzResearch.WordTrace tailWord_103637 prefixEnd_103637 15767583582256667692115 := by
  unfold tailWord_103637
  simp only [CollatzResearch.WordTrace]
  refine ⟨3779951925548323635557165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2519967950365549090371443 3779951925548323635557165)
  ·
    refine ⟨1417481972080621363333937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3779951925548323635557165 1417481972080621363333937)
    ·
      refine ⟨1063111479060466022500453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1417481972080621363333937 1063111479060466022500453)
      ·
        refine ⟨199333402323837379218835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1063111479060466022500453 199333402323837379218835)
        ·
          refine ⟨299000103485756068828253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199333402323837379218835 299000103485756068828253)
          ·
            refine ⟨112125038807158525810595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299000103485756068828253 112125038807158525810595)
            ·
              refine ⟨168187558210737788715893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112125038807158525810595 168187558210737788715893)
              ·
                refine ⟨15767583582256667692115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168187558210737788715893 15767583582256667692115)
                ·
                  rfl

theorem cell20_103637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 5].length) (baseStart_103637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103637 prefixEnd_103637 := by exact prefixLift 103637
  have htrace : WordTrace (prefixWord ++ tailWord_103637) baseStart_103637 baseEnd_103637 := by
    simpa [prefixWord, tailWord_103637, baseEnd_103637] using wordTrace_append hprefix tailTrace_103637
  have hstable : (prefixWord ++ tailWord_103637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103637).length < 2 ^ (prefixWord ++ tailWord_103637).sum := by decide
  have hdescent : baseEnd_103637 < baseStart_103637 := by decide
  rcases family_descends (prefixWord ++ tailWord_103637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103679 : List Nat := [1, 1, 2, 2, 1, 6, 7]
def baseStart_103679 : Nat := 118140960795 + 103679 * 2 ^ 59
def prefixEnd_103679 : Nat := 4983230072969 + 3 ^ 40 * 103679 * 2
def baseEnd_103679 : Nat := 5257991187911613741797

theorem tailTrace_103679 : CollatzResearch.WordTrace tailWord_103679 prefixEnd_103679 5257991187911613741797 := by
  unfold tailWord_103679
  simp only [CollatzResearch.WordTrace]
  refine ⟨3781483791396164808586091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2520989194264109872390727 3781483791396164808586091)
  ·
    refine ⟨5672225687094247212879137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3781483791396164808586091 5672225687094247212879137)
    ·
      refine ⟨4254169265320685409659353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5672225687094247212879137 4254169265320685409659353)
      ·
        refine ⟨3190626948990514057244515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4254169265320685409659353 3190626948990514057244515)
        ·
          refine ⟨4785940423485771085866773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3190626948990514057244515 4785940423485771085866773)
          ·
            refine ⟨224340957350895519650005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4785940423485771085866773 224340957350895519650005)
            ·
              refine ⟨5257991187911613741797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 224340957350895519650005 5257991187911613741797)
              ·
                rfl

theorem cell20_103679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 7].length) (baseStart_103679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103679 prefixEnd_103679 := by exact prefixLift 103679
  have htrace : WordTrace (prefixWord ++ tailWord_103679) baseStart_103679 baseEnd_103679 := by
    simpa [prefixWord, tailWord_103679, baseEnd_103679] using wordTrace_append hprefix tailTrace_103679
  have hstable : (prefixWord ++ tailWord_103679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103679).length < 2 ^ (prefixWord ++ tailWord_103679).sum := by decide
  have hdescent : baseEnd_103679 < baseStart_103679 := by decide
  rcases family_descends (prefixWord ++ tailWord_103679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103689 : List Nat := [1, 2, 1, 1, 3, 3, 1, 6, 2]
def baseStart_103689 : Nat := 118140960795 + 103689 * 2 ^ 59
def prefixEnd_103689 : Nat := 4983230072969 + 3 ^ 40 * 103689 * 2
def baseEnd_103689 : Nat := 47326484963688933342799

theorem tailTrace_103689 : CollatzResearch.WordTrace tailWord_103689 prefixEnd_103689 47326484963688933342799 := by
  unfold tailWord_103689
  simp only [CollatzResearch.WordTrace]
  refine ⟨3781848521359936516450121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2521232347573291010966747 3781848521359936516450121)
  ·
    refine ⟨2836386391019952387337591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3781848521359936516450121 2836386391019952387337591)
    ·
      refine ⟨4254579586529928581006387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2836386391019952387337591 4254579586529928581006387)
      ·
        refine ⟨6381869379794892871509581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4254579586529928581006387 6381869379794892871509581)
        ·
          refine ⟨2393201017423084826816093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6381869379794892871509581 2393201017423084826816093)
          ·
            refine ⟨897450381533656810056035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2393201017423084826816093 897450381533656810056035)
            ·
              refine ⟨1346175572300485215084053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897450381533656810056035 1346175572300485215084053)
              ·
                refine ⟨63101979951585244457065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1346175572300485215084053 63101979951585244457065)
                ·
                  refine ⟨47326484963688933342799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63101979951585244457065 47326484963688933342799)
                  ·
                    rfl

theorem cell20_103689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 2].length) (baseStart_103689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103689 prefixEnd_103689 := by exact prefixLift 103689
  have htrace : WordTrace (prefixWord ++ tailWord_103689) baseStart_103689 baseEnd_103689 := by
    simpa [prefixWord, tailWord_103689, baseEnd_103689] using wordTrace_append hprefix tailTrace_103689
  have hstable : (prefixWord ++ tailWord_103689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103689).length < 2 ^ (prefixWord ++ tailWord_103689).sum := by decide
  have hdescent : baseEnd_103689 < baseStart_103689 := by decide
  rcases family_descends (prefixWord ++ tailWord_103689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103744 : List Nat := [2, 1, 1, 2, 2, 1, 7, 2, 2]
def baseStart_103744 : Nat := 118140960795 + 103744 * 2 ^ 59
def prefixEnd_103744 : Nat := 4983230072969 + 3 ^ 40 * 103744 * 2
def baseEnd_103744 : Nat := 47351588462353186509241

theorem tailTrace_103744 : CollatzResearch.WordTrace tailWord_103744 prefixEnd_103744 47351588462353186509241 := by
  unfold tailWord_103744
  simp only [CollatzResearch.WordTrace]
  refine ⟨1891927268080340454851143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2522569690773787273134857 1891927268080340454851143)
  ·
    refine ⟨2837890902120510682276715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1891927268080340454851143 2837890902120510682276715)
    ·
      refine ⟨4256836353180766023415073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2837890902120510682276715 4256836353180766023415073)
      ·
        refine ⟨3192627264885574517561305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4256836353180766023415073 3192627264885574517561305)
        ·
          refine ⟨2394470448664180888170979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3192627264885574517561305 2394470448664180888170979)
          ·
            refine ⟨3591705672996271332256469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2394470448664180888170979 3591705672996271332256469)
            ·
              refine ⟨84180601710850109349761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3591705672996271332256469 84180601710850109349761)
              ·
                refine ⟨63135451283137582012321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84180601710850109349761 63135451283137582012321)
                ·
                  refine ⟨47351588462353186509241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63135451283137582012321 47351588462353186509241)
                  ·
                    rfl

theorem cell20_103744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 2].length) (baseStart_103744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103744 prefixEnd_103744 := by exact prefixLift 103744
  have htrace : WordTrace (prefixWord ++ tailWord_103744) baseStart_103744 baseEnd_103744 := by
    simpa [prefixWord, tailWord_103744, baseEnd_103744] using wordTrace_append hprefix tailTrace_103744
  have hstable : (prefixWord ++ tailWord_103744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103744).length < 2 ^ (prefixWord ++ tailWord_103744).sum := by decide
  have hdescent : baseEnd_103744 < baseStart_103744 := by decide
  rcases family_descends (prefixWord ++ tailWord_103744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103750 : List Nat := [6, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_103750 : Nat := 118140960795 + 103750 * 2 ^ 59
def prefixEnd_103750 : Nat := 4983230072969 + 3 ^ 40 * 103750 * 2
def baseEnd_103750 : Nat := 47354327025843832309217

theorem tailTrace_103750 : CollatzResearch.WordTrace tailWord_103750 prefixEnd_103750 47354327025843832309217 := by
  unfold tailWord_103750
  simp only [CollatzResearch.WordTrace]
  refine ⟨118252292941841997950647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2522715582759295956280469 118252292941841997950647)
  ·
    refine ⟨177378439412762996925971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118252292941841997950647 177378439412762996925971)
    ·
      refine ⟨266067659119144495388957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177378439412762996925971 266067659119144495388957)
      ·
        refine ⟨99775372169679185770859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266067659119144495388957 99775372169679185770859)
        ·
          refine ⟨149663058254518778656289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99775372169679185770859 149663058254518778656289)
          ·
            refine ⟨112247293690889083992217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149663058254518778656289 112247293690889083992217)
            ·
              refine ⟨84185470268166812994163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112247293690889083992217 84185470268166812994163)
              ·
                refine ⟨126278205402250219491245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84185470268166812994163 126278205402250219491245)
                ·
                  refine ⟨47354327025843832309217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126278205402250219491245 47354327025843832309217)
                  ·
                    rfl

theorem cell20_103750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_103750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103750 prefixEnd_103750 := by exact prefixLift 103750
  have htrace : WordTrace (prefixWord ++ tailWord_103750) baseStart_103750 baseEnd_103750 := by
    simpa [prefixWord, tailWord_103750, baseEnd_103750] using wordTrace_append hprefix tailTrace_103750
  have hstable : (prefixWord ++ tailWord_103750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103750).length < 2 ^ (prefixWord ++ tailWord_103750).sum := by decide
  have hdescent : baseEnd_103750 < baseStart_103750 := by decide
  rcases family_descends (prefixWord ++ tailWord_103750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103803 : List Nat := [1, 1, 1, 1, 1, 6, 3, 4, 2]
def baseStart_103803 : Nat := 118140960795 + 103803 * 2 ^ 59
def prefixEnd_103803 : Nat := 4983230072969 + 3 ^ 40 * 103803 * 2
def baseEnd_103803 : Nat := 47378517670011203542333

theorem tailTrace_103803 : CollatzResearch.WordTrace tailWord_103803 prefixEnd_103803 47378517670011203542333 := by
  unfold tailWord_103803
  simp only [CollatzResearch.WordTrace]
  refine ⟨3786006442946933986100063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2524004295297955990733375 3786006442946933986100063)
  ·
    refine ⟨5679009664420400979150095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3786006442946933986100063 5679009664420400979150095)
    ·
      refine ⟨8518514496630601468725143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5679009664420400979150095 8518514496630601468725143)
      ·
        refine ⟨12777771744945902203087715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8518514496630601468725143 12777771744945902203087715)
        ·
          refine ⟨19166657617418853304631573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12777771744945902203087715 19166657617418853304631573)
          ·
            refine ⟨898437075816508748654605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19166657617418853304631573 898437075816508748654605)
            ·
              refine ⟨336913903431190780745477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 898437075816508748654605 336913903431190780745477)
              ·
                refine ⟨63171356893348271389777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 336913903431190780745477 63171356893348271389777)
                ·
                  refine ⟨47378517670011203542333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63171356893348271389777 47378517670011203542333)
                  ·
                    rfl

theorem cell20_103803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 2].length) (baseStart_103803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103803 prefixEnd_103803 := by exact prefixLift 103803
  have htrace : WordTrace (prefixWord ++ tailWord_103803) baseStart_103803 baseEnd_103803 := by
    simpa [prefixWord, tailWord_103803, baseEnd_103803] using wordTrace_append hprefix tailTrace_103803
  have hstable : (prefixWord ++ tailWord_103803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103803).length < 2 ^ (prefixWord ++ tailWord_103803).sum := by decide
  have hdescent : baseEnd_103803 < baseStart_103803 := by decide
  rcases family_descends (prefixWord ++ tailWord_103803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103869 : List Nat := [1, 4, 1, 2, 2, 1, 2, 7]
def baseStart_103869 : Nat := 118140960795 + 103869 * 2 ^ 59
def prefixEnd_103869 : Nat := 4983230072969 + 3 ^ 40 * 103869 * 2
def baseEnd_103869 : Nat := 15802880622802769114021

theorem tailTrace_103869 : CollatzResearch.WordTrace tailWord_103869 prefixEnd_103869 15802880622802769114021 := by
  unfold tailWord_103869
  simp only [CollatzResearch.WordTrace]
  refine ⟨3788413660707827258002661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2525609107138551505335107 3788413660707827258002661)
  ·
    refine ⟨710327561382717610875499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3788413660707827258002661 710327561382717610875499)
    ·
      refine ⟨1065491342074076416313249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 710327561382717610875499 1065491342074076416313249)
      ·
        refine ⟨799118506555557312234937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1065491342074076416313249 799118506555557312234937)
        ·
          refine ⟨599338879916667984176203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 799118506555557312234937 599338879916667984176203)
          ·
            refine ⟨899008319875001976264305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599338879916667984176203 899008319875001976264305)
            ·
              refine ⟨674256239906251482198229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899008319875001976264305 674256239906251482198229)
              ·
                refine ⟨15802880622802769114021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 674256239906251482198229 15802880622802769114021)
                ·
                  rfl

theorem cell20_103869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 7].length) (baseStart_103869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103869 prefixEnd_103869 := by exact prefixLift 103869
  have htrace : WordTrace (prefixWord ++ tailWord_103869) baseStart_103869 baseEnd_103869 := by
    simpa [prefixWord, tailWord_103869, baseEnd_103869] using wordTrace_append hprefix tailTrace_103869
  have hstable : (prefixWord ++ tailWord_103869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103869).length < 2 ^ (prefixWord ++ tailWord_103869).sum := by decide
  have hdescent : baseEnd_103869 < baseStart_103869 := by decide
  rcases family_descends (prefixWord ++ tailWord_103869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103886 : List Nat := [4, 1, 1, 1, 2, 1, 6, 4]
def baseStart_103886 : Nat := 118140960795 + 103886 * 2 ^ 59
def prefixEnd_103886 : Nat := 4983230072969 + 3 ^ 40 * 103886 * 2
def baseEnd_103886 : Nat := 15805467043877267925109

theorem tailTrace_103886 : CollatzResearch.WordTrace tailWord_103886 prefixEnd_103886 15805467043877267925109 := by
  unfold tailWord_103886
  simp only [CollatzResearch.WordTrace]
  refine ⟨473629212705779895171439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2526022467764159440914341 473629212705779895171439)
  ·
    refine ⟨710443819058669842757159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 473629212705779895171439 710443819058669842757159)
    ·
      refine ⟨1065665728588004764135739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 710443819058669842757159 1065665728588004764135739)
      ·
        refine ⟨1598498592882007146203609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1065665728588004764135739 1598498592882007146203609)
        ·
          refine ⟨1198873944661505359652707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1598498592882007146203609 1198873944661505359652707)
          ·
            refine ⟨1798310916992258039479061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198873944661505359652707 1798310916992258039479061)
            ·
              refine ⟨84295824234012095600581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1798310916992258039479061 84295824234012095600581)
              ·
                refine ⟨15805467043877267925109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84295824234012095600581 15805467043877267925109)
                ·
                  rfl

theorem cell20_103886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_103886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103886 prefixEnd_103886 := by exact prefixLift 103886
  have htrace : WordTrace (prefixWord ++ tailWord_103886) baseStart_103886 baseEnd_103886 := by
    simpa [prefixWord, tailWord_103886, baseEnd_103886] using wordTrace_append hprefix tailTrace_103886
  have hstable : (prefixWord ++ tailWord_103886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103886).length < 2 ^ (prefixWord ++ tailWord_103886).sum := by decide
  have hdescent : baseEnd_103886 < baseStart_103886 := by decide
  rcases family_descends (prefixWord ++ tailWord_103886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103892 : List Nat := [2, 4, 1, 2, 4, 1, 1, 3, 2]
def baseStart_103892 : Nat := 118140960795 + 103892 * 2 ^ 59
def prefixEnd_103892 : Nat := 4983230072969 + 3 ^ 40 * 103892 * 2
def baseEnd_103892 : Nat := 47419139695122449575303

theorem tailTrace_103892 : CollatzResearch.WordTrace tailWord_103892 prefixEnd_103892 47419139695122449575303 := by
  unfold tailWord_103892
  simp only [CollatzResearch.WordTrace]
  refine ⟨1894626269812251093044965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2526168359749668124059953 1894626269812251093044965)
  ·
    refine ⟨355242425589797079945931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1894626269812251093044965 355242425589797079945931)
    ·
      refine ⟨532863638384695619918897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355242425589797079945931 532863638384695619918897)
      ·
        refine ⟨399647728788521714939173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 532863638384695619918897 399647728788521714939173)
        ·
          refine ⟨74933949147847821551095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 399647728788521714939173 74933949147847821551095)
          ·
            refine ⟨112400923721771732326643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74933949147847821551095 112400923721771732326643)
            ·
              refine ⟨168601385582657598489965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112400923721771732326643 168601385582657598489965)
              ·
                refine ⟨63225519593496599433737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168601385582657598489965 63225519593496599433737)
                ·
                  refine ⟨47419139695122449575303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63225519593496599433737 47419139695122449575303)
                  ·
                    rfl

theorem cell20_103892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_103892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103892 prefixEnd_103892 := by exact prefixLift 103892
  have htrace : WordTrace (prefixWord ++ tailWord_103892) baseStart_103892 baseEnd_103892 := by
    simpa [prefixWord, tailWord_103892, baseEnd_103892] using wordTrace_append hprefix tailTrace_103892
  have hstable : (prefixWord ++ tailWord_103892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103892).length < 2 ^ (prefixWord ++ tailWord_103892).sum := by decide
  have hdescent : baseEnd_103892 < baseStart_103892 := by decide
  rcases family_descends (prefixWord ++ tailWord_103892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103907 : List Nat := [1, 1, 1, 6, 2, 1, 8]
def baseStart_103907 : Nat := 118140960795 + 103907 * 2 ^ 59
def prefixEnd_103907 : Nat := 4983230072969 + 3 ^ 40 * 103907 * 2
def baseEnd_103907 : Nat := 5269554011538784897249

theorem tailTrace_103907 : CollatzResearch.WordTrace tailWord_103907 prefixEnd_103907 5269554011538784897249 := by
  unfold tailWord_103907
  simp only [CollatzResearch.WordTrace]
  refine ⟨3789799634570159747885975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2526533089713439831923983 3789799634570159747885975)
  ·
    refine ⟨5684699451855239621828963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3789799634570159747885975 5684699451855239621828963)
    ·
      refine ⟨8527049177782859432743445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5684699451855239621828963 8527049177782859432743445)
      ·
        refine ⟨399705430208571535909849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8527049177782859432743445 399705430208571535909849)
        ·
          refine ⟨299779072656428651932387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399705430208571535909849 299779072656428651932387)
          ·
            refine ⟨449668608984642977898581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299779072656428651932387 449668608984642977898581)
            ·
              refine ⟨5269554011538784897249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 449668608984642977898581 5269554011538784897249)
              ·
                rfl

theorem cell20_103907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 8].length) (baseStart_103907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103907 prefixEnd_103907 := by exact prefixLift 103907
  have htrace : WordTrace (prefixWord ++ tailWord_103907) baseStart_103907 baseEnd_103907 := by
    simpa [prefixWord, tailWord_103907, baseEnd_103907] using wordTrace_append hprefix tailTrace_103907
  have hstable : (prefixWord ++ tailWord_103907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103907).length < 2 ^ (prefixWord ++ tailWord_103907).sum := by decide
  have hdescent : baseEnd_103907 < baseStart_103907 := by decide
  rcases family_descends (prefixWord ++ tailWord_103907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103969 : List Nat := [1, 2, 3, 2, 2, 2, 1, 4, 3]
def baseStart_103969 : Nat := 118140960795 + 103969 * 2 ^ 59
def prefixEnd_103969 : Nat := 4983230072969 + 3 ^ 40 * 103969 * 2
def baseEnd_103969 : Nat := 47454284593252404008321

theorem tailTrace_103969 : CollatzResearch.WordTrace tailWord_103969 prefixEnd_103969 47454284593252404008321 := by
  unfold tailWord_103969
  simp only [CollatzResearch.WordTrace]
  refine ⟨3792060960345544336642961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2528040640230362891095307 3792060960345544336642961)
  ·
    refine ⟨2844045720259158252482221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3792060960345544336642961 2844045720259158252482221)
    ·
      refine ⟨1066517145097184344680833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2844045720259158252482221 1066517145097184344680833)
      ·
        refine ⟨799887858822888258510625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1066517145097184344680833 799887858822888258510625)
        ·
          refine ⟨599915894117166193882969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 799887858822888258510625 599915894117166193882969)
          ·
            refine ⟨449936920587874645412227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599915894117166193882969 449936920587874645412227)
            ·
              refine ⟨674905380881811968118341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449936920587874645412227 674905380881811968118341)
              ·
                refine ⟨126544758915339744022189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 674905380881811968118341 126544758915339744022189)
                ·
                  refine ⟨47454284593252404008321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126544758915339744022189 47454284593252404008321)
                  ·
                    rfl

theorem cell20_103969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_103969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_103969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_103969 prefixEnd_103969 := by exact prefixLift 103969
  have htrace : WordTrace (prefixWord ++ tailWord_103969) baseStart_103969 baseEnd_103969 := by
    simpa [prefixWord, tailWord_103969, baseEnd_103969] using wordTrace_append hprefix tailTrace_103969
  have hstable : (prefixWord ++ tailWord_103969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103969).length < 2 ^ (prefixWord ++ tailWord_103969).sum := by decide
  have hdescent : baseEnd_103969 < baseStart_103969 := by decide
  rcases family_descends (prefixWord ++ tailWord_103969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104006 : List Nat := [6, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_104006 : Nat := 118140960795 + 104006 * 2 ^ 59
def prefixEnd_104006 : Nat := 4983230072969 + 3 ^ 40 * 104006 * 2
def baseEnd_104006 : Nat := 47471172401444719774837

theorem tailTrace_104006 : CollatzResearch.WordTrace tailWord_104006 prefixEnd_104006 47471172401444719774837 := by
  unfold tailWord_104006
  simp only [CollatzResearch.WordTrace]
  refine ⟨118544076912859364241871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2528940307474333103826581 118544076912859364241871)
  ·
    refine ⟨177816115369289046362807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118544076912859364241871 177816115369289046362807)
    ·
      refine ⟨266724173053933569544211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177816115369289046362807 266724173053933569544211)
      ·
        refine ⟨400086259580900354316317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266724173053933569544211 400086259580900354316317)
        ·
          refine ⟨150032347342837632868619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400086259580900354316317 150032347342837632868619)
          ·
            refine ⟨225048521014256449302929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150032347342837632868619 225048521014256449302929)
            ·
              refine ⟨168786390760692336977197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225048521014256449302929 168786390760692336977197)
              ·
                refine ⟨63294896535259626366449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168786390760692336977197 63294896535259626366449)
                ·
                  refine ⟨47471172401444719774837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63294896535259626366449 47471172401444719774837)
                  ·
                    rfl

theorem cell20_104006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_104006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104006 prefixEnd_104006 := by exact prefixLift 104006
  have htrace : WordTrace (prefixWord ++ tailWord_104006) baseStart_104006 baseEnd_104006 := by
    simpa [prefixWord, tailWord_104006, baseEnd_104006] using wordTrace_append hprefix tailTrace_104006
  have hstable : (prefixWord ++ tailWord_104006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104006).length < 2 ^ (prefixWord ++ tailWord_104006).sum := by decide
  have hdescent : baseEnd_104006 < baseStart_104006 := by decide
  rcases family_descends (prefixWord ++ tailWord_104006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104073 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 6]
def baseStart_104073 : Nat := 118140960795 + 104073 * 2 ^ 59
def prefixEnd_104073 : Nat := 4983230072969 + 3 ^ 40 * 104073 * 2
def baseEnd_104073 : Nat := 47501753027090264541229

theorem tailTrace_104073 : CollatzResearch.WordTrace tailWord_104073 prefixEnd_104073 47501753027090264541229 := by
  unfold tailWord_104073
  simp only [CollatzResearch.WordTrace]
  refine ⟨3795854151968770098428873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2530569434645846732285915 3795854151968770098428873)
  ·
    refine ⟨2846890613976577573821655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3795854151968770098428873 2846890613976577573821655)
    ·
      refine ⟨4270335920964866360732483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2846890613976577573821655 4270335920964866360732483)
      ·
        refine ⟨6405503881447299541098725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4270335920964866360732483 6405503881447299541098725)
        ·
          refine ⟨1201031977771368663956011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6405503881447299541098725 1201031977771368663956011)
          ·
            refine ⟨1801547966657052995934017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201031977771368663956011 1801547966657052995934017)
            ·
              refine ⟨1351160974992789746950513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1801547966657052995934017 1351160974992789746950513)
              ·
                refine ⟨1013370731244592310212885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1351160974992789746950513 1013370731244592310212885)
                ·
                  refine ⟨47501753027090264541229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1013370731244592310212885 47501753027090264541229)
                  ·
                    rfl

theorem cell20_104073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_104073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104073 prefixEnd_104073 := by exact prefixLift 104073
  have htrace : WordTrace (prefixWord ++ tailWord_104073) baseStart_104073 baseEnd_104073 := by
    simpa [prefixWord, tailWord_104073, baseEnd_104073] using wordTrace_append hprefix tailTrace_104073
  have hstable : (prefixWord ++ tailWord_104073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104073).length < 2 ^ (prefixWord ++ tailWord_104073).sum := by decide
  have hdescent : baseEnd_104073 < baseStart_104073 := by decide
  rcases family_descends (prefixWord ++ tailWord_104073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104097 : List Nat := [1, 2, 3, 3, 2, 1, 1, 7]
def baseStart_104097 : Nat := 118140960795 + 104097 * 2 ^ 59
def prefixEnd_104097 : Nat := 4983230072969 + 3 ^ 40 * 104097 * 2
def baseEnd_104097 : Nat := 15837569093684282580377

theorem tailTrace_104097 : CollatzResearch.WordTrace tailWord_104097 prefixEnd_104097 15837569093684282580377 := by
  unfold tailWord_104097
  simp only [CollatzResearch.WordTrace]
  refine ⟨3796729503881822197302545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2531153002587881464868363 3796729503881822197302545)
  ·
    refine ⟨2847547127911366647976909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3796729503881822197302545 2847547127911366647976909)
    ·
      refine ⟨1067830172966762492991341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2847547127911366647976909 1067830172966762492991341)
      ·
        refine ⟨400436314862535934871753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1067830172966762492991341 400436314862535934871753)
        ·
          refine ⟨300327236146901951153815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400436314862535934871753 300327236146901951153815)
          ·
            refine ⟨450490854220352926730723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300327236146901951153815 450490854220352926730723)
            ·
              refine ⟨675736281330529390096085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450490854220352926730723 675736281330529390096085)
              ·
                refine ⟨15837569093684282580377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 675736281330529390096085 15837569093684282580377)
                ·
                  rfl

theorem cell20_104097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 7].length) (baseStart_104097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104097 prefixEnd_104097 := by exact prefixLift 104097
  have htrace : WordTrace (prefixWord ++ tailWord_104097) baseStart_104097 baseEnd_104097 := by
    simpa [prefixWord, tailWord_104097, baseEnd_104097] using wordTrace_append hprefix tailTrace_104097
  have hstable : (prefixWord ++ tailWord_104097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104097).length < 2 ^ (prefixWord ++ tailWord_104097).sum := by decide
  have hdescent : baseEnd_104097 < baseStart_104097 := by decide
  rcases family_descends (prefixWord ++ tailWord_104097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104100 : List Nat := [2, 3, 1, 2, 2, 2, 4, 1, 3]
def baseStart_104100 : Nat := 118140960795 + 104100 * 2 ^ 59
def prefixEnd_104100 : Nat := 4983230072969 + 3 ^ 40 * 104100 * 2
def baseEnd_104100 : Nat := 47514076562798170641119

theorem tailTrace_104100 : CollatzResearch.WordTrace tailWord_104100 prefixEnd_104100 47514076562798170641119 := by
  unfold tailWord_104100
  simp only [CollatzResearch.WordTrace]
  refine ⟨1898419461435476854830877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2531225948580635806441169 1898419461435476854830877)
  ·
    refine ⟨711907298038303820561579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1898419461435476854830877 711907298038303820561579)
    ·
      refine ⟨1067860947057455730842369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 711907298038303820561579 1067860947057455730842369)
      ·
        refine ⟨800895710293091798131777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1067860947057455730842369 800895710293091798131777)
        ·
          refine ⟨600671782719818848598833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 800895710293091798131777 600671782719818848598833)
          ·
            refine ⟨450503837039864136449125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600671782719818848598833 450503837039864136449125)
            ·
              refine ⟨84469469444974525584211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 450503837039864136449125 84469469444974525584211)
              ·
                refine ⟨126704204167461788376317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84469469444974525584211 126704204167461788376317)
                ·
                  refine ⟨47514076562798170641119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126704204167461788376317 47514076562798170641119)
                  ·
                    rfl

theorem cell20_104100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_104100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104100 prefixEnd_104100 := by exact prefixLift 104100
  have htrace : WordTrace (prefixWord ++ tailWord_104100) baseStart_104100 baseEnd_104100 := by
    simpa [prefixWord, tailWord_104100, baseEnd_104100] using wordTrace_append hprefix tailTrace_104100
  have hstable : (prefixWord ++ tailWord_104100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104100).length < 2 ^ (prefixWord ++ tailWord_104100).sum := by decide
  have hdescent : baseEnd_104100 < baseStart_104100 := by decide
  rcases family_descends (prefixWord ++ tailWord_104100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104111 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 6]
def baseStart_104111 : Nat := 118140960795 + 104111 * 2 ^ 59
def prefixEnd_104111 : Nat := 4983230072969 + 3 ^ 40 * 104111 * 2
def baseEnd_104111 : Nat := 47519097262531021274407

theorem tailTrace_104111 : CollatzResearch.WordTrace tailWord_104111 prefixEnd_104111 47519097262531021274407 := by
  unfold tailWord_104111
  simp only [CollatzResearch.WordTrace]
  refine ⟨3797240125831102588312187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2531493417220735058874791 3797240125831102588312187)
  ·
    refine ⟨5695860188746653882468281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3797240125831102588312187 5695860188746653882468281)
    ·
      refine ⟨4271895141559990411851211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5695860188746653882468281 4271895141559990411851211)
      ·
        refine ⟨6407842712339985617776817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4271895141559990411851211 6407842712339985617776817)
        ·
          refine ⟨4805882034254989213332613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6407842712339985617776817 4805882034254989213332613)
          ·
            refine ⟨901102881422810477499865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4805882034254989213332613 901102881422810477499865)
            ·
              refine ⟨675827161067107858124899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 901102881422810477499865 675827161067107858124899)
              ·
                refine ⟨1013740741600661787187349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675827161067107858124899 1013740741600661787187349)
                ·
                  refine ⟨47519097262531021274407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1013740741600661787187349 47519097262531021274407)
                  ·
                    rfl

theorem cell20_104111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_104111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104111 prefixEnd_104111 := by exact prefixLift 104111
  have htrace : WordTrace (prefixWord ++ tailWord_104111) baseStart_104111 baseEnd_104111 := by
    simpa [prefixWord, tailWord_104111, baseEnd_104111] using wordTrace_append hprefix tailTrace_104111
  have hstable : (prefixWord ++ tailWord_104111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104111).length < 2 ^ (prefixWord ++ tailWord_104111).sum := by decide
  have hdescent : baseEnd_104111 < baseStart_104111 := by decide
  rcases family_descends (prefixWord ++ tailWord_104111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104134 : List Nat := [6, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_104134 : Nat := 118140960795 + 104134 * 2 ^ 59
def prefixEnd_104134 : Nat := 4983230072969 + 3 ^ 40 * 104134 * 2
def baseEnd_104134 : Nat := 47529595089245163507647

theorem tailTrace_104134 : CollatzResearch.WordTrace tailWord_104134 prefixEnd_104134 47529595089245163507647 := by
  unfold tailWord_104134
  simp only [CollatzResearch.WordTrace]
  refine ⟨118689968898368047387483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2532052669831851677599637 118689968898368047387483)
  ·
    refine ⟨178034953347552071081225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118689968898368047387483 178034953347552071081225)
    ·
      refine ⟨133526215010664053310919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178034953347552071081225 133526215010664053310919)
      ·
        refine ⟨200289322515996079966379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133526215010664053310919 200289322515996079966379)
        ·
          refine ⟨300433983773994119949569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200289322515996079966379 300433983773994119949569)
          ·
            refine ⟨225325487830495589962177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300433983773994119949569 225325487830495589962177)
            ·
              refine ⟨168994115872871692471633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225325487830495589962177 168994115872871692471633)
              ·
                refine ⟨126745586904653769353725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168994115872871692471633 126745586904653769353725)
                ·
                  refine ⟨47529595089245163507647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126745586904653769353725 47529595089245163507647)
                  ·
                    rfl

theorem cell20_104134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_104134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104134 prefixEnd_104134 := by exact prefixLift 104134
  have htrace : WordTrace (prefixWord ++ tailWord_104134) baseStart_104134 baseEnd_104134 := by
    simpa [prefixWord, tailWord_104134, baseEnd_104134] using wordTrace_append hprefix tailTrace_104134
  have hstable : (prefixWord ++ tailWord_104134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104134).length < 2 ^ (prefixWord ++ tailWord_104134).sum := by decide
  have hdescent : baseEnd_104134 < baseStart_104134 := by decide
  rcases family_descends (prefixWord ++ tailWord_104134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104138 : List Nat := [3, 1, 2, 1, 5, 1, 2, 2, 3]
def baseStart_104138 : Nat := 118140960795 + 104138 * 2 ^ 59
def prefixEnd_104138 : Nat := 4983230072969 + 3 ^ 40 * 104138 * 2
def baseEnd_104138 : Nat := 47531420798238927374297

theorem tailTrace_104138 : CollatzResearch.WordTrace tailWord_104138 prefixEnd_104138 47531420798238927374297 := by
  unfold tailWord_104138
  simp only [CollatzResearch.WordTrace]
  refine ⟨949556224183321549886267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2532149931155524133030045 949556224183321549886267)
  ·
    refine ⟨1424334336274982324829401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 949556224183321549886267 1424334336274982324829401)
    ·
      refine ⟨1068250752206236743622051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1424334336274982324829401 1068250752206236743622051)
      ·
        refine ⟨1602376128309355115433077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1068250752206236743622051 1602376128309355115433077)
        ·
          refine ⟨150222762029002042071851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1602376128309355115433077 150222762029002042071851)
          ·
            refine ⟨225334143043503063107777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150222762029002042071851 225334143043503063107777)
            ·
              refine ⟨169000607282627297330833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225334143043503063107777 169000607282627297330833)
              ·
                refine ⟨126750455461970472998125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169000607282627297330833 126750455461970472998125)
                ·
                  refine ⟨47531420798238927374297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126750455461970472998125 47531420798238927374297)
                  ·
                    rfl

theorem cell20_104138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_104138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104138 prefixEnd_104138 := by exact prefixLift 104138
  have htrace : WordTrace (prefixWord ++ tailWord_104138) baseStart_104138 baseEnd_104138 := by
    simpa [prefixWord, tailWord_104138, baseEnd_104138] using wordTrace_append hprefix tailTrace_104138
  have hstable : (prefixWord ++ tailWord_104138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104138).length < 2 ^ (prefixWord ++ tailWord_104138).sum := by decide
  have hdescent : baseEnd_104138 < baseStart_104138 := by decide
  rcases family_descends (prefixWord ++ tailWord_104138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104141 : List Nat := [1, 6, 2, 1, 1, 2, 1, 4, 2]
def baseStart_104141 : Nat := 118140960795 + 104141 * 2 ^ 59
def prefixEnd_104141 : Nat := 4983230072969 + 3 ^ 40 * 104141 * 2
def baseEnd_104141 : Nat := 47532790079984250274285

theorem tailTrace_104141 : CollatzResearch.WordTrace tailWord_104141 prefixEnd_104141 47532790079984250274285 := by
  unfold tailWord_104141
  simp only [CollatzResearch.WordTrace]
  refine ⟨3798334315722417711904277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2532222877148278474602851 3798334315722417711904277)
  ·
    refine ⟨178046921049488330245513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3798334315722417711904277 178046921049488330245513)
    ·
      refine ⟨133535190787116247684135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178046921049488330245513 133535190787116247684135)
      ·
        refine ⟨200302786180674371526203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133535190787116247684135 200302786180674371526203)
        ·
          refine ⟨300454179271011557289305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200302786180674371526203 300454179271011557289305)
          ·
            refine ⟨225340634453258667966979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300454179271011557289305 225340634453258667966979)
            ·
              refine ⟨338010951679888001950469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225340634453258667966979 338010951679888001950469)
              ·
                refine ⟨63377053439979000365713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 338010951679888001950469 63377053439979000365713)
                ·
                  refine ⟨47532790079984250274285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63377053439979000365713 47532790079984250274285)
                  ·
                    rfl

theorem cell20_104141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_104141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104141 prefixEnd_104141 := by exact prefixLift 104141
  have htrace : WordTrace (prefixWord ++ tailWord_104141) baseStart_104141 baseEnd_104141 := by
    simpa [prefixWord, tailWord_104141, baseEnd_104141] using wordTrace_append hprefix tailTrace_104141
  have hstable : (prefixWord ++ tailWord_104141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104141).length < 2 ^ (prefixWord ++ tailWord_104141).sum := by decide
  have hdescent : baseEnd_104141 < baseStart_104141 := by decide
  rcases family_descends (prefixWord ++ tailWord_104141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104145 : List Nat := [1, 2, 2, 1, 2, 5, 1, 4, 2]
def baseStart_104145 : Nat := 118140960795 + 104145 * 2 ^ 59
def prefixEnd_104145 : Nat := 4983230072969 + 3 ^ 40 * 104145 * 2
def baseEnd_104145 : Nat := 47534615788978014140935

theorem tailTrace_104145 : CollatzResearch.WordTrace tailWord_104145 prefixEnd_104145 47534615788978014140935 := by
  unfold tailWord_104145
  simp only [CollatzResearch.WordTrace]
  refine ⟨3798480207707926395049889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2532320138471950930033259 3798480207707926395049889)
  ·
    refine ⟨2848860155780944796287417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3798480207707926395049889 2848860155780944796287417)
    ·
      refine ⟨2136645116835708597215563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2848860155780944796287417 2136645116835708597215563)
      ·
        refine ⟨3204967675253562895823345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2136645116835708597215563 3204967675253562895823345)
        ·
          refine ⟨2403725756440172171867509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3204967675253562895823345 2403725756440172171867509)
          ·
            refine ⟨225349289666266141112579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2403725756440172171867509 225349289666266141112579)
            ·
              refine ⟨338023934499399211668869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225349289666266141112579 338023934499399211668869)
              ·
                refine ⟨63379487718637352187913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 338023934499399211668869 63379487718637352187913)
                ·
                  refine ⟨47534615788978014140935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63379487718637352187913 47534615788978014140935)
                  ·
                    rfl

theorem cell20_104145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 2].length) (baseStart_104145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104145 prefixEnd_104145 := by exact prefixLift 104145
  have htrace : WordTrace (prefixWord ++ tailWord_104145) baseStart_104145 baseEnd_104145 := by
    simpa [prefixWord, tailWord_104145, baseEnd_104145] using wordTrace_append hprefix tailTrace_104145
  have hstable : (prefixWord ++ tailWord_104145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104145).length < 2 ^ (prefixWord ++ tailWord_104145).sum := by decide
  have hdescent : baseEnd_104145 < baseStart_104145 := by decide
  rcases family_descends (prefixWord ++ tailWord_104145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104190 : List Nat := [4, 2, 2, 1, 3, 1, 7]
def baseStart_104190 : Nat := 118140960795 + 104190 * 2 ^ 59
def prefixEnd_104190 : Nat := 4983230072969 + 3 ^ 40 * 104190 * 2
def baseEnd_104190 : Nat := 5283906112795317515639

theorem tailTrace_104190 : CollatzResearch.WordTrace tailWord_104190 prefixEnd_104190 5283906112795317515639 := by
  unfold tailWord_104190
  simp only [CollatzResearch.WordTrace]
  refine ⟨475015186568112385054753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2533414328363266053625349 475015186568112385054753)
  ·
    refine ⟨356261389926084288791065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 475015186568112385054753 356261389926084288791065)
    ·
      refine ⟨267196042444563216593299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356261389926084288791065 267196042444563216593299)
      ·
        refine ⟨400794063666844824889949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267196042444563216593299 400794063666844824889949)
        ·
          refine ⟨150297773875066809333731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400794063666844824889949 150297773875066809333731)
          ·
            refine ⟨225446660812600214000597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150297773875066809333731 225446660812600214000597)
            ·
              refine ⟨5283906112795317515639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 225446660812600214000597 5283906112795317515639)
              ·
                rfl

theorem cell20_104190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 7].length) (baseStart_104190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104190 prefixEnd_104190 := by exact prefixLift 104190
  have htrace : WordTrace (prefixWord ++ tailWord_104190) baseStart_104190 baseEnd_104190 := by
    simpa [prefixWord, tailWord_104190, baseEnd_104190] using wordTrace_append hprefix tailTrace_104190
  have hstable : (prefixWord ++ tailWord_104190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104190).length < 2 ^ (prefixWord ++ tailWord_104190).sum := by decide
  have hdescent : baseEnd_104190 < baseStart_104190 := by decide
  rcases family_descends (prefixWord ++ tailWord_104190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104228 : List Nat := [2, 3, 1, 3, 2, 1, 4, 4]
def baseStart_104228 : Nat := 118140960795 + 104228 * 2 ^ 59
def prefixEnd_104228 : Nat := 4983230072969 + 3 ^ 40 * 104228 * 2
def baseEnd_104228 : Nat := 15857499750199538124643

theorem tailTrace_104228 : CollatzResearch.WordTrace tailWord_104228 prefixEnd_104228 15857499750199538124643 := by
  unfold tailWord_104228
  simp only [CollatzResearch.WordTrace]
  refine ⟨1900753733203615785160669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2534338310938154380214225 1900753733203615785160669)
  ·
    refine ⟨712782649951355919435251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1900753733203615785160669 712782649951355919435251)
    ·
      refine ⟨1069173974927033879152877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 712782649951355919435251 1069173974927033879152877)
      ·
        refine ⟨400940240597637704682329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1069173974927033879152877 400940240597637704682329)
        ·
          refine ⟨300705180448228278511747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400940240597637704682329 300705180448228278511747)
          ·
            refine ⟨451057770672342417767621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300705180448228278511747 451057770672342417767621)
            ·
              refine ⟨84573332001064203331429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 451057770672342417767621 84573332001064203331429)
              ·
                refine ⟨15857499750199538124643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84573332001064203331429 15857499750199538124643)
                ·
                  rfl

theorem cell20_104228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_104228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104228 prefixEnd_104228 := by exact prefixLift 104228
  have htrace : WordTrace (prefixWord ++ tailWord_104228) baseStart_104228 baseEnd_104228 := by
    simpa [prefixWord, tailWord_104228, baseEnd_104228] using wordTrace_append hprefix tailTrace_104228
  have hstable : (prefixWord ++ tailWord_104228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104228).length < 2 ^ (prefixWord ++ tailWord_104228).sum := by decide
  have hdescent : baseEnd_104228 < baseStart_104228 := by decide
  rcases family_descends (prefixWord ++ tailWord_104228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104269 : List Nat := [1, 6, 1, 2, 1, 1, 4, 1, 3]
def baseStart_104269 : Nat := 118140960795 + 104269 * 2 ^ 59
def prefixEnd_104269 : Nat := 4983230072969 + 3 ^ 40 * 104269 * 2
def baseEnd_104269 : Nat := 47591212767784694007095

theorem tailTrace_104269 : CollatzResearch.WordTrace tailWord_104269 prefixEnd_104269 47591212767784694007095 := by
  unfold tailWord_104269
  simp only [CollatzResearch.WordTrace]
  refine ⟨3803002859258695572563861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2535335239505797048375907 3803002859258695572563861)
  ·
    refine ⟨178265759027751354963931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3803002859258695572563861 178265759027751354963931)
    ·
      refine ⟨267398638541627032445897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178265759027751354963931 267398638541627032445897)
      ·
        refine ⟨200548978906220274334423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267398638541627032445897 200548978906220274334423)
        ·
          refine ⟨300823468359330411501635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200548978906220274334423 300823468359330411501635)
          ·
            refine ⟨451235202538995617252453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300823468359330411501635 451235202538995617252453)
            ·
              refine ⟨84606600476061678234835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 451235202538995617252453 84606600476061678234835)
              ·
                refine ⟨126909900714092517352253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84606600476061678234835 126909900714092517352253)
                ·
                  refine ⟨47591212767784694007095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126909900714092517352253 47591212767784694007095)
                  ·
                    rfl

theorem cell20_104269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_104269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104269 prefixEnd_104269 := by exact prefixLift 104269
  have htrace : WordTrace (prefixWord ++ tailWord_104269) baseStart_104269 baseEnd_104269 := by
    simpa [prefixWord, tailWord_104269, baseEnd_104269] using wordTrace_append hprefix tailTrace_104269
  have hstable : (prefixWord ++ tailWord_104269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104269).length < 2 ^ (prefixWord ++ tailWord_104269).sum := by decide
  have hdescent : baseEnd_104269 < baseStart_104269 := by decide
  rcases family_descends (prefixWord ++ tailWord_104269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104273 : List Nat := [1, 2, 2, 1, 5, 2, 1, 3, 3]
def baseStart_104273 : Nat := 118140960795 + 104273 * 2 ^ 59
def prefixEnd_104273 : Nat := 4983230072969 + 3 ^ 40 * 104273 * 2
def baseEnd_104273 : Nat := 47593038476778457873745

theorem tailTrace_104273 : CollatzResearch.WordTrace tailWord_104273 prefixEnd_104273 47593038476778457873745 := by
  unfold tailWord_104273
  simp only [CollatzResearch.WordTrace]
  refine ⟨3803148751244204255709473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2535432500829469503806315 3803148751244204255709473)
  ·
    refine ⟨2852361563433153191782105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3803148751244204255709473 2852361563433153191782105)
    ·
      refine ⟨2139271172574864893836579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2852361563433153191782105 2139271172574864893836579)
      ·
        refine ⟨3208906758862297340754869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2139271172574864893836579 3208906758862297340754869)
        ·
          refine ⟨300835008643340375695769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3208906758862297340754869 300835008643340375695769)
          ·
            refine ⟨225626256482505281771827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300835008643340375695769 225626256482505281771827)
            ·
              refine ⟨338439384723757922657741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225626256482505281771827 338439384723757922657741)
              ·
                refine ⟨126914769271409220996653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338439384723757922657741 126914769271409220996653)
                ·
                  refine ⟨47593038476778457873745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126914769271409220996653 47593038476778457873745)
                  ·
                    rfl

theorem cell20_104273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_104273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104273 prefixEnd_104273 := by exact prefixLift 104273
  have htrace : WordTrace (prefixWord ++ tailWord_104273) baseStart_104273 baseEnd_104273 := by
    simpa [prefixWord, tailWord_104273, baseEnd_104273] using wordTrace_append hprefix tailTrace_104273
  have hstable : (prefixWord ++ tailWord_104273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104273).length < 2 ^ (prefixWord ++ tailWord_104273).sum := by decide
  have hdescent : baseEnd_104273 < baseStart_104273 := by decide
  rcases family_descends (prefixWord ++ tailWord_104273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104310 : List Nat := [5, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_104310 : Nat := 118140960795 + 104310 * 2 ^ 59
def prefixEnd_104310 : Nat := 4983230072969 + 3 ^ 40 * 104310 * 2
def baseEnd_104310 : Nat := 47609926284970773640261

theorem tailTrace_104310 : CollatzResearch.WordTrace tailWord_104310 prefixEnd_104310 47609926284970773640261 := by
  unfold tailWord_104310
  simp only [CollatzResearch.WordTrace]
  refine ⟨237781140756884973425399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2536332168073439716537589 237781140756884973425399)
  ·
    refine ⟨356671711135327460138099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237781140756884973425399 356671711135327460138099)
    ·
      refine ⟨535007566702991190207149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356671711135327460138099 535007566702991190207149)
      ·
        refine ⟨200627837513621696327681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 535007566702991190207149 200627837513621696327681)
        ·
          refine ⟨150470878135216272245761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200627837513621696327681 150470878135216272245761)
          ·
            refine ⟨112853158601412204184321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150470878135216272245761 112853158601412204184321)
            ·
              refine ⟨84639868951059153138241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112853158601412204184321 84639868951059153138241)
              ·
                refine ⟨63479901713294364853681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84639868951059153138241 63479901713294364853681)
                ·
                  refine ⟨47609926284970773640261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63479901713294364853681 47609926284970773640261)
                  ·
                    rfl

theorem cell20_104310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_104310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104310 prefixEnd_104310 := by exact prefixLift 104310
  have htrace : WordTrace (prefixWord ++ tailWord_104310) baseStart_104310 baseEnd_104310 := by
    simpa [prefixWord, tailWord_104310, baseEnd_104310] using wordTrace_append hprefix tailTrace_104310
  have hstable : (prefixWord ++ tailWord_104310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104310).length < 2 ^ (prefixWord ++ tailWord_104310).sum := by decide
  have hdescent : baseEnd_104310 < baseStart_104310 := by decide
  rcases family_descends (prefixWord ++ tailWord_104310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104321 : List Nat := [1, 2, 4, 4, 1, 2, 1, 5]
def baseStart_104321 : Nat := 118140960795 + 104321 * 2 ^ 59
def prefixEnd_104321 : Nat := 4983230072969 + 3 ^ 40 * 104321 * 2
def baseEnd_104321 : Nat := 15871648994901208091183

theorem tailTrace_104321 : CollatzResearch.WordTrace tailWord_104321 prefixEnd_104321 15871648994901208091183 := by
  unfold tailWord_104321
  simp only [CollatzResearch.WordTrace]
  refine ⟨3804899455070308453456817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2536599636713538968971211 3804899455070308453456817)
  ·
    refine ⟨2853674591302731340092613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3804899455070308453456817 2853674591302731340092613)
    ·
      refine ⟨535063985869262126267365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2853674591302731340092613 535063985869262126267365)
      ·
        refine ⟨100324497350486648675131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 535063985869262126267365 100324497350486648675131)
        ·
          refine ⟨150486746025729973012697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100324497350486648675131 150486746025729973012697)
          ·
            refine ⟨112865059519297479759523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150486746025729973012697 112865059519297479759523)
            ·
              refine ⟨169297589278946219639285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112865059519297479759523 169297589278946219639285)
              ·
                refine ⟨15871648994901208091183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169297589278946219639285 15871648994901208091183)
                ·
                  rfl

theorem cell20_104321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 5].length) (baseStart_104321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104321 prefixEnd_104321 := by exact prefixLift 104321
  have htrace : WordTrace (prefixWord ++ tailWord_104321) baseStart_104321 baseEnd_104321 := by
    simpa [prefixWord, tailWord_104321, baseEnd_104321] using wordTrace_append hprefix tailTrace_104321
  have hstable : (prefixWord ++ tailWord_104321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104321).length < 2 ^ (prefixWord ++ tailWord_104321).sum := by decide
  have hdescent : baseEnd_104321 < baseStart_104321 := by decide
  rcases family_descends (prefixWord ++ tailWord_104321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104373 : List Nat := [1, 3, 3, 2, 1, 2, 2, 4, 2]
def baseStart_104373 : Nat := 118140960795 + 104373 * 2 ^ 59
def prefixEnd_104373 : Nat := 4983230072969 + 3 ^ 40 * 104373 * 2
def baseEnd_104373 : Nat := 47638681201622554540003

theorem tailTrace_104373 : CollatzResearch.WordTrace tailWord_104373 prefixEnd_104373 47638681201622554540003 := by
  unfold tailWord_104373
  simp only [CollatzResearch.WordTrace]
  refine ⟨3806796050881921334349773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2537864033921280889566515 3806796050881921334349773)
  ·
    refine ⟨1427548519080720500381165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3806796050881921334349773 1427548519080720500381165)
    ·
      refine ⟨535330694655270187642937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1427548519080720500381165 535330694655270187642937)
      ·
        refine ⟨401498020991452640732203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535330694655270187642937 401498020991452640732203)
        ·
          refine ⟨602247031487178961098305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401498020991452640732203 602247031487178961098305)
          ·
            refine ⟨451685273615384220823729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602247031487178961098305 451685273615384220823729)
            ·
              refine ⟨338763955211538165617797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451685273615384220823729 338763955211538165617797)
              ·
                refine ⟨63518241602163406053337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 338763955211538165617797 63518241602163406053337)
                ·
                  refine ⟨47638681201622554540003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63518241602163406053337 47638681201622554540003)
                  ·
                    rfl

theorem cell20_104373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_104373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104373 prefixEnd_104373 := by exact prefixLift 104373
  have htrace : WordTrace (prefixWord ++ tailWord_104373) baseStart_104373 baseEnd_104373 := by
    simpa [prefixWord, tailWord_104373, baseEnd_104373] using wordTrace_append hprefix tailTrace_104373
  have hstable : (prefixWord ++ tailWord_104373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104373).length < 2 ^ (prefixWord ++ tailWord_104373).sum := by decide
  have hdescent : baseEnd_104373 < baseStart_104373 := by decide
  rcases family_descends (prefixWord ++ tailWord_104373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104384 : List Nat := [2, 1, 1, 2, 3, 2, 2, 7]
def baseStart_104384 : Nat := 118140960795 + 104384 * 2 ^ 59
def prefixEnd_104384 : Nat := 4983230072969 + 3 ^ 40 * 104384 * 2
def baseEnd_104384 : Nat := 15881233967118468391097

theorem tailTrace_104384 : CollatzResearch.WordTrace tailWord_104384 prefixEnd_104384 15881233967118468391097 := by
  unfold tailWord_104384
  simp only [CollatzResearch.WordTrace]
  refine ⟨1903598626921035106500103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2538131502561380142000137 1903598626921035106500103)
  ·
    refine ⟨2855397940381552659750155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1903598626921035106500103 2855397940381552659750155)
    ·
      refine ⟨4283096910572328989625233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2855397940381552659750155 4283096910572328989625233)
      ·
        refine ⟨3212322682929246742218925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4283096910572328989625233 3212322682929246742218925)
        ·
          refine ⟨1204621006098467528332097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3212322682929246742218925 1204621006098467528332097)
          ·
            refine ⟨903465754573850646249073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1204621006098467528332097 903465754573850646249073)
            ·
              refine ⟨677599315930387984686805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 903465754573850646249073 677599315930387984686805)
              ·
                refine ⟨15881233967118468391097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 677599315930387984686805 15881233967118468391097)
                ·
                  rfl

theorem cell20_104384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_104384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104384 prefixEnd_104384 := by exact prefixLift 104384
  have htrace : WordTrace (prefixWord ++ tailWord_104384) baseStart_104384 baseEnd_104384 := by
    simpa [prefixWord, tailWord_104384, baseEnd_104384] using wordTrace_append hprefix tailTrace_104384
  have hstable : (prefixWord ++ tailWord_104384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104384).length < 2 ^ (prefixWord ++ tailWord_104384).sum := by decide
  have hdescent : baseEnd_104384 < baseStart_104384 := by decide
  rcases family_descends (prefixWord ++ tailWord_104384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104432 : List Nat := [2, 1, 1, 1, 3, 2, 2, 6, 2]
def baseStart_104432 : Nat := 118140960795 + 104432 * 2 ^ 59
def prefixEnd_104432 : Nat := 4983230072969 + 3 ^ 40 * 104432 * 2
def baseEnd_104432 : Nat := 47665610409280571573095

theorem tailTrace_104432 : CollatzResearch.WordTrace tailWord_104432 prefixEnd_104432 47665610409280571573095 := by
  unfold tailWord_104432
  simp only [CollatzResearch.WordTrace]
  refine ⟨1904473978834087205373775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2539298638445449607165033 1904473978834087205373775)
  ·
    refine ⟨2856710968251130808060663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1904473978834087205373775 2856710968251130808060663)
    ·
      refine ⟨4285066452376696212090995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2856710968251130808060663 4285066452376696212090995)
      ·
        refine ⟨6427599678565044318136493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4285066452376696212090995 6427599678565044318136493)
        ·
          refine ⟨2410349879461891619301185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6427599678565044318136493 2410349879461891619301185)
          ·
            refine ⟨1807762409596418714475889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2410349879461891619301185 1807762409596418714475889)
            ·
              refine ⟨1355821807197314035856917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1807762409596418714475889 1355821807197314035856917)
              ·
                refine ⟨63554147212374095430793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1355821807197314035856917 63554147212374095430793)
                ·
                  refine ⟨47665610409280571573095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63554147212374095430793 47665610409280571573095)
                  ·
                    rfl

theorem cell20_104432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 2].length) (baseStart_104432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104432 prefixEnd_104432 := by exact prefixLift 104432
  have htrace : WordTrace (prefixWord ++ tailWord_104432) baseStart_104432 baseEnd_104432 := by
    simpa [prefixWord, tailWord_104432, baseEnd_104432] using wordTrace_append hprefix tailTrace_104432
  have hstable : (prefixWord ++ tailWord_104432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104432).length < 2 ^ (prefixWord ++ tailWord_104432).sum := by decide
  have hdescent : baseEnd_104432 < baseStart_104432 := by decide
  rcases family_descends (prefixWord ++ tailWord_104432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104438 : List Nat := [5, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_104438 : Nat := 118140960795 + 104438 * 2 ^ 59
def prefixEnd_104438 : Nat := 4983230072969 + 3 ^ 40 * 104438 * 2
def baseEnd_104438 : Nat := 47668348972771217373071

theorem tailTrace_104438 : CollatzResearch.WordTrace tailWord_104438 prefixEnd_104438 47668348972771217373071 := by
  unfold tailWord_104438
  simp only [CollatzResearch.WordTrace]
  refine ⟨238072924727902339716623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2539444530430958290310645 238072924727902339716623)
  ·
    refine ⟨357109387091853509574935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238072924727902339716623 357109387091853509574935)
    ·
      refine ⟨535664080637780264362403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357109387091853509574935 535664080637780264362403)
      ·
        refine ⟨803496120956670396543605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535664080637780264362403 803496120956670396543605)
        ·
          refine ⟨75327761339687849675963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 803496120956670396543605 75327761339687849675963)
          ·
            refine ⟨112991642009531774513945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75327761339687849675963 112991642009531774513945)
            ·
              refine ⟨84743731507148830885459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112991642009531774513945 84743731507148830885459)
              ·
                refine ⟨127115597260723246328189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84743731507148830885459 127115597260723246328189)
                ·
                  refine ⟨47668348972771217373071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127115597260723246328189 47668348972771217373071)
                  ·
                    rfl

theorem cell20_104438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_104438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104438 prefixEnd_104438 := by exact prefixLift 104438
  have htrace : WordTrace (prefixWord ++ tailWord_104438) baseStart_104438 baseEnd_104438 := by
    simpa [prefixWord, tailWord_104438, baseEnd_104438] using wordTrace_append hprefix tailTrace_104438
  have hstable : (prefixWord ++ tailWord_104438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104438).length < 2 ^ (prefixWord ++ tailWord_104438).sum := by decide
  have hdescent : baseEnd_104438 < baseStart_104438 := by decide
  rcases family_descends (prefixWord ++ tailWord_104438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104460 : List Nat := [2, 2, 1, 2, 3, 1, 1, 8]
def baseStart_104460 : Nat := 118140960795 + 104460 * 2 ^ 59
def prefixEnd_104460 : Nat := 4983230072969 + 3 ^ 40 * 104460 * 2
def baseEnd_104460 : Nat := 15892796790745639546549

theorem tailTrace_104460 : CollatzResearch.WordTrace tailWord_104460 prefixEnd_104460 15892796790745639546549 := by
  unfold tailWord_104460
  simp only [CollatzResearch.WordTrace]
  refine ⟨1904984600783367596383417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2539979467711156795177889 1904984600783367596383417)
  ·
    refine ⟨1428738450587525697287563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1904984600783367596383417 1428738450587525697287563)
    ·
      refine ⟨2143107675881288545931345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1428738450587525697287563 2143107675881288545931345)
      ·
        refine ⟨1607330756910966409448509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2143107675881288545931345 1607330756910966409448509)
        ·
          refine ⟨602749033841612403543191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1607330756910966409448509 602749033841612403543191)
          ·
            refine ⟨904123550762418605314787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602749033841612403543191 904123550762418605314787)
            ·
              refine ⟨1356185326143627907972181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904123550762418605314787 1356185326143627907972181)
              ·
                refine ⟨15892796790745639546549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1356185326143627907972181 15892796790745639546549)
                ·
                  rfl

theorem cell20_104460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_104460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104460 prefixEnd_104460 := by exact prefixLift 104460
  have htrace : WordTrace (prefixWord ++ tailWord_104460) baseStart_104460 baseEnd_104460 := by
    simpa [prefixWord, tailWord_104460, baseEnd_104460] using wordTrace_append hprefix tailTrace_104460
  have hstable : (prefixWord ++ tailWord_104460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104460).length < 2 ^ (prefixWord ++ tailWord_104460).sum := by decide
  have hdescent : baseEnd_104460 < baseStart_104460 := by decide
  rcases family_descends (prefixWord ++ tailWord_104460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104467 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 7]
def baseStart_104467 : Nat := 118140960795 + 104467 * 2 ^ 59
def prefixEnd_104467 : Nat := 4983230072969 + 3 ^ 40 * 104467 * 2
def baseEnd_104467 : Nat := 47681585362976005406285

theorem tailTrace_104467 : CollatzResearch.WordTrace tailWord_104467 prefixEnd_104467 47681585362976005406285 := by
  unfold tailWord_104467
  simp only [CollatzResearch.WordTrace]
  refine ⟨3810224512541375388271655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2540149675027583592181103 3810224512541375388271655)
  ·
    refine ⟨5715336768812063082407483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3810224512541375388271655 5715336768812063082407483)
    ·
      refine ⟨8573005153218094623611225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5715336768812063082407483 8573005153218094623611225)
      ·
        refine ⟨6429753864913570967708419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8573005153218094623611225 6429753864913570967708419)
        ·
          refine ⟨9644630797370356451562629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6429753864913570967708419 9644630797370356451562629)
          ·
            refine ⟨1808368274506941834667993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9644630797370356451562629 1808368274506941834667993)
            ·
              refine ⟨1356276205880206376000995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1808368274506941834667993 1356276205880206376000995)
              ·
                refine ⟨2034414308820309564001493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1356276205880206376000995 2034414308820309564001493)
                ·
                  refine ⟨47681585362976005406285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2034414308820309564001493 47681585362976005406285)
                  ·
                    rfl

theorem cell20_104467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_104467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104467 prefixEnd_104467 := by exact prefixLift 104467
  have htrace : WordTrace (prefixWord ++ tailWord_104467) baseStart_104467 baseEnd_104467 := by
    simpa [prefixWord, tailWord_104467, baseEnd_104467] using wordTrace_append hprefix tailTrace_104467
  have hstable : (prefixWord ++ tailWord_104467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104467).length < 2 ^ (prefixWord ++ tailWord_104467).sum := by decide
  have hdescent : baseEnd_104467 < baseStart_104467 := by decide
  rcases family_descends (prefixWord ++ tailWord_104467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104494 : List Nat := [4, 1, 3, 1, 1, 4, 1, 5]
def baseStart_104494 : Nat := 118140960795 + 104494 * 2 ^ 59
def prefixEnd_104494 : Nat := 4983230072969 + 3 ^ 40 * 104494 * 2
def baseEnd_104494 : Nat := 15897969632894637168725

theorem tailTrace_104494 : CollatzResearch.WordTrace tailWord_104494 prefixEnd_104494 15897969632894637168725 := by
  unfold tailWord_104494
  simp only [CollatzResearch.WordTrace]
  refine ⟨476401160430444874938067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2540806188962372666336357 476401160430444874938067)
  ·
    refine ⟨714601740645667312407101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 476401160430444874938067 714601740645667312407101)
    ·
      refine ⟨267975652742125242152663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 714601740645667312407101 267975652742125242152663)
      ·
        refine ⟨401963479113187863228995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267975652742125242152663 401963479113187863228995)
        ·
          refine ⟨602945218669781794843493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401963479113187863228995 602945218669781794843493)
          ·
            refine ⟨113052228500584086533155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 602945218669781794843493 113052228500584086533155)
            ·
              refine ⟨169578342750876129799733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113052228500584086533155 169578342750876129799733)
              ·
                refine ⟨15897969632894637168725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169578342750876129799733 15897969632894637168725)
                ·
                  rfl

theorem cell20_104494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_104494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104494 prefixEnd_104494 := by exact prefixLift 104494
  have htrace : WordTrace (prefixWord ++ tailWord_104494) baseStart_104494 baseEnd_104494 := by
    simpa [prefixWord, tailWord_104494, baseEnd_104494] using wordTrace_append hprefix tailTrace_104494
  have hstable : (prefixWord ++ tailWord_104494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104494).length < 2 ^ (prefixWord ++ tailWord_104494).sum := by decide
  have hdescent : baseEnd_104494 < baseStart_104494 := by decide
  rcases family_descends (prefixWord ++ tailWord_104494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104536 : List Nat := [2, 1, 2, 2, 1, 5, 7]
def baseStart_104536 : Nat := 118140960795 + 104536 * 2 ^ 59
def prefixEnd_104536 : Nat := 4983230072969 + 3 ^ 40 * 104536 * 2
def baseEnd_104536 : Nat := 5301453204790936900667

theorem tailTrace_104536 : CollatzResearch.WordTrace tailWord_104536 prefixEnd_104536 5301453204790936900667 := by
  unfold tailWord_104536
  simp only [CollatzResearch.WordTrace]
  refine ⟨1906370574645700086266731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2541827432860933448355641 1906370574645700086266731)
  ·
    refine ⟨2859555861968550129400097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1906370574645700086266731 2859555861968550129400097)
    ·
      refine ⟨2144666896476412597050073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2859555861968550129400097 2144666896476412597050073)
      ·
        refine ⟨1608500172357309447787555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2144666896476412597050073 1608500172357309447787555)
        ·
          refine ⟨2412750258535964171681333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1608500172357309447787555 2412750258535964171681333)
          ·
            refine ⟨226195336737746641095125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2412750258535964171681333 226195336737746641095125)
            ·
              refine ⟨5301453204790936900667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 226195336737746641095125 5301453204790936900667)
              ·
                rfl

theorem cell20_104536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 7].length) (baseStart_104536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104536 prefixEnd_104536 := by exact prefixLift 104536
  have htrace : WordTrace (prefixWord ++ tailWord_104536) baseStart_104536 baseEnd_104536 := by
    simpa [prefixWord, tailWord_104536, baseEnd_104536] using wordTrace_append hprefix tailTrace_104536
  have hstable : (prefixWord ++ tailWord_104536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104536).length < 2 ^ (prefixWord ++ tailWord_104536).sum := by decide
  have hdescent : baseEnd_104536 < baseStart_104536 := by decide
  rcases family_descends (prefixWord ++ tailWord_104536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104567 : List Nat := [1, 1, 3, 1, 1, 5, 2, 2, 4]
def baseStart_104567 : Nat := 118140960795 + 104567 * 2 ^ 59
def prefixEnd_104567 : Nat := 4983230072969 + 3 ^ 40 * 104567 * 2
def baseEnd_104567 : Nat := 47727228087820102072543

theorem tailTrace_104567 : CollatzResearch.WordTrace tailWord_104567 prefixEnd_104567 47727228087820102072543 := by
  unfold tailWord_104567
  simp only [CollatzResearch.WordTrace]
  refine ⟨3813871812179092466911955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2542581208119394977941303 3813871812179092466911955)
  ·
    refine ⟨5720807718268638700367933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3813871812179092466911955 5720807718268638700367933)
    ·
      refine ⟨2145302894350739512637975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5720807718268638700367933 2145302894350739512637975)
      ·
        refine ⟨3217954341526109268956963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2145302894350739512637975 3217954341526109268956963)
        ·
          refine ⟨4826931512289163903435445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3217954341526109268956963 4826931512289163903435445)
          ·
            refine ⟨452524829277109115947073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4826931512289163903435445 452524829277109115947073)
            ·
              refine ⟨339393621957831836960305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452524829277109115947073 339393621957831836960305)
              ·
                refine ⟨254545216468373877720229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339393621957831836960305 254545216468373877720229)
                ·
                  refine ⟨47727228087820102072543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 254545216468373877720229 47727228087820102072543)
                  ·
                    rfl

theorem cell20_104567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_104567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104567 prefixEnd_104567 := by exact prefixLift 104567
  have htrace : WordTrace (prefixWord ++ tailWord_104567) baseStart_104567 baseEnd_104567 := by
    simpa [prefixWord, tailWord_104567, baseEnd_104567] using wordTrace_append hprefix tailTrace_104567
  have hstable : (prefixWord ++ tailWord_104567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104567).length < 2 ^ (prefixWord ++ tailWord_104567).sum := by decide
  have hdescent : baseEnd_104567 < baseStart_104567 := by decide
  rcases family_descends (prefixWord ++ tailWord_104567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104652 : List Nat := [2, 2, 1, 6, 2, 1, 2, 2, 2]
def baseStart_104652 : Nat := 118140960795 + 104652 * 2 ^ 59
def prefixEnd_104652 : Nat := 4983230072969 + 3 ^ 40 * 104652 * 2
def baseEnd_104652 : Nat := 47766024403937584238863

theorem tailTrace_104652 : CollatzResearch.WordTrace tailWord_104652 prefixEnd_104652 47766024403937584238863 := by
  unfold tailWord_104652
  simp only [CollatzResearch.WordTrace]
  refine ⟨1908486008435575991878105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2544648011247434655837473 1908486008435575991878105)
  ·
    refine ⟨1431364506326681993908579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1908486008435575991878105 1431364506326681993908579)
    ·
      refine ⟨2147046759490022990862869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1431364506326681993908579 2147046759490022990862869)
      ·
        refine ⟨100642816851094827696697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2147046759490022990862869 100642816851094827696697)
        ·
          refine ⟨75482112638321120772523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100642816851094827696697 75482112638321120772523)
          ·
            refine ⟨113223168957481681158785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75482112638321120772523 113223168957481681158785)
            ·
              refine ⟨84917376718111260869089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113223168957481681158785 84917376718111260869089)
              ·
                refine ⟨63688032538583445651817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84917376718111260869089 63688032538583445651817)
                ·
                  refine ⟨47766024403937584238863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63688032538583445651817 47766024403937584238863)
                  ·
                    rfl

theorem cell20_104652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_104652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104652 prefixEnd_104652 := by exact prefixLift 104652
  have htrace : WordTrace (prefixWord ++ tailWord_104652) baseStart_104652 baseEnd_104652 := by
    simpa [prefixWord, tailWord_104652, baseEnd_104652] using wordTrace_append hprefix tailTrace_104652
  have hstable : (prefixWord ++ tailWord_104652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104652).length < 2 ^ (prefixWord ++ tailWord_104652).sum := by decide
  have hdescent : baseEnd_104652 < baseStart_104652 := by decide
  rcases family_descends (prefixWord ++ tailWord_104652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104657 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 5]
def baseStart_104657 : Nat := 118140960795 + 104657 * 2 ^ 59
def prefixEnd_104657 : Nat := 4983230072969 + 3 ^ 40 * 104657 * 2
def baseEnd_104657 : Nat := 47768306540179789072175

theorem tailTrace_104657 : CollatzResearch.WordTrace tailWord_104657 prefixEnd_104657 47768306540179789072175 := by
  unfold tailWord_104657
  simp only [CollatzResearch.WordTrace]
  refine ⟨3817154381853037837688225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2544769587902025225125483 3817154381853037837688225)
  ·
    refine ⟨2862865786389778378266169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3817154381853037837688225 2862865786389778378266169)
    ·
      refine ⟨2147149339792333783699627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2862865786389778378266169 2147149339792333783699627)
      ·
        refine ⟨3220724009688500675549441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2147149339792333783699627 3220724009688500675549441)
        ·
          refine ⟨2415543007266375506662081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3220724009688500675549441 2415543007266375506662081)
          ·
            refine ⟨1811657255449781629996561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2415543007266375506662081 1811657255449781629996561)
            ·
              refine ⟨1358742941587336222497421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1811657255449781629996561 1358742941587336222497421)
              ·
                refine ⟨509528603095251083436533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1358742941587336222497421 509528603095251083436533)
                ·
                  refine ⟨47768306540179789072175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 509528603095251083436533 47768306540179789072175)
                  ·
                    rfl

theorem cell20_104657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_104657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104657 prefixEnd_104657 := by exact prefixLift 104657
  have htrace : WordTrace (prefixWord ++ tailWord_104657) baseStart_104657 baseEnd_104657 := by
    simpa [prefixWord, tailWord_104657, baseEnd_104657] using wordTrace_append hprefix tailTrace_104657
  have hstable : (prefixWord ++ tailWord_104657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104657).length < 2 ^ (prefixWord ++ tailWord_104657).sum := by decide
  have hdescent : baseEnd_104657 < baseStart_104657 := by decide
  rcases family_descends (prefixWord ++ tailWord_104657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104698 : List Nat := [3, 1, 1, 1, 1, 5, 1, 5, 2]
def baseStart_104698 : Nat := 118140960795 + 104698 * 2 ^ 59
def prefixEnd_104698 : Nat := 4983230072969 + 3 ^ 40 * 104698 * 2
def baseEnd_104698 : Nat := 47787020057365868705341

theorem tailTrace_104698 : CollatzResearch.WordTrace tailWord_104698 prefixEnd_104698 47787020057365868705341 := by
  unfold tailWord_104698
  simp only [CollatzResearch.WordTrace]
  refine ⟨954662443676125459982687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2545766516469667893287165 954662443676125459982687)
  ·
    refine ⟨1431993665514188189974031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 954662443676125459982687 1431993665514188189974031)
    ·
      refine ⟨2147990498271282284961047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1431993665514188189974031 2147990498271282284961047)
      ·
        refine ⟨3221985747406923427441571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2147990498271282284961047 3221985747406923427441571)
        ·
          refine ⟨4832978621110385141162357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3221985747406923427441571 4832978621110385141162357)
          ·
            refine ⟨453091745729098606983971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4832978621110385141162357 453091745729098606983971)
            ·
              refine ⟨679637618593647910475957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453091745729098606983971 679637618593647910475957)
              ·
                refine ⟨63716026743154491607121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 679637618593647910475957 63716026743154491607121)
                ·
                  refine ⟨47787020057365868705341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63716026743154491607121 47787020057365868705341)
                  ·
                    rfl

theorem cell20_104698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_104698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104698 prefixEnd_104698 := by exact prefixLift 104698
  have htrace : WordTrace (prefixWord ++ tailWord_104698) baseStart_104698 baseEnd_104698 := by
    simpa [prefixWord, tailWord_104698, baseEnd_104698] using wordTrace_append hprefix tailTrace_104698
  have hstable : (prefixWord ++ tailWord_104698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104698).length < 2 ^ (prefixWord ++ tailWord_104698).sum := by decide
  have hdescent : baseEnd_104698 < baseStart_104698 := by decide
  rcases family_descends (prefixWord ++ tailWord_104698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104708 : List Nat := [2, 3, 2, 2, 3, 2, 1, 2, 3]
def baseStart_104708 : Nat := 118140960795 + 104708 * 2 ^ 59
def prefixEnd_104708 : Nat := 4983230072969 + 3 ^ 40 * 104708 * 2
def baseEnd_104708 : Nat := 47791584329850278371967

theorem tailTrace_104708 : CollatzResearch.WordTrace tailWord_104708 prefixEnd_104708 47791584329850278371967 := by
  unfold tailWord_104708
  simp only [CollatzResearch.WordTrace]
  refine ⟨1909507252334136773897389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2546009669778849031863185 1909507252334136773897389)
  ·
    refine ⟨716065219625301290211521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1909507252334136773897389 716065219625301290211521)
    ·
      refine ⟨537048914718975967658641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 716065219625301290211521 537048914718975967658641)
      ·
        refine ⟨402786686039231975743981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 537048914718975967658641 402786686039231975743981)
        ·
          refine ⟨151045007264711990903993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 402786686039231975743981 151045007264711990903993)
          ·
            refine ⟨113283755448533993177995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151045007264711990903993 113283755448533993177995)
            ·
              refine ⟨169925633172800989766993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113283755448533993177995 169925633172800989766993)
              ·
                refine ⟨127444224879600742325245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169925633172800989766993 127444224879600742325245)
                ·
                  refine ⟨47791584329850278371967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127444224879600742325245 47791584329850278371967)
                  ·
                    rfl

theorem cell20_104708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_104708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104708 prefixEnd_104708 := by exact prefixLift 104708
  have htrace : WordTrace (prefixWord ++ tailWord_104708) baseStart_104708 baseEnd_104708 := by
    simpa [prefixWord, tailWord_104708, baseEnd_104708] using wordTrace_append hprefix tailTrace_104708
  have hstable : (prefixWord ++ tailWord_104708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104708).length < 2 ^ (prefixWord ++ tailWord_104708).sum := by decide
  have hdescent : baseEnd_104708 < baseStart_104708 := by decide
  rcases family_descends (prefixWord ++ tailWord_104708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104712 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 5]
def baseStart_104712 : Nat := 118140960795 + 104712 * 2 ^ 59
def prefixEnd_104712 : Nat := 4983230072969 + 3 ^ 40 * 104712 * 2
def baseEnd_104712 : Nat := 47793410038844042238617

theorem tailTrace_104712 : CollatzResearch.WordTrace tailWord_104712 prefixEnd_104712 47793410038844042238617 := by
  unfold tailWord_104712
  simp only [CollatzResearch.WordTrace]
  refine ⟨1909580198326891115470195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2546106931102521487293593 1909580198326891115470195)
  ·
    refine ⟨2864370297490336673205293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1909580198326891115470195 2864370297490336673205293)
    ·
      refine ⟨1074138861558876252451985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2864370297490336673205293 1074138861558876252451985)
      ·
        refine ⟨805604146169157189338989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1074138861558876252451985 805604146169157189338989)
        ·
          refine ⟨302101554813433946002121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 805604146169157189338989 302101554813433946002121)
          ·
            refine ⟨226576166110075459501591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302101554813433946002121 226576166110075459501591)
            ·
              refine ⟨339864249165113189252387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226576166110075459501591 339864249165113189252387)
              ·
                refine ⟨509796373747669783878581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339864249165113189252387 509796373747669783878581)
                ·
                  refine ⟨47793410038844042238617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 509796373747669783878581 47793410038844042238617)
                  ·
                    rfl

theorem cell20_104712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_104712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104712 prefixEnd_104712 := by exact prefixLift 104712
  have htrace : WordTrace (prefixWord ++ tailWord_104712) baseStart_104712 baseEnd_104712 := by
    simpa [prefixWord, tailWord_104712, baseEnd_104712] using wordTrace_append hprefix tailTrace_104712
  have hstable : (prefixWord ++ tailWord_104712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104712).length < 2 ^ (prefixWord ++ tailWord_104712).sum := by decide
  have hdescent : baseEnd_104712 < baseStart_104712 := by decide
  rcases family_descends (prefixWord ++ tailWord_104712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104749 : List Nat := [1, 5, 3, 1, 2, 2, 1, 3, 2]
def baseStart_104749 : Nat := 118140960795 + 104749 * 2 ^ 59
def prefixEnd_104749 : Nat := 4983230072969 + 3 ^ 40 * 104749 * 2
def baseEnd_104749 : Nat := 47810297847036358005133

theorem tailTrace_104749 : CollatzResearch.WordTrace tailWord_104749 prefixEnd_104749 47810297847036358005133 := by
  unfold tailWord_104749
  simp only [CollatzResearch.WordTrace]
  refine ⟨3820509897519737550037301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2547006598346491700024867 3820509897519737550037301)
  ·
    refine ⟨358172802892475395315997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3820509897519737550037301 358172802892475395315997)
    ·
      refine ⟨134314801084678273243499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358172802892475395315997 134314801084678273243499)
      ·
        refine ⟨201472201627017409865249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134314801084678273243499 201472201627017409865249)
        ·
          refine ⟨151104151220263057398937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201472201627017409865249 151104151220263057398937)
          ·
            refine ⟨113328113415197293049203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151104151220263057398937 113328113415197293049203)
            ·
              refine ⟨169992170122795939573805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113328113415197293049203 169992170122795939573805)
              ·
                refine ⟨63747063796048477340177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169992170122795939573805 63747063796048477340177)
                ·
                  refine ⟨47810297847036358005133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63747063796048477340177 47810297847036358005133)
                  ·
                    rfl

theorem cell20_104749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_104749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104749 prefixEnd_104749 := by exact prefixLift 104749
  have htrace : WordTrace (prefixWord ++ tailWord_104749) baseStart_104749 baseEnd_104749 := by
    simpa [prefixWord, tailWord_104749, baseEnd_104749] using wordTrace_append hprefix tailTrace_104749
  have hstable : (prefixWord ++ tailWord_104749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104749).length < 2 ^ (prefixWord ++ tailWord_104749).sum := by decide
  have hdescent : baseEnd_104749 < baseStart_104749 := by decide
  rcases family_descends (prefixWord ++ tailWord_104749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104771 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 5]
def baseStart_104771 : Nat := 118140960795 + 104771 * 2 ^ 59
def prefixEnd_104771 : Nat := 4983230072969 + 3 ^ 40 * 104771 * 2
def baseEnd_104771 : Nat := 47820339246502059271709

theorem tailTrace_104771 : CollatzResearch.WordTrace tailWord_104771 prefixEnd_104771 47820339246502059271709 := by
  unfold tailWord_104771
  simp only [CollatzResearch.WordTrace]
  refine ⟨3821312303440035307338167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2547541535626690204892111 3821312303440035307338167)
  ·
    refine ⟨5731968455160052961007251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3821312303440035307338167 5731968455160052961007251)
    ·
      refine ⟨8597952682740079441510877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5731968455160052961007251 8597952682740079441510877)
      ·
        refine ⟨3224232256027529790566579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8597952682740079441510877 3224232256027529790566579)
        ·
          refine ⟨4836348384041294685849869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3224232256027529790566579 4836348384041294685849869)
          ·
            refine ⟨1813630644015485507193701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4836348384041294685849869 1813630644015485507193701)
            ·
              refine ⟨340055745752903532598819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1813630644015485507193701 340055745752903532598819)
              ·
                refine ⟨510083618629355298898229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340055745752903532598819 510083618629355298898229)
                ·
                  refine ⟨47820339246502059271709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 510083618629355298898229 47820339246502059271709)
                  ·
                    rfl

theorem cell20_104771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_104771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104771 prefixEnd_104771 := by exact prefixLift 104771
  have htrace : WordTrace (prefixWord ++ tailWord_104771) baseStart_104771 baseEnd_104771 := by
    simpa [prefixWord, tailWord_104771, baseEnd_104771] using wordTrace_append hprefix tailTrace_104771
  have hstable : (prefixWord ++ tailWord_104771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104771).length < 2 ^ (prefixWord ++ tailWord_104771).sum := by decide
  have hdescent : baseEnd_104771 < baseStart_104771 := by decide
  rcases family_descends (prefixWord ++ tailWord_104771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104829 : List Nat := [1, 4, 1, 1, 2, 3, 4, 2, 2]
def baseStart_104829 : Nat := 118140960795 + 104829 * 2 ^ 59
def prefixEnd_104829 : Nat := 4983230072969 + 3 ^ 40 * 104829 * 2
def baseEnd_104829 : Nat := 47846812026911635338139

theorem tailTrace_104829 : CollatzResearch.WordTrace tailWord_104829 prefixEnd_104829 47846812026911635338139 := by
  unfold tailWord_104829
  simp only [CollatzResearch.WordTrace]
  refine ⟨3823427737229911212949541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2548951824819940808633027 3823427737229911212949541)
  ·
    refine ⟨716892700730608352428039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3823427737229911212949541 716892700730608352428039)
    ·
      refine ⟨1075339051095912528642059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 716892700730608352428039 1075339051095912528642059)
      ·
        refine ⟨1613008576643868792963089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1075339051095912528642059 1613008576643868792963089)
        ·
          refine ⟨1209756432482901594722317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1613008576643868792963089 1209756432482901594722317)
          ·
            refine ⟨453658662181088098020869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1209756432482901594722317 453658662181088098020869)
            ·
              refine ⟨85060999158954018378913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 453658662181088098020869 85060999158954018378913)
              ·
                refine ⟨63795749369215513784185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85060999158954018378913 63795749369215513784185)
                ·
                  refine ⟨47846812026911635338139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63795749369215513784185 47846812026911635338139)
                  ·
                    rfl

theorem cell20_104829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_104829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104829 prefixEnd_104829 := by exact prefixLift 104829
  have htrace : WordTrace (prefixWord ++ tailWord_104829) baseStart_104829 baseEnd_104829 := by
    simpa [prefixWord, tailWord_104829, baseEnd_104829] using wordTrace_append hprefix tailTrace_104829
  have hstable : (prefixWord ++ tailWord_104829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104829).length < 2 ^ (prefixWord ++ tailWord_104829).sum := by decide
  have hdescent : baseEnd_104829 < baseStart_104829 := by decide
  rcases family_descends (prefixWord ++ tailWord_104829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104877 : List Nat := [1, 5, 2, 2, 3, 1, 1, 2, 3]
def baseStart_104877 : Nat := 118140960795 + 104877 * 2 ^ 59
def prefixEnd_104877 : Nat := 4983230072969 + 3 ^ 40 * 104877 * 2
def baseEnd_104877 : Nat := 47868720534836801737943

theorem tailTrace_104877 : CollatzResearch.WordTrace tailWord_104877 prefixEnd_104877 47868720534836801737943 := by
  unfold tailWord_104877
  simp only [CollatzResearch.WordTrace]
  refine ⟨3825178441056015410696885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2550118960704010273797923 3825178441056015410696885)
  ·
    refine ⟨358610478849001444752833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3825178441056015410696885 358610478849001444752833)
    ·
      refine ⟨268957859136751083564625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358610478849001444752833 268957859136751083564625)
      ·
        refine ⟨201718394352563312673469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268957859136751083564625 201718394352563312673469)
        ·
          refine ⟨75644397882211242252551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201718394352563312673469 75644397882211242252551)
          ·
            refine ⟨113466596823316863378827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75644397882211242252551 113466596823316863378827)
            ·
              refine ⟨170199895234975295068241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113466596823316863378827 170199895234975295068241)
              ·
                refine ⟨127649921426231471301181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170199895234975295068241 127649921426231471301181)
                ·
                  refine ⟨47868720534836801737943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127649921426231471301181 47868720534836801737943)
                  ·
                    rfl

theorem cell20_104877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_104877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104877 prefixEnd_104877 := by exact prefixLift 104877
  have htrace : WordTrace (prefixWord ++ tailWord_104877) baseStart_104877 baseEnd_104877 := by
    simpa [prefixWord, tailWord_104877, baseEnd_104877] using wordTrace_append hprefix tailTrace_104877
  have hstable : (prefixWord ++ tailWord_104877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104877).length < 2 ^ (prefixWord ++ tailWord_104877).sum := by decide
  have hdescent : baseEnd_104877 < baseStart_104877 := by decide
  rcases family_descends (prefixWord ++ tailWord_104877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104881 : List Nat := [1, 2, 2, 4, 1, 4, 1, 2, 3]
def baseStart_104881 : Nat := 118140960795 + 104881 * 2 ^ 59
def prefixEnd_104881 : Nat := 4983230072969 + 3 ^ 40 * 104881 * 2
def baseEnd_104881 : Nat := 47870546243830565604593

theorem tailTrace_104881 : CollatzResearch.WordTrace tailWord_104881 prefixEnd_104881 47870546243830565604593 := by
  unfold tailWord_104881
  simp only [CollatzResearch.WordTrace]
  refine ⟨3825324333041524093842497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2550216222027682729228331 3825324333041524093842497)
  ·
    refine ⟨2868993249781143070381873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3825324333041524093842497 2868993249781143070381873)
    ·
      refine ⟨2151744937335857302786405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2868993249781143070381873 2151744937335857302786405)
      ·
        refine ⟨403452175750473244272451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2151744937335857302786405 403452175750473244272451)
        ·
          refine ⟨605178263625709866408677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403452175750473244272451 605178263625709866408677)
          ·
            refine ⟨113470924429820599951627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 605178263625709866408677 113470924429820599951627)
            ·
              refine ⟨170206386644730899927441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113470924429820599951627 170206386644730899927441)
              ·
                refine ⟨127654789983548174945581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170206386644730899927441 127654789983548174945581)
                ·
                  refine ⟨47870546243830565604593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127654789983548174945581 47870546243830565604593)
                  ·
                    rfl

theorem cell20_104881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 3].length) (baseStart_104881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104881 prefixEnd_104881 := by exact prefixLift 104881
  have htrace : WordTrace (prefixWord ++ tailWord_104881) baseStart_104881 baseEnd_104881 := by
    simpa [prefixWord, tailWord_104881, baseEnd_104881] using wordTrace_append hprefix tailTrace_104881
  have hstable : (prefixWord ++ tailWord_104881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104881).length < 2 ^ (prefixWord ++ tailWord_104881).sum := by decide
  have hdescent : baseEnd_104881 < baseStart_104881 := by decide
  rcases family_descends (prefixWord ++ tailWord_104881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104884 : List Nat := [2, 5, 2, 2, 1, 1, 2, 1, 4]
def baseStart_104884 : Nat := 118140960795 + 104884 * 2 ^ 59
def prefixEnd_104884 : Nat := 4983230072969 + 3 ^ 40 * 104884 * 2
def baseEnd_104884 : Nat := 47871915525575888504581

theorem tailTrace_104884 : CollatzResearch.WordTrace tailWord_104884 prefixEnd_104884 47871915525575888504581 := by
  unfold tailWord_104884
  simp only [CollatzResearch.WordTrace]
  refine ⟨1912716876015327803100853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2550289168020437070801137 1912716876015327803100853)
  ·
    refine ⟨179317207126436981540705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1912716876015327803100853 179317207126436981540705)
    ·
      refine ⟨134487905344827736155529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179317207126436981540705 134487905344827736155529)
      ·
        refine ⟨100865929008620802116647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134487905344827736155529 100865929008620802116647)
        ·
          refine ⟨151298893512931203174971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100865929008620802116647 151298893512931203174971)
          ·
            refine ⟨226948340269396804762457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151298893512931203174971 226948340269396804762457)
            ·
              refine ⟨170211255202047603571843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226948340269396804762457 170211255202047603571843)
              ·
                refine ⟨255316882803071405357765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170211255202047603571843 255316882803071405357765)
                ·
                  refine ⟨47871915525575888504581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255316882803071405357765 47871915525575888504581)
                  ·
                    rfl

theorem cell20_104884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_104884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104884 prefixEnd_104884 := by exact prefixLift 104884
  have htrace : WordTrace (prefixWord ++ tailWord_104884) baseStart_104884 baseEnd_104884 := by
    simpa [prefixWord, tailWord_104884, baseEnd_104884] using wordTrace_append hprefix tailTrace_104884
  have hstable : (prefixWord ++ tailWord_104884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104884).length < 2 ^ (prefixWord ++ tailWord_104884).sum := by decide
  have hdescent : baseEnd_104884 < baseStart_104884 := by decide
  rcases family_descends (prefixWord ++ tailWord_104884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104899 : List Nat := [1, 1, 1, 3, 1, 1, 3, 9]
def baseStart_104899 : Nat := 118140960795 + 104899 * 2 ^ 59
def prefixEnd_104899 : Nat := 4983230072969 + 3 ^ 40 * 104899 * 2
def baseEnd_104899 : Nat := 15959587311434167668173

theorem tailTrace_104899 : CollatzResearch.WordTrace tailWord_104899 prefixEnd_104899 15959587311434167668173 := by
  unfold tailWord_104899
  simp only [CollatzResearch.WordTrace]
  refine ⟨3825980846976313167997751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2550653897984208778665167 3825980846976313167997751)
  ·
    refine ⟨5738971270464469751996627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3825980846976313167997751 5738971270464469751996627)
    ·
      refine ⟨8608456905696704627994941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5738971270464469751996627 8608456905696704627994941)
      ·
        refine ⟨3228171339636264235498103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8608456905696704627994941 3228171339636264235498103)
        ·
          refine ⟨4842257009454396353247155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3228171339636264235498103 4842257009454396353247155)
          ·
            refine ⟨7263385514181594529870733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4842257009454396353247155 7263385514181594529870733)
            ·
              refine ⟨2723769567818097948701525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7263385514181594529870733 2723769567818097948701525)
              ·
                refine ⟨15959587311434167668173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2723769567818097948701525 15959587311434167668173)
                ·
                  rfl

theorem cell20_104899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 9].length) (baseStart_104899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104899 prefixEnd_104899 := by exact prefixLift 104899
  have htrace : WordTrace (prefixWord ++ tailWord_104899) baseStart_104899 baseEnd_104899 := by
    simpa [prefixWord, tailWord_104899, baseEnd_104899] using wordTrace_append hprefix tailTrace_104899
  have hstable : (prefixWord ++ tailWord_104899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104899).length < 2 ^ (prefixWord ++ tailWord_104899).sum := by decide
  have hdescent : baseEnd_104899 < baseStart_104899 := by decide
  rcases family_descends (prefixWord ++ tailWord_104899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104933 : List Nat := [1, 3, 1, 5, 2, 2, 6]
def baseStart_104933 : Nat := 118140960795 + 104933 * 2 ^ 59
def prefixEnd_104933 : Nat := 4983230072969 + 3 ^ 40 * 104933 * 2
def baseEnd_104933 : Nat := 5321586717861055096783

theorem tailTrace_104933 : CollatzResearch.WordTrace tailWord_104933 prefixEnd_104933 5321586717861055096783 := by
  unfold tailWord_104933
  simp only [CollatzResearch.WordTrace]
  refine ⟨3827220928853136974735453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2551480619235424649823635 3827220928853136974735453)
  ·
    refine ⟨1435207848319926365525795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3827220928853136974735453 1435207848319926365525795)
    ·
      refine ⟨2152811772479889548288693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1435207848319926365525795 2152811772479889548288693)
      ·
        refine ⟨201826103669989645152065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2152811772479889548288693 201826103669989645152065)
        ·
          refine ⟨151369577752492233864049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201826103669989645152065 151369577752492233864049)
          ·
            refine ⟨113527183314369175398037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151369577752492233864049 113527183314369175398037)
            ·
              refine ⟨5321586717861055096783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113527183314369175398037 5321586717861055096783)
              ·
                rfl

theorem cell20_104933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 6].length) (baseStart_104933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104933 prefixEnd_104933 := by exact prefixLift 104933
  have htrace : WordTrace (prefixWord ++ tailWord_104933) baseStart_104933 baseEnd_104933 := by
    simpa [prefixWord, tailWord_104933, baseEnd_104933] using wordTrace_append hprefix tailTrace_104933
  have hstable : (prefixWord ++ tailWord_104933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104933).length < 2 ^ (prefixWord ++ tailWord_104933).sum := by decide
  have hdescent : baseEnd_104933 < baseStart_104933 := by decide
  rcases family_descends (prefixWord ++ tailWord_104933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104968 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 6]
def baseStart_104968 : Nat := 118140960795 + 104968 * 2 ^ 59
def prefixEnd_104968 : Nat := 4983230072969 + 3 ^ 40 * 104968 * 2
def baseEnd_104968 : Nat := 47910255414444929704237

theorem tailTrace_104968 : CollatzResearch.WordTrace tailWord_104968 prefixEnd_104968 47910255414444929704237 := by
  unfold tailWord_104968
  simp only [CollatzResearch.WordTrace]
  refine ⟨1914248741863168976129779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2552331655817558634839705 1914248741863168976129779)
  ·
    refine ⟨2871373112794753464194669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1914248741863168976129779 2871373112794753464194669)
    ·
      refine ⟨1076764917298032549073001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2871373112794753464194669 1076764917298032549073001)
      ·
        refine ⟨807573687973524411804751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1076764917298032549073001 807573687973524411804751)
        ·
          refine ⟨1211360531960286617707127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807573687973524411804751 1211360531960286617707127)
          ·
            refine ⟨1817040797940429926560691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211360531960286617707127 1817040797940429926560691)
            ·
              refine ⟨2725561196910644889841037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817040797940429926560691 2725561196910644889841037)
              ·
                refine ⟨1022085448841491833690389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2725561196910644889841037 1022085448841491833690389)
                ·
                  refine ⟨47910255414444929704237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1022085448841491833690389 47910255414444929704237)
                  ·
                    rfl

theorem cell20_104968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_104968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104968 prefixEnd_104968 := by exact prefixLift 104968
  have htrace : WordTrace (prefixWord ++ tailWord_104968) baseStart_104968 baseEnd_104968 := by
    simpa [prefixWord, tailWord_104968, baseEnd_104968] using wordTrace_append hprefix tailTrace_104968
  have hstable : (prefixWord ++ tailWord_104968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104968).length < 2 ^ (prefixWord ++ tailWord_104968).sum := by decide
  have hdescent : baseEnd_104968 < baseStart_104968 := by decide
  rcases family_descends (prefixWord ++ tailWord_104968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104992 : List Nat := [2, 1, 1, 6, 2, 8]
def baseStart_104992 : Nat := 118140960795 + 104992 * 2 ^ 59
def prefixEnd_104992 : Nat := 4983230072969 + 3 ^ 40 * 104992 * 2
def baseEnd_104992 : Nat := 1774859617348426403857

theorem tailTrace_104992 : CollatzResearch.WordTrace tailWord_104992 prefixEnd_104992 1774859617348426403857 := by
  unfold tailWord_104992
  simp only [CollatzResearch.WordTrace]
  refine ⟨1914686417819695025566615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2552915223759593367422153 1914686417819695025566615)
  ·
    refine ⟨2872029626729542538349923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1914686417819695025566615 2872029626729542538349923)
    ·
      refine ⟨4308044440094313807524885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2872029626729542538349923 4308044440094313807524885)
      ·
        refine ⟨201939583129420959727729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4308044440094313807524885 201939583129420959727729)
        ·
          refine ⟨151454687347065719795797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201939583129420959727729 151454687347065719795797)
          ·
            refine ⟨1774859617348426403857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 151454687347065719795797 1774859617348426403857)
            ·
              rfl

theorem cell20_104992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 8].length) (baseStart_104992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_104992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_104992 prefixEnd_104992 := by exact prefixLift 104992
  have htrace : WordTrace (prefixWord ++ tailWord_104992) baseStart_104992 baseEnd_104992 := by
    simpa [prefixWord, tailWord_104992, baseEnd_104992] using wordTrace_append hprefix tailTrace_104992
  have hstable : (prefixWord ++ tailWord_104992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104992).length < 2 ^ (prefixWord ++ tailWord_104992).sum := by decide
  have hdescent : baseEnd_104992 < baseStart_104992 := by decide
  rcases family_descends (prefixWord ++ tailWord_104992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105099 : List Nat := [1, 1, 1, 1, 4, 1, 2, 7, 2]
def baseStart_105099 : Nat := 118140960795 + 105099 * 2 ^ 59
def prefixEnd_105099 : Nat := 4983230072969 + 3 ^ 40 * 105099 * 2
def baseEnd_105099 : Nat := 47970047383990696337035

theorem tailTrace_105099 : CollatzResearch.WordTrace tailWord_105099 prefixEnd_105099 47970047383990696337035 := by
  unfold tailWord_105099
  simp only [CollatzResearch.WordTrace]
  refine ⟨3833275446251747325278351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2555516964167831550185567 3833275446251747325278351)
  ·
    refine ⟨5749913169377620987917527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3833275446251747325278351 5749913169377620987917527)
    ·
      refine ⟨8624869754066431481876291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5749913169377620987917527 8624869754066431481876291)
      ·
        refine ⟨12937304631099647222814437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8624869754066431481876291 12937304631099647222814437)
        ·
          refine ⟨2425744618331183854277707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12937304631099647222814437 2425744618331183854277707)
          ·
            refine ⟨3638616927496775781416561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2425744618331183854277707 3638616927496775781416561)
            ·
              refine ⟨2728962695622581836062421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3638616927496775781416561 2728962695622581836062421)
              ·
                refine ⟨63960063178654261782713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2728962695622581836062421 63960063178654261782713)
                ·
                  refine ⟨47970047383990696337035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63960063178654261782713 47970047383990696337035)
                  ·
                    rfl

theorem cell20_105099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 2].length) (baseStart_105099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105099 prefixEnd_105099 := by exact prefixLift 105099
  have htrace : WordTrace (prefixWord ++ tailWord_105099) baseStart_105099 baseEnd_105099 := by
    simpa [prefixWord, tailWord_105099, baseEnd_105099] using wordTrace_append hprefix tailTrace_105099
  have hstable : (prefixWord ++ tailWord_105099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105099).length < 2 ^ (prefixWord ++ tailWord_105099).sum := by decide
  have hdescent : baseEnd_105099 < baseStart_105099 := by decide
  rcases family_descends (prefixWord ++ tailWord_105099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105106 : List Nat := [3, 2, 3, 1, 2, 1, 8]
def baseStart_105106 : Nat := 118140960795 + 105106 * 2 ^ 59
def prefixEnd_105106 : Nat := 4983230072969 + 3 ^ 40 * 105106 * 2
def baseEnd_105106 : Nat := 5330360263858864789297

theorem tailTrace_105106 : CollatzResearch.WordTrace tailWord_105106 prefixEnd_105106 5330360263858864789297 := by
  unfold tailWord_105106
  simp only [CollatzResearch.WordTrace]
  refine ⟨958382689306596880195793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2555687171484258347188781 958382689306596880195793)
  ·
    refine ⟨718787016979947660146845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 958382689306596880195793 718787016979947660146845)
    ·
      refine ⟨269545131367480372555067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 718787016979947660146845 269545131367480372555067)
      ·
        refine ⟨404317697051220558832601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269545131367480372555067 404317697051220558832601)
        ·
          refine ⟨303238272788415419124451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404317697051220558832601 303238272788415419124451)
          ·
            refine ⟨454857409182623128686677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303238272788415419124451 454857409182623128686677)
            ·
              refine ⟨5330360263858864789297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 454857409182623128686677 5330360263858864789297)
              ·
                rfl

theorem cell20_105106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 8].length) (baseStart_105106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105106 prefixEnd_105106 := by exact prefixLift 105106
  have htrace : WordTrace (prefixWord ++ tailWord_105106) baseStart_105106 baseEnd_105106 := by
    simpa [prefixWord, tailWord_105106, baseEnd_105106] using wordTrace_append hprefix tailTrace_105106
  have hstable : (prefixWord ++ tailWord_105106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105106).length < 2 ^ (prefixWord ++ tailWord_105106).sum := by decide
  have hdescent : baseEnd_105106 < baseStart_105106 := by decide
  rcases family_descends (prefixWord ++ tailWord_105106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105113 : List Nat := [1, 2, 1, 2, 1, 2, 4, 4, 3]
def baseStart_105113 : Nat := 118140960795 + 105113 * 2 ^ 59
def prefixEnd_105113 : Nat := 4983230072969 + 3 ^ 40 * 105113 * 2
def baseEnd_105113 : Nat := 47976437365468869870311

theorem tailTrace_105113 : CollatzResearch.WordTrace tailWord_105113 prefixEnd_105113 47976437365468869870311 := by
  unfold tailWord_105113
  simp only [CollatzResearch.WordTrace]
  refine ⟨3833786068201027716287993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2555857378800685144191995 3833786068201027716287993)
  ·
    refine ⟨2875339551150770787215995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3833786068201027716287993 2875339551150770787215995)
    ·
      refine ⟨4313009326726156180823993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2875339551150770787215995 4313009326726156180823993)
      ·
        refine ⟨3234756995044617135617995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4313009326726156180823993 3234756995044617135617995)
        ·
          refine ⟨4852135492566925703426993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3234756995044617135617995 4852135492566925703426993)
          ·
            refine ⟨3639101619425194277570245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4852135492566925703426993 3639101619425194277570245)
            ·
              refine ⟨682331553642223927044421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3639101619425194277570245 682331553642223927044421)
              ·
                refine ⟨127937166307916986320829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 682331553642223927044421 127937166307916986320829)
                ·
                  refine ⟨47976437365468869870311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127937166307916986320829 47976437365468869870311)
                  ·
                    rfl

theorem cell20_105113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_105113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105113 prefixEnd_105113 := by exact prefixLift 105113
  have htrace : WordTrace (prefixWord ++ tailWord_105113) baseStart_105113 baseEnd_105113 := by
    simpa [prefixWord, tailWord_105113, baseEnd_105113] using wordTrace_append hprefix tailTrace_105113
  have hstable : (prefixWord ++ tailWord_105113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105113).length < 2 ^ (prefixWord ++ tailWord_105113).sum := by decide
  have hdescent : baseEnd_105113 < baseStart_105113 := by decide
  rcases family_descends (prefixWord ++ tailWord_105113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105116 : List Nat := [2, 2, 3, 2, 2, 3, 1, 1, 4]
def baseStart_105116 : Nat := 118140960795 + 105116 * 2 ^ 59
def prefixEnd_105116 : Nat := 4983230072969 + 3 ^ 40 * 105116 * 2
def baseEnd_105116 : Nat := 47977806647214192770299

theorem tailTrace_105116 : CollatzResearch.WordTrace tailWord_105116 prefixEnd_105116 47977806647214192770299 := by
  unfold tailWord_105116
  simp only [CollatzResearch.WordTrace]
  refine ⟨1916947743595079614323601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2555930324793439485764801 1916947743595079614323601)
  ·
    refine ⟨1437710807696309710742701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1916947743595079614323601 1437710807696309710742701)
    ·
      refine ⟨539141552886116141528513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1437710807696309710742701 539141552886116141528513)
      ·
        refine ⟨404356164664587106146385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539141552886116141528513 404356164664587106146385)
        ·
          refine ⟨303267123498440329609789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404356164664587106146385 303267123498440329609789)
          ·
            refine ⟨113725171311915123603671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303267123498440329609789 113725171311915123603671)
            ·
              refine ⟨170587756967872685405507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113725171311915123603671 170587756967872685405507)
              ·
                refine ⟨255881635451809028108261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170587756967872685405507 255881635451809028108261)
                ·
                  refine ⟨47977806647214192770299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255881635451809028108261 47977806647214192770299)
                  ·
                    rfl

theorem cell20_105116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_105116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105116 prefixEnd_105116 := by exact prefixLift 105116
  have htrace : WordTrace (prefixWord ++ tailWord_105116) baseStart_105116 baseEnd_105116 := by
    simpa [prefixWord, tailWord_105116, baseEnd_105116] using wordTrace_append hprefix tailTrace_105116
  have hstable : (prefixWord ++ tailWord_105116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105116).length < 2 ^ (prefixWord ++ tailWord_105116).sum := by decide
  have hdescent : baseEnd_105116 < baseStart_105116 := by decide
  rcases family_descends (prefixWord ++ tailWord_105116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105205 : List Nat := [1, 3, 6, 1, 1, 1, 2, 3, 2]
def baseStart_105205 : Nat := 118140960795 + 105205 * 2 ^ 59
def prefixEnd_105205 : Nat := 4983230072969 + 3 ^ 40 * 105205 * 2
def baseEnd_105205 : Nat := 48018428672325438803269

theorem tailTrace_105205 : CollatzResearch.WordTrace tailWord_105205 prefixEnd_105205 48018428672325438803269 := by
  unfold tailWord_105205
  simp only [CollatzResearch.WordTrace]
  refine ⟨3837141583867727428637069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2558094389245151619091379 3837141583867727428637069)
  ·
    refine ⟨1438928093950397785738901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3837141583867727428637069 1438928093950397785738901)
    ·
      refine ⟨67449754403924896206511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1438928093950397785738901 67449754403924896206511)
      ·
        refine ⟨101174631605887344309767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67449754403924896206511 101174631605887344309767)
        ·
          refine ⟨151761947408831016464651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101174631605887344309767 151761947408831016464651)
          ·
            refine ⟨227642921113246524696977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151761947408831016464651 227642921113246524696977)
            ·
              refine ⟨170732190834934893522733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227642921113246524696977 170732190834934893522733)
              ·
                refine ⟨64024571563100585071025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170732190834934893522733 64024571563100585071025)
                ·
                  refine ⟨48018428672325438803269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64024571563100585071025 48018428672325438803269)
                  ·
                    rfl

theorem cell20_105205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_105205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105205 prefixEnd_105205 := by exact prefixLift 105205
  have htrace : WordTrace (prefixWord ++ tailWord_105205) baseStart_105205 baseEnd_105205 := by
    simpa [prefixWord, tailWord_105205, baseEnd_105205] using wordTrace_append hprefix tailTrace_105205
  have hstable : (prefixWord ++ tailWord_105205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105205).length < 2 ^ (prefixWord ++ tailWord_105205).sum := by decide
  have hdescent : baseEnd_105205 < baseStart_105205 := by decide
  rcases family_descends (prefixWord ++ tailWord_105205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105223 : List Nat := [1, 1, 4, 4, 1, 3, 1, 2, 3]
def baseStart_105223 : Nat := 118140960795 + 105223 * 2 ^ 59
def prefixEnd_105223 : Nat := 4983230072969 + 3 ^ 40 * 105223 * 2
def baseEnd_105223 : Nat := 48026644362797376203195

theorem tailTrace_105223 : CollatzResearch.WordTrace tailWord_105223 prefixEnd_105223 48026644362797376203195 := by
  unfold tailWord_105223
  simp only [CollatzResearch.WordTrace]
  refine ⟨3837798097802516502792323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2558532065201677668528215 3837798097802516502792323)
  ·
    refine ⟨5756697146703774754188485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3837798097802516502792323 5756697146703774754188485)
    ·
      refine ⟨1079380715006957766410341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5756697146703774754188485 1079380715006957766410341)
      ·
        refine ⟨202383884063804581201939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1079380715006957766410341 202383884063804581201939)
        ·
          refine ⟨303575826095706871802909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202383884063804581201939 303575826095706871802909)
          ·
            refine ⟨113840934785890076926091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303575826095706871802909 113840934785890076926091)
            ·
              refine ⟨170761402178835115389137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113840934785890076926091 170761402178835115389137)
              ·
                refine ⟨128071051634126336541853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170761402178835115389137 128071051634126336541853)
                ·
                  refine ⟨48026644362797376203195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128071051634126336541853 48026644362797376203195)
                  ·
                    rfl

theorem cell20_105223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 3].length) (baseStart_105223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105223 prefixEnd_105223 := by exact prefixLift 105223
  have htrace : WordTrace (prefixWord ++ tailWord_105223) baseStart_105223 baseEnd_105223 := by
    simpa [prefixWord, tailWord_105223, baseEnd_105223] using wordTrace_append hprefix tailTrace_105223
  have hstable : (prefixWord ++ tailWord_105223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105223).length < 2 ^ (prefixWord ++ tailWord_105223).sum := by decide
  have hdescent : baseEnd_105223 < baseStart_105223 := by decide
  rcases family_descends (prefixWord ++ tailWord_105223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105279 : List Nat := [1, 1, 2, 2, 5, 1, 8]
def baseStart_105279 : Nat := 118140960795 + 105279 * 2 ^ 59
def prefixEnd_105279 : Nat := 4983230072969 + 3 ^ 40 * 105279 * 2
def baseEnd_105279 : Nat := 5339133809856674481811

theorem tailTrace_105279 : CollatzResearch.WordTrace tailWord_105279 prefixEnd_105279 5339133809856674481811 := by
  unfold tailWord_105279
  simp only [CollatzResearch.WordTrace]
  refine ⟨3839840585599638066830891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2559893723733092044553927 3839840585599638066830891)
  ·
    refine ⟨5759760878399457100246337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3839840585599638066830891 5759760878399457100246337)
    ·
      refine ⟨4319820658799592825184753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5759760878399457100246337 4319820658799592825184753)
      ·
        refine ⟨3239865494099694618888565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4319820658799592825184753 3239865494099694618888565)
        ·
          refine ⟨303737390071846370520803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3239865494099694618888565 303737390071846370520803)
          ·
            refine ⟨455606085107769555781205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303737390071846370520803 455606085107769555781205)
            ·
              refine ⟨5339133809856674481811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 455606085107769555781205 5339133809856674481811)
              ·
                rfl

theorem cell20_105279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 8].length) (baseStart_105279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105279 prefixEnd_105279 := by exact prefixLift 105279
  have htrace : WordTrace (prefixWord ++ tailWord_105279) baseStart_105279 baseEnd_105279 := by
    simpa [prefixWord, tailWord_105279, baseEnd_105279] using wordTrace_append hprefix tailTrace_105279
  have hstable : (prefixWord ++ tailWord_105279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105279).length < 2 ^ (prefixWord ++ tailWord_105279).sum := by decide
  have hdescent : baseEnd_105279 < baseStart_105279 := by decide
  rcases family_descends (prefixWord ++ tailWord_105279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105289 : List Nat := [1, 2, 1, 1, 2, 7, 1, 1, 4]
def baseStart_105289 : Nat := 118140960795 + 105289 * 2 ^ 59
def prefixEnd_105289 : Nat := 4983230072969 + 3 ^ 40 * 105289 * 2
def baseEnd_105289 : Nat := 48056768561194480002925

theorem tailTrace_105289 : CollatzResearch.WordTrace tailWord_105289 prefixEnd_105289 48056768561194480002925 := by
  unfold tailWord_105289
  simp only [CollatzResearch.WordTrace]
  refine ⟨3840205315563409774694921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2560136877042273183129947 3840205315563409774694921)
  ·
    refine ⟨2880153986672557331021191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3840205315563409774694921 2880153986672557331021191)
    ·
      refine ⟨4320230980008835996531787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2880153986672557331021191 4320230980008835996531787)
      ·
        refine ⟨6480346470013253994797681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4320230980008835996531787 6480346470013253994797681)
        ·
          refine ⟨4860259852509940496098261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6480346470013253994797681 4860259852509940496098261)
          ·
            refine ⟨113912340293201730377303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4860259852509940496098261 113912340293201730377303)
            ·
              refine ⟨170868510439802595565955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113912340293201730377303 170868510439802595565955)
              ·
                refine ⟨256302765659703893348933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170868510439802595565955 256302765659703893348933)
                ·
                  refine ⟨48056768561194480002925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 256302765659703893348933 48056768561194480002925)
                  ·
                    rfl

theorem cell20_105289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 4].length) (baseStart_105289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105289 prefixEnd_105289 := by exact prefixLift 105289
  have htrace : WordTrace (prefixWord ++ tailWord_105289) baseStart_105289 baseEnd_105289 := by
    simpa [prefixWord, tailWord_105289, baseEnd_105289] using wordTrace_append hprefix tailTrace_105289
  have hstable : (prefixWord ++ tailWord_105289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105289).length < 2 ^ (prefixWord ++ tailWord_105289).sum := by decide
  have hdescent : baseEnd_105289 < baseStart_105289 := by decide
  rcases family_descends (prefixWord ++ tailWord_105289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105317 : List Nat := [1, 3, 1, 3, 1, 1, 4, 6]
def baseStart_105317 : Nat := 118140960795 + 105317 * 2 ^ 59
def prefixEnd_105317 : Nat := 4983230072969 + 3 ^ 40 * 105317 * 2
def baseEnd_105317 : Nat := 16023182841383609023159

theorem tailTrace_105317 : CollatzResearch.WordTrace tailWord_105317 prefixEnd_105317 16023182841383609023159 := by
  unfold tailWord_105317
  simp only [CollatzResearch.WordTrace]
  refine ⟨3841226559461970556714205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2560817706307980371142803 3841226559461970556714205)
  ·
    refine ⟨1440459959798238958767827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3841226559461970556714205 1440459959798238958767827)
    ·
      refine ⟨2160689939697358438151741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1440459959798238958767827 2160689939697358438151741)
      ·
        refine ⟨810258727386509414306903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2160689939697358438151741 810258727386509414306903)
        ·
          refine ⟨1215388091079764121460355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810258727386509414306903 1215388091079764121460355)
          ·
            refine ⟨1823082136619646182190533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215388091079764121460355 1823082136619646182190533)
            ·
              refine ⟨341827900616183659160725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1823082136619646182190533 341827900616183659160725)
              ·
                refine ⟨16023182841383609023159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 341827900616183659160725 16023182841383609023159)
                ·
                  rfl

theorem cell20_105317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 6].length) (baseStart_105317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105317 prefixEnd_105317 := by exact prefixLift 105317
  have htrace : WordTrace (prefixWord ++ tailWord_105317) baseStart_105317 baseEnd_105317 := by
    simpa [prefixWord, tailWord_105317, baseEnd_105317] using wordTrace_append hprefix tailTrace_105317
  have hstable : (prefixWord ++ tailWord_105317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105317).length < 2 ^ (prefixWord ++ tailWord_105317).sum := by decide
  have hdescent : baseEnd_105317 < baseStart_105317 := by decide
  rcases family_descends (prefixWord ++ tailWord_105317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105334 : List Nat := [5, 1, 1, 3, 1, 9]
def baseStart_105334 : Nat := 118140960795 + 105334 * 2 ^ 59
def prefixEnd_105334 : Nat := 4983230072969 + 3 ^ 40 * 105334 * 2
def baseEnd_105334 : Nat := 1780641029162011981583

theorem tailTrace_105334 : CollatzResearch.WordTrace tailWord_105334 prefixEnd_105334 1780641029162011981583 := by
  unfold tailWord_105334
  simp only [CollatzResearch.WordTrace]
  refine ⟨240115412525023903755191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2561231066933588306722037 240115412525023903755191)
  ·
    refine ⟨360173118787535855632787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240115412525023903755191 360173118787535855632787)
    ·
      refine ⟨540259678181303783449181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360173118787535855632787 540259678181303783449181)
      ·
        refine ⟨202597379317988918793443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 540259678181303783449181 202597379317988918793443)
        ·
          refine ⟨303896068976983378190165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202597379317988918793443 303896068976983378190165)
          ·
            refine ⟨1780641029162011981583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 303896068976983378190165 1780641029162011981583)
            ·
              rfl

theorem cell20_105334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 9].length) (baseStart_105334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105334 prefixEnd_105334 := by exact prefixLift 105334
  have htrace : WordTrace (prefixWord ++ tailWord_105334) baseStart_105334 baseEnd_105334 := by
    simpa [prefixWord, tailWord_105334, baseEnd_105334] using wordTrace_append hprefix tailTrace_105334
  have hstable : (prefixWord ++ tailWord_105334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105334).length < 2 ^ (prefixWord ++ tailWord_105334).sum := by decide
  have hdescent : baseEnd_105334 < baseStart_105334 := by decide
  rcases family_descends (prefixWord ++ tailWord_105334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105341 : List Nat := [1, 4, 1, 1, 2, 1, 3, 4, 3]
def baseStart_105341 : Nat := 118140960795 + 105341 * 2 ^ 59
def prefixEnd_105341 : Nat := 4983230072969 + 3 ^ 40 * 105341 * 2
def baseEnd_105341 : Nat := 48080502778113410269379

theorem tailTrace_105341 : CollatzResearch.WordTrace tailWord_105341 prefixEnd_105341 48080502778113410269379 := by
  unfold tailWord_105341
  simp only [CollatzResearch.WordTrace]
  refine ⟨3842101911375022655587877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2561401274250015103725251 3842101911375022655587877)
  ·
    refine ⟨720394108382816747922727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3842101911375022655587877 720394108382816747922727)
    ·
      refine ⟨1080591162574225121884091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 720394108382816747922727 1080591162574225121884091)
      ·
        refine ⟨1620886743861337682826137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1080591162574225121884091 1620886743861337682826137)
        ·
          refine ⟨1215665057896003262119603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1620886743861337682826137 1215665057896003262119603)
          ·
            refine ⟨1823497586844004893179405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215665057896003262119603 1823497586844004893179405)
            ·
              refine ⟨683811595066501834942277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1823497586844004893179405 683811595066501834942277)
              ·
                refine ⟨128214674074969094051677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 683811595066501834942277 128214674074969094051677)
                ·
                  refine ⟨48080502778113410269379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128214674074969094051677 48080502778113410269379)
                  ·
                    rfl

theorem cell20_105341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_105341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105341 prefixEnd_105341 := by exact prefixLift 105341
  have htrace : WordTrace (prefixWord ++ tailWord_105341) baseStart_105341 baseEnd_105341 := by
    simpa [prefixWord, tailWord_105341, baseEnd_105341] using wordTrace_append hprefix tailTrace_105341
  have hstable : (prefixWord ++ tailWord_105341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105341).length < 2 ^ (prefixWord ++ tailWord_105341).sum := by decide
  have hdescent : baseEnd_105341 < baseStart_105341 := by decide
  rcases family_descends (prefixWord ++ tailWord_105341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105348 : List Nat := [2, 3, 2, 1, 1, 1, 1, 5, 4]
def baseStart_105348 : Nat := 118140960795 + 105348 * 2 ^ 59
def prefixEnd_105348 : Nat := 4983230072969 + 3 ^ 40 * 105348 * 2
def baseEnd_105348 : Nat := 48083697768852497036017

theorem tailTrace_105348 : CollatzResearch.WordTrace tailWord_105348 prefixEnd_105348 48083697768852497036017 := by
  unfold tailWord_105348
  simp only [CollatzResearch.WordTrace]
  refine ⟨1921178611174831425546349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2561571481566441900728465 1921178611174831425546349)
  ·
    refine ⟨720441979190561784579881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1921178611174831425546349 720441979190561784579881)
    ·
      refine ⟨540331484392921338434911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 720441979190561784579881 540331484392921338434911)
      ·
        refine ⟨810497226589382007652367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540331484392921338434911 810497226589382007652367)
        ·
          refine ⟨1215745839884073011478551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810497226589382007652367 1215745839884073011478551)
          ·
            refine ⟨1823618759826109517217827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215745839884073011478551 1823618759826109517217827)
            ·
              refine ⟨2735428139739164275826741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1823618759826109517217827 2735428139739164275826741)
              ·
                refine ⟨256446388100546650858757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2735428139739164275826741 256446388100546650858757)
                ·
                  refine ⟨48083697768852497036017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 256446388100546650858757 48083697768852497036017)
                  ·
                    rfl

theorem cell20_105348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_105348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105348 prefixEnd_105348 := by exact prefixLift 105348
  have htrace : WordTrace (prefixWord ++ tailWord_105348) baseStart_105348 baseEnd_105348 := by
    simpa [prefixWord, tailWord_105348, baseEnd_105348] using wordTrace_append hprefix tailTrace_105348
  have hstable : (prefixWord ++ tailWord_105348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105348).length < 2 ^ (prefixWord ++ tailWord_105348).sum := by decide
  have hdescent : baseEnd_105348 < baseStart_105348 := by decide
  rcases family_descends (prefixWord ++ tailWord_105348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105355 : List Nat := [1, 1, 1, 1, 4, 2, 5, 5]
def baseStart_105355 : Nat := 118140960795 + 105355 * 2 ^ 59
def prefixEnd_105355 : Nat := 4983230072969 + 3 ^ 40 * 105355 * 2
def baseEnd_105355 : Nat := 16028964253197194600885

theorem tailTrace_105355 : CollatzResearch.WordTrace tailWord_105355 prefixEnd_105355 16028964253197194600885 := by
  unfold tailWord_105355
  simp only [CollatzResearch.WordTrace]
  refine ⟨3842612533324303046597519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2561741688882868697731679 3842612533324303046597519)
  ·
    refine ⟨5763918799986454569896279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3842612533324303046597519 5763918799986454569896279)
    ·
      refine ⟨8645878199979681854844419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5763918799986454569896279 8645878199979681854844419)
      ·
        refine ⟨12968817299969522782266629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8645878199979681854844419 12968817299969522782266629)
        ·
          refine ⟨2431653243744285521674993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12968817299969522782266629 2431653243744285521674993)
          ·
            refine ⟨1823739932808214141256245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2431653243744285521674993 1823739932808214141256245)
            ·
              refine ⟨170975618700770075742773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1823739932808214141256245 170975618700770075742773)
              ·
                refine ⟨16028964253197194600885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 170975618700770075742773 16028964253197194600885)
                ·
                  rfl

theorem cell20_105355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 5].length) (baseStart_105355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105355 prefixEnd_105355 := by exact prefixLift 105355
  have htrace : WordTrace (prefixWord ++ tailWord_105355) baseStart_105355 baseEnd_105355 := by
    simpa [prefixWord, tailWord_105355, baseEnd_105355] using wordTrace_append hprefix tailTrace_105355
  have hstable : (prefixWord ++ tailWord_105355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105355).length < 2 ^ (prefixWord ++ tailWord_105355).sum := by decide
  have hdescent : baseEnd_105355 < baseStart_105355 := by decide
  rcases family_descends (prefixWord ++ tailWord_105355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105389 : List Nat := [1, 5, 2, 3, 1, 1, 7]
def baseStart_105389 : Nat := 118140960795 + 105389 * 2 ^ 59
def prefixEnd_105389 : Nat := 4983230072969 + 3 ^ 40 * 105389 * 2
def baseEnd_105389 : Nat := 5344712365115397407687

theorem tailTrace_105389 : CollatzResearch.WordTrace tailWord_105389 prefixEnd_105389 5344712365115397407687 := by
  unfold tailWord_105389
  simp only [CollatzResearch.WordTrace]
  refine ⟨3843852615201126853335221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2562568410134084568890147 3843852615201126853335221)
  ·
    refine ⟨360361182675105642500177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3843852615201126853335221 360361182675105642500177)
    ·
      refine ⟨270270887006329231875133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360361182675105642500177 270270887006329231875133)
      ·
        refine ⟨101351582627373461953175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270270887006329231875133 101351582627373461953175)
        ·
          refine ⟨152027373941060192929763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101351582627373461953175 152027373941060192929763)
          ·
            refine ⟨228041060911590289394645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152027373941060192929763 228041060911590289394645)
            ·
              refine ⟨5344712365115397407687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 228041060911590289394645 5344712365115397407687)
              ·
                rfl

theorem cell20_105389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 7].length) (baseStart_105389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105389 prefixEnd_105389 := by exact prefixLift 105389
  have htrace : WordTrace (prefixWord ++ tailWord_105389) baseStart_105389 baseEnd_105389 := by
    simpa [prefixWord, tailWord_105389, baseEnd_105389] using wordTrace_append hprefix tailTrace_105389
  have hstable : (prefixWord ++ tailWord_105389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105389).length < 2 ^ (prefixWord ++ tailWord_105389).sum := by decide
  have hdescent : baseEnd_105389 < baseStart_105389 := by decide
  rcases family_descends (prefixWord ++ tailWord_105389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105437 : List Nat := [1, 4, 3, 1, 2, 3, 1, 3, 2]
def baseStart_105437 : Nat := 118140960795 + 105437 * 2 ^ 59
def prefixEnd_105437 : Nat := 4983230072969 + 3 ^ 40 * 105437 * 2
def baseEnd_105437 : Nat := 48124319793963743068987

theorem tailTrace_105437 : CollatzResearch.WordTrace tailWord_105437 prefixEnd_105437 48124319793963743068987 := by
  unfold tailWord_105437
  simp only [CollatzResearch.WordTrace]
  refine ⟨3845603319027231051082565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2563735546018154034055043 3845603319027231051082565)
  ·
    refine ⟨721050622317605822077981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3845603319027231051082565 721050622317605822077981)
    ·
      refine ⟨270393983369102183279243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 721050622317605822077981 270393983369102183279243)
      ·
        refine ⟨405590975053653274918865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270393983369102183279243 405590975053653274918865)
        ·
          refine ⟨304193231290239956189149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405590975053653274918865 304193231290239956189149)
          ·
            refine ⟨114072461733839983570931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304193231290239956189149 114072461733839983570931)
            ·
              refine ⟨171108692600759975356397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114072461733839983570931 171108692600759975356397)
              ·
                refine ⟨64165759725284990758649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171108692600759975356397 64165759725284990758649)
                ·
                  refine ⟨48124319793963743068987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64165759725284990758649 48124319793963743068987)
                  ·
                    rfl

theorem cell20_105437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_105437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105437 prefixEnd_105437 := by exact prefixLift 105437
  have htrace : WordTrace (prefixWord ++ tailWord_105437) baseStart_105437 baseEnd_105437 := by
    simpa [prefixWord, tailWord_105437, baseEnd_105437] using wordTrace_append hprefix tailTrace_105437
  have hstable : (prefixWord ++ tailWord_105437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105437).length < 2 ^ (prefixWord ++ tailWord_105437).sum := by decide
  have hdescent : baseEnd_105437 < baseStart_105437 := by decide
  rcases family_descends (prefixWord ++ tailWord_105437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105559 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 8]
def baseStart_105559 : Nat := 118140960795 + 105559 * 2 ^ 59
def prefixEnd_105559 : Nat := 4983230072969 + 3 ^ 40 * 105559 * 2
def baseEnd_105559 : Nat := 48180003918273541001821

theorem tailTrace_105559 : CollatzResearch.WordTrace tailWord_105559 prefixEnd_105559 48180003918273541001821 := by
  unfold tailWord_105559
  simp only [CollatzResearch.WordTrace]
  refine ⟨3850053024585245887023731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2566702016390163924682487 3850053024585245887023731)
  ·
    refine ⟨5775079536877868830535597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3850053024585245887023731 5775079536877868830535597)
    ·
      refine ⟨2165654826329200811450849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5775079536877868830535597 2165654826329200811450849)
      ·
        refine ⟨1624241119746900608588137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2165654826329200811450849 1624241119746900608588137)
        ·
          refine ⟨1218180839810175456441103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1624241119746900608588137 1218180839810175456441103)
          ·
            refine ⟨1827271259715263184661655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218180839810175456441103 1827271259715263184661655)
            ·
              refine ⟨2740906889572894776992483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1827271259715263184661655 2740906889572894776992483)
              ·
                refine ⟨4111360334359342165488725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2740906889572894776992483 4111360334359342165488725)
                ·
                  refine ⟨48180003918273541001821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4111360334359342165488725 48180003918273541001821)
                  ·
                    rfl

theorem cell20_105559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_105559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105559 prefixEnd_105559 := by exact prefixLift 105559
  have htrace : WordTrace (prefixWord ++ tailWord_105559) baseStart_105559 baseEnd_105559 := by
    simpa [prefixWord, tailWord_105559, baseEnd_105559] using wordTrace_append hprefix tailTrace_105559
  have hstable : (prefixWord ++ tailWord_105559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105559).length < 2 ^ (prefixWord ++ tailWord_105559).sum := by decide
  have hdescent : baseEnd_105559 < baseStart_105559 := by decide
  rcases family_descends (prefixWord ++ tailWord_105559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105569 : List Nat := [1, 2, 3, 1, 1, 2, 5, 2, 3]
def baseStart_105569 : Nat := 118140960795 + 105569 * 2 ^ 59
def prefixEnd_105569 : Nat := 4983230072969 + 3 ^ 40 * 105569 * 2
def baseEnd_105569 : Nat := 48184568190757950668447

theorem tailTrace_105569 : CollatzResearch.WordTrace tailWord_105569 prefixEnd_105569 48184568190757950668447 := by
  unfold tailWord_105569
  simp only [CollatzResearch.WordTrace]
  refine ⟨3850417754549017594887761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2566945169699345063258507 3850417754549017594887761)
  ·
    refine ⟨2887813315911763196165821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3850417754549017594887761 2887813315911763196165821)
    ·
      refine ⟨1082929993466911198562183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2887813315911763196165821 1082929993466911198562183)
      ·
        refine ⟨1624394990200366797843275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082929993466911198562183 1624394990200366797843275)
        ·
          refine ⟨2436592485300550196764913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1624394990200366797843275 2436592485300550196764913)
          ·
            refine ⟨1827444363975412647573685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2436592485300550196764913 1827444363975412647573685)
            ·
              refine ⟨171322909122694935710033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1827444363975412647573685 171322909122694935710033)
              ·
                refine ⟨128492181842021201782525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171322909122694935710033 128492181842021201782525)
                ·
                  refine ⟨48184568190757950668447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128492181842021201782525 48184568190757950668447)
                  ·
                    rfl

theorem cell20_105569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_105569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105569 prefixEnd_105569 := by exact prefixLift 105569
  have htrace : WordTrace (prefixWord ++ tailWord_105569) baseStart_105569 baseEnd_105569 := by
    simpa [prefixWord, tailWord_105569, baseEnd_105569] using wordTrace_append hprefix tailTrace_105569
  have hstable : (prefixWord ++ tailWord_105569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105569).length < 2 ^ (prefixWord ++ tailWord_105569).sum := by decide
  have hdescent : baseEnd_105569 < baseStart_105569 := by decide
  rcases family_descends (prefixWord ++ tailWord_105569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105586 : List Nat := [3, 2, 1, 2, 2, 1, 5, 1, 3]
def baseStart_105586 : Nat := 118140960795 + 105586 * 2 ^ 59
def prefixEnd_105586 : Nat := 4983230072969 + 3 ^ 40 * 105586 * 2
def baseEnd_105586 : Nat := 48192327453981447101711

theorem tailTrace_105586 : CollatzResearch.WordTrace tailWord_105586 prefixEnd_105586 48192327453981447101711 := by
  unfold tailWord_105586
  simp only [CollatzResearch.WordTrace]
  refine ⟨962759448871857374564153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2567358530324952998837741 962759448871857374564153)
  ·
    refine ⟨722069586653893030923115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 962759448871857374564153 722069586653893030923115)
    ·
      refine ⟨1083104379980839546384673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 722069586653893030923115 1083104379980839546384673)
      ·
        refine ⟨812328284985629659788505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1083104379980839546384673 812328284985629659788505)
        ·
          refine ⟨609246213739222244841379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 812328284985629659788505 609246213739222244841379)
          ·
            refine ⟨913869320608833367262069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609246213739222244841379 913869320608833367262069)
            ·
              refine ⟨85675248807078128180819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 913869320608833367262069 85675248807078128180819)
              ·
                refine ⟨128512873210617192271229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85675248807078128180819 128512873210617192271229)
                ·
                  refine ⟨48192327453981447101711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128512873210617192271229 48192327453981447101711)
                  ·
                    rfl

theorem cell20_105586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_105586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105586 prefixEnd_105586 := by exact prefixLift 105586
  have htrace : WordTrace (prefixWord ++ tailWord_105586) baseStart_105586 baseEnd_105586 := by
    simpa [prefixWord, tailWord_105586, baseEnd_105586] using wordTrace_append hprefix tailTrace_105586
  have hstable : (prefixWord ++ tailWord_105586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105586).length < 2 ^ (prefixWord ++ tailWord_105586).sum := by decide
  have hdescent : baseEnd_105586 < baseStart_105586 := by decide
  rcases family_descends (prefixWord ++ tailWord_105586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105693 : List Nat := [1, 4, 3, 2, 2, 2, 1, 5]
def baseStart_105693 : Nat := 118140960795 + 105693 * 2 ^ 59
def prefixEnd_105693 : Nat := 4983230072969 + 3 ^ 40 * 105693 * 2
def baseEnd_105693 : Nat := 16080388389854876844869

theorem tailTrace_105693 : CollatzResearch.WordTrace tailWord_105693 prefixEnd_105693 16080388389854876844869 := by
  unfold tailWord_105693
  simp only [CollatzResearch.WordTrace]
  refine ⟨3854940406099786772401733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2569960270733191181601155 3854940406099786772401733)
  ·
    refine ⟨722801326143710019825325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3854940406099786772401733 722801326143710019825325)
    ·
      refine ⟨271050497303891257434497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 722801326143710019825325 271050497303891257434497)
      ·
        refine ⟨203287872977918443075873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271050497303891257434497 203287872977918443075873)
        ·
          refine ⟨152465904733438832306905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203287872977918443075873 152465904733438832306905)
          ·
            refine ⟨114349428550079124230179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152465904733438832306905 114349428550079124230179)
            ·
              refine ⟨171524142825118686345269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114349428550079124230179 171524142825118686345269)
              ·
                refine ⟨16080388389854876844869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 171524142825118686345269 16080388389854876844869)
                ·
                  rfl

theorem cell20_105693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 5].length) (baseStart_105693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105693 prefixEnd_105693 := by exact prefixLift 105693
  have htrace : WordTrace (prefixWord ++ tailWord_105693) baseStart_105693 baseEnd_105693 := by
    simpa [prefixWord, tailWord_105693, baseEnd_105693] using wordTrace_append hprefix tailTrace_105693
  have hstable : (prefixWord ++ tailWord_105693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105693).length < 2 ^ (prefixWord ++ tailWord_105693).sum := by decide
  have hdescent : baseEnd_105693 < baseStart_105693 := by decide
  rcases family_descends (prefixWord ++ tailWord_105693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105697 : List Nat := [1, 2, 3, 1, 3, 2, 3, 5]
def baseStart_105697 : Nat := 118140960795 + 105697 * 2 ^ 59
def prefixEnd_105697 : Nat := 4983230072969 + 3 ^ 40 * 105697 * 2
def baseEnd_105697 : Nat := 16080996959519464800419

theorem tailTrace_105697 : CollatzResearch.WordTrace tailWord_105697 prefixEnd_105697 16080996959519464800419 := by
  unfold tailWord_105697
  simp only [CollatzResearch.WordTrace]
  refine ⟨3855086298085295455547345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2570057532056863637031563 3855086298085295455547345)
  ·
    refine ⟨2891314723563971591660509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3855086298085295455547345 2891314723563971591660509)
    ·
      refine ⟨1084243021336489346872691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2891314723563971591660509 1084243021336489346872691)
      ·
        refine ⟨1626364532004734020309037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084243021336489346872691 1626364532004734020309037)
        ·
          refine ⟨609886699501775257615889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1626364532004734020309037 609886699501775257615889)
          ·
            refine ⟨457415024626331443211917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609886699501775257615889 457415024626331443211917)
            ·
              refine ⟨171530634234874291204469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 457415024626331443211917 171530634234874291204469)
              ·
                refine ⟨16080996959519464800419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 171530634234874291204469 16080996959519464800419)
                ·
                  rfl

theorem cell20_105697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 5].length) (baseStart_105697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105697 prefixEnd_105697 := by exact prefixLift 105697
  have htrace : WordTrace (prefixWord ++ tailWord_105697) baseStart_105697 baseEnd_105697 := by
    simpa [prefixWord, tailWord_105697, baseEnd_105697] using wordTrace_append hprefix tailTrace_105697
  have hstable : (prefixWord ++ tailWord_105697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105697).length < 2 ^ (prefixWord ++ tailWord_105697).sum := by decide
  have hdescent : baseEnd_105697 < baseStart_105697 := by decide
  rcases family_descends (prefixWord ++ tailWord_105697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105724 : List Nat := [2, 2, 2, 1, 5, 1, 2, 3, 2]
def baseStart_105724 : Nat := 118140960795 + 105724 * 2 ^ 59
def prefixEnd_105724 : Nat := 4983230072969 + 3 ^ 40 * 105724 * 2
def baseEnd_105724 : Nat := 48255314414266300501147

theorem tailTrace_105724 : CollatzResearch.WordTrace tailWord_105724 prefixEnd_105724 48255314414266300501147 := by
  unfold tailWord_105724
  simp only [CollatzResearch.WordTrace]
  refine ⟨1928035534493739533390113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2570714045991652711186817 1928035534493739533390113)
  ·
    refine ⟨1446026650870304650042585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1928035534493739533390113 1446026650870304650042585)
    ·
      refine ⟨1084519988152728487531939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1446026650870304650042585 1084519988152728487531939)
      ·
        refine ⟨1626779982229092731297909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084519988152728487531939 1626779982229092731297909)
        ·
          refine ⟨152510623333977443559179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1626779982229092731297909 152510623333977443559179)
          ·
            refine ⟨228765935000966165338769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152510623333977443559179 228765935000966165338769)
            ·
              refine ⟨171574451250724624004077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228765935000966165338769 171574451250724624004077)
              ·
                refine ⟨64340419219021734001529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171574451250724624004077 64340419219021734001529)
                ·
                  refine ⟨48255314414266300501147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64340419219021734001529 48255314414266300501147)
                  ·
                    rfl

theorem cell20_105724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_105724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105724 prefixEnd_105724 := by exact prefixLift 105724
  have htrace : WordTrace (prefixWord ++ tailWord_105724) baseStart_105724 baseEnd_105724 := by
    simpa [prefixWord, tailWord_105724, baseEnd_105724] using wordTrace_append hprefix tailTrace_105724
  have hstable : (prefixWord ++ tailWord_105724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105724).length < 2 ^ (prefixWord ++ tailWord_105724).sum := by decide
  have hdescent : baseEnd_105724 < baseStart_105724 := by decide
  rcases family_descends (prefixWord ++ tailWord_105724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105804 : List Nat := [2, 2, 1, 3, 2, 2, 3, 1, 4]
def baseStart_105804 : Nat := 118140960795 + 105804 * 2 ^ 59
def prefixEnd_105804 : Nat := 4983230072969 + 3 ^ 40 * 105804 * 2
def baseEnd_105804 : Nat := 48291828594141577834153

theorem tailTrace_105804 : CollatzResearch.WordTrace tailWord_105804 prefixEnd_105804 48291828594141577834153 := by
  unfold tailWord_105804
  simp only [CollatzResearch.WordTrace]
  refine ⟨1929494454348826364846233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2572659272465101819794977 1929494454348826364846233)
  ·
    refine ⟨1447120840761619773634675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1929494454348826364846233 1447120840761619773634675)
    ·
      refine ⟨2170681261142429660452013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1447120840761619773634675 2170681261142429660452013)
      ·
        refine ⟨814005472928411122669505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2170681261142429660452013 814005472928411122669505)
        ·
          refine ⟨610504104696308342002129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 814005472928411122669505 610504104696308342002129)
          ·
            refine ⟨457878078522231256501597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 610504104696308342002129 457878078522231256501597)
            ·
              refine ⟨171704279445836721188099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 457878078522231256501597 171704279445836721188099)
              ·
                refine ⟨257556419168755081782149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171704279445836721188099 257556419168755081782149)
                ·
                  refine ⟨48291828594141577834153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 257556419168755081782149 48291828594141577834153)
                  ·
                    rfl

theorem cell20_105804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_105804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105804 prefixEnd_105804 := by exact prefixLift 105804
  have htrace : WordTrace (prefixWord ++ tailWord_105804) baseStart_105804 baseEnd_105804 := by
    simpa [prefixWord, tailWord_105804, baseEnd_105804] using wordTrace_append hprefix tailTrace_105804
  have hstable : (prefixWord ++ tailWord_105804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105804).length < 2 ^ (prefixWord ++ tailWord_105804).sum := by decide
  have hdescent : baseEnd_105804 < baseStart_105804 := by decide
  rcases family_descends (prefixWord ++ tailWord_105804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105825 : List Nat := [1, 2, 3, 1, 1, 1, 1, 6, 4]
def baseStart_105825 : Nat := 118140960795 + 105825 * 2 ^ 59
def prefixEnd_105825 : Nat := 4983230072969 + 3 ^ 40 * 105825 * 2
def baseEnd_105825 : Nat := 48301413566358838134067

theorem tailTrace_105825 : CollatzResearch.WordTrace tailWord_105825 prefixEnd_105825 48301413566358838134067 := by
  unfold tailWord_105825
  simp only [CollatzResearch.WordTrace]
  refine ⟨3859754841621573316206929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2573169894414382210804619 3859754841621573316206929)
  ·
    refine ⟨2894816131216179987155197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3859754841621573316206929 2894816131216179987155197)
    ·
      refine ⟨1085556049206067495183199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2894816131216179987155197 1085556049206067495183199)
      ·
        refine ⟨1628334073809101242774799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1085556049206067495183199 1628334073809101242774799)
        ·
          refine ⟨2442501110713651864162199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628334073809101242774799 2442501110713651864162199)
          ·
            refine ⟨3663751666070477796243299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2442501110713651864162199 3663751666070477796243299)
            ·
              refine ⟨5495627499105716694364949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3663751666070477796243299 5495627499105716694364949)
              ·
                refine ⟨257607539020580470048357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5495627499105716694364949 257607539020580470048357)
                ·
                  refine ⟨48301413566358838134067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 257607539020580470048357 48301413566358838134067)
                  ·
                    rfl

theorem cell20_105825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_105825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105825 prefixEnd_105825 := by exact prefixLift 105825
  have htrace : WordTrace (prefixWord ++ tailWord_105825) baseStart_105825 baseEnd_105825 := by
    simpa [prefixWord, tailWord_105825, baseEnd_105825] using wordTrace_append hprefix tailTrace_105825
  have hstable : (prefixWord ++ tailWord_105825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105825).length < 2 ^ (prefixWord ++ tailWord_105825).sum := by decide
  have hdescent : baseEnd_105825 < baseStart_105825 := by decide
  rcases family_descends (prefixWord ++ tailWord_105825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105859 : List Nat := [1, 1, 1, 3, 5, 2, 1, 4, 2]
def baseStart_105859 : Nat := 118140960795 + 105859 * 2 ^ 59
def prefixEnd_105859 : Nat := 4983230072969 + 3 ^ 40 * 105859 * 2
def baseEnd_105859 : Nat := 48316932092805831000595

theorem tailTrace_105859 : CollatzResearch.WordTrace tailWord_105859 prefixEnd_105859 48316932092805831000595 := by
  unfold tailWord_105859
  simp only [CollatzResearch.WordTrace]
  refine ⟨3860994923498397122944631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2573996615665598081963087 3860994923498397122944631)
  ·
    refine ⟨5791492385247595684416947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3860994923498397122944631 5791492385247595684416947)
    ·
      refine ⟨8687238577871393526625421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5791492385247595684416947 8687238577871393526625421)
      ·
        refine ⟨3257714466701772572484533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8687238577871393526625421 3257714466701772572484533)
        ·
          refine ⟨305410731253291178670425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3257714466701772572484533 305410731253291178670425)
          ·
            refine ⟨229058048439968384002819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305410731253291178670425 229058048439968384002819)
            ·
              refine ⟨343587072659952576004229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229058048439968384002819 343587072659952576004229)
              ·
                refine ⟨64422576123741108000793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 343587072659952576004229 64422576123741108000793)
                ·
                  refine ⟨48316932092805831000595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64422576123741108000793 48316932092805831000595)
                  ·
                    rfl

theorem cell20_105859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 2].length) (baseStart_105859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105859 prefixEnd_105859 := by exact prefixLift 105859
  have htrace : WordTrace (prefixWord ++ tailWord_105859) baseStart_105859 baseEnd_105859 := by
    simpa [prefixWord, tailWord_105859, baseEnd_105859] using wordTrace_append hprefix tailTrace_105859
  have hstable : (prefixWord ++ tailWord_105859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105859).length < 2 ^ (prefixWord ++ tailWord_105859).sum := by decide
  have hdescent : baseEnd_105859 < baseStart_105859 := by decide
  rcases family_descends (prefixWord ++ tailWord_105859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105942 : List Nat := [5, 2, 1, 1, 1, 3, 1, 6]
def baseStart_105942 : Nat := 118140960795 + 105942 * 2 ^ 59
def prefixEnd_105942 : Nat := 4983230072969 + 3 ^ 40 * 105942 * 2
def baseEnd_105942 : Nat := 16118271851475477077863

theorem tailTrace_105942 : CollatzResearch.WordTrace tailWord_105942 prefixEnd_105942 16118271851475477077863 := by
  unfold tailWord_105942
  simp only [CollatzResearch.WordTrace]
  refine ⟨241501386387356393638505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2576014788131801532144053 241501386387356393638505)
  ·
    refine ⟨181126039790517295228879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241501386387356393638505 181126039790517295228879)
    ·
      refine ⟨271689059685775942843319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181126039790517295228879 271689059685775942843319)
      ·
        refine ⟨407533589528663914264979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271689059685775942843319 407533589528663914264979)
        ·
          refine ⟨611300384292995871397469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407533589528663914264979 611300384292995871397469)
          ·
            refine ⟨229237644109873451774051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 611300384292995871397469 229237644109873451774051)
            ·
              refine ⟨343856466164810177661077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229237644109873451774051 343856466164810177661077)
              ·
                refine ⟨16118271851475477077863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 343856466164810177661077 16118271851475477077863)
                ·
                  rfl

theorem cell20_105942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_105942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105942 prefixEnd_105942 := by exact prefixLift 105942
  have htrace : WordTrace (prefixWord ++ tailWord_105942) baseStart_105942 baseEnd_105942 := by
    simpa [prefixWord, tailWord_105942, baseEnd_105942] using wordTrace_append hprefix tailTrace_105942
  have hstable : (prefixWord ++ tailWord_105942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105942).length < 2 ^ (prefixWord ++ tailWord_105942).sum := by decide
  have hdescent : baseEnd_105942 < baseStart_105942 := by decide
  rcases family_descends (prefixWord ++ tailWord_105942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105973 : List Nat := [1, 3, 5, 1, 1, 1, 3, 1, 4]
def baseStart_105973 : Nat := 118140960795 + 105973 * 2 ^ 59
def prefixEnd_105973 : Nat := 4983230072969 + 3 ^ 40 * 105973 * 2
def baseEnd_105973 : Nat := 48368964799128101200129

theorem tailTrace_105973 : CollatzResearch.WordTrace tailWord_105973 prefixEnd_105973 48368964799128101200129 := by
  unfold tailWord_105973
  simp only [CollatzResearch.WordTrace]
  refine ⟨3865152845085394592594573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2576768563390263061729715 3865152845085394592594573)
  ·
    refine ⟨1449432316907022972222965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3865152845085394592594573 1449432316907022972222965)
    ·
      refine ⟨135884279710033403645903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1449432316907022972222965 135884279710033403645903)
      ·
        refine ⟨203826419565050105468855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135884279710033403645903 203826419565050105468855)
        ·
          refine ⟨305739629347575158203283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203826419565050105468855 305739629347575158203283)
          ·
            refine ⟨458609444021362737304925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305739629347575158203283 458609444021362737304925)
            ·
              refine ⟨171978541508011026489347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 458609444021362737304925 171978541508011026489347)
              ·
                refine ⟨257967812262016539734021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171978541508011026489347 257967812262016539734021)
                ·
                  refine ⟨48368964799128101200129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 257967812262016539734021 48368964799128101200129)
                  ·
                    rfl

theorem cell20_105973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_105973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_105973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_105973 prefixEnd_105973 := by exact prefixLift 105973
  have htrace : WordTrace (prefixWord ++ tailWord_105973) baseStart_105973 baseEnd_105973 := by
    simpa [prefixWord, tailWord_105973, baseEnd_105973] using wordTrace_append hprefix tailTrace_105973
  have hstable : (prefixWord ++ tailWord_105973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105973).length < 2 ^ (prefixWord ++ tailWord_105973).sum := by decide
  have hdescent : baseEnd_105973 < baseStart_105973 := by decide
  rcases family_descends (prefixWord ++ tailWord_105973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106014 : List Nat := [4, 3, 3, 1, 2, 7]
def baseStart_106014 : Nat := 118140960795 + 106014 * 2 ^ 59
def prefixEnd_106014 : Nat := 4983230072969 + 3 ^ 40 * 106014 * 2
def baseEnd_106014 : Nat := 1792136233937562253085

theorem tailTrace_106014 : CollatzResearch.WordTrace tailWord_106014 prefixEnd_106014 1792136233937562253085 := by
  unfold tailWord_106014
  simp only [CollatzResearch.WordTrace]
  refine ⟨483331029742107324354637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2577765491957905729891397 483331029742107324354637)
  ·
    refine ⟨181249136153290246632989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 483331029742107324354637 181249136153290246632989)
    ·
      refine ⟨67968426057483842487371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181249136153290246632989 67968426057483842487371)
      ·
        refine ⟨101952639086225763731057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67968426057483842487371 101952639086225763731057)
        ·
          refine ⟨76464479314669322798293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101952639086225763731057 76464479314669322798293)
          ·
            refine ⟨1792136233937562253085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 76464479314669322798293 1792136233937562253085)
            ·
              rfl

theorem cell20_106014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 7].length) (baseStart_106014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106014 prefixEnd_106014 := by exact prefixLift 106014
  have htrace : WordTrace (prefixWord ++ tailWord_106014) baseStart_106014 baseEnd_106014 := by
    simpa [prefixWord, tailWord_106014, baseEnd_106014] using wordTrace_append hprefix tailTrace_106014
  have hstable : (prefixWord ++ tailWord_106014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106014).length < 2 ^ (prefixWord ++ tailWord_106014).sum := by decide
  have hdescent : baseEnd_106014 < baseStart_106014 := by decide
  rcases family_descends (prefixWord ++ tailWord_106014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106024 : List Nat := [2, 1, 5, 2, 3, 1, 2, 2, 2]
def baseStart_106024 : Nat := 118140960795 + 106024 * 2 ^ 59
def prefixEnd_106024 : Nat := 4983230072969 + 3 ^ 40 * 106024 * 2
def baseEnd_106024 : Nat := 48392242588798590499921

theorem tailTrace_106024 : CollatzResearch.WordTrace tailWord_106024 prefixEnd_106024 48392242588798590499921 := by
  unfold tailWord_106024
  simp only [CollatzResearch.WordTrace]
  refine ⟨1933506483950315151350563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2578008645267086868467417 1933506483950315151350563)
  ·
    refine ⟨2900259725925472727025845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1933506483950315151350563 2900259725925472727025845)
    ·
      refine ⟨271899349305513068158673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2900259725925472727025845 271899349305513068158673)
      ·
        refine ⟨203924511979134801119005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271899349305513068158673 203924511979134801119005)
        ·
          refine ⟨76471691992175550419627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203924511979134801119005 76471691992175550419627)
          ·
            refine ⟨114707537988263325629441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76471691992175550419627 114707537988263325629441)
            ·
              refine ⟨86030653491197494222081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114707537988263325629441 86030653491197494222081)
              ·
                refine ⟨64522990118398120666561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86030653491197494222081 64522990118398120666561)
                ·
                  refine ⟨48392242588798590499921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64522990118398120666561 48392242588798590499921)
                  ·
                    rfl

theorem cell20_106024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 2].length) (baseStart_106024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106024 prefixEnd_106024 := by exact prefixLift 106024
  have htrace : WordTrace (prefixWord ++ tailWord_106024) baseStart_106024 baseEnd_106024 := by
    simpa [prefixWord, tailWord_106024, baseEnd_106024] using wordTrace_append hprefix tailTrace_106024
  have hstable : (prefixWord ++ tailWord_106024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106024).length < 2 ^ (prefixWord ++ tailWord_106024).sum := by decide
  have hdescent : baseEnd_106024 < baseStart_106024 := by decide
  rcases family_descends (prefixWord ++ tailWord_106024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106039 : List Nat := [1, 1, 3, 1, 2, 6, 1, 5]
def baseStart_106039 : Nat := 118140960795 + 106039 * 2 ^ 59
def prefixEnd_106039 : Nat := 4983230072969 + 3 ^ 40 * 106039 * 2
def baseEnd_106039 : Nat := 16133029665841734999953

theorem tailTrace_106039 : CollatzResearch.WordTrace tailWord_106039 prefixEnd_106039 16133029665841734999953 := by
  unfold tailWord_106039
  simp only [CollatzResearch.WordTrace]
  refine ⟨3867560062846287864497171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2578373375230858576331447 3867560062846287864497171)
  ·
    refine ⟨5801340094269431796745757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3867560062846287864497171 5801340094269431796745757)
    ·
      refine ⟨2175502535351036923779659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5801340094269431796745757 2175502535351036923779659)
      ·
        refine ⟨3263253803026555385669489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2175502535351036923779659 3263253803026555385669489)
        ·
          refine ⟨2447440352269916539252117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3263253803026555385669489 2447440352269916539252117)
          ·
            refine ⟨114723766512652337777443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2447440352269916539252117 114723766512652337777443)
            ·
              refine ⟨172085649768978506666165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114723766512652337777443 172085649768978506666165)
              ·
                refine ⟨16133029665841734999953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172085649768978506666165 16133029665841734999953)
                ·
                  rfl

theorem cell20_106039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 5].length) (baseStart_106039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106039 prefixEnd_106039 := by exact prefixLift 106039
  have htrace : WordTrace (prefixWord ++ tailWord_106039) baseStart_106039 baseEnd_106039 := by
    simpa [prefixWord, tailWord_106039, baseEnd_106039] using wordTrace_append hprefix tailTrace_106039
  have hstable : (prefixWord ++ tailWord_106039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106039).length < 2 ^ (prefixWord ++ tailWord_106039).sum := by decide
  have hdescent : baseEnd_106039 < baseStart_106039 := by decide
  rcases family_descends (prefixWord ++ tailWord_106039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106053 : List Nat := [1, 3, 1, 1, 1, 4, 3, 2, 4]
def baseStart_106053 : Nat := 118140960795 + 106053 * 2 ^ 59
def prefixEnd_106053 : Nat := 4983230072969 + 3 ^ 40 * 106053 * 2
def baseEnd_106053 : Nat := 48405478979003378533135

theorem tailTrace_106053 : CollatzResearch.WordTrace tailWord_106053 prefixEnd_106053 48405478979003378533135 := by
  unfold tailWord_106053
  simp only [CollatzResearch.WordTrace]
  refine ⟨3868070684795568255506813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2578713789863712170337875 3868070684795568255506813)
  ·
    refine ⟨1450526506798338095815055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3868070684795568255506813 1450526506798338095815055)
    ·
      refine ⟨2175789760197507143722583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1450526506798338095815055 2175789760197507143722583)
      ·
        refine ⟨3263684640296260715583875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2175789760197507143722583 3263684640296260715583875)
        ·
          refine ⟨4895526960444391073375813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3263684640296260715583875 4895526960444391073375813)
          ·
            refine ⟨917911305083323326257965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4895526960444391073375813 917911305083323326257965)
            ·
              refine ⟨344216739406246247346737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 917911305083323326257965 344216739406246247346737)
              ·
                refine ⟨258162554554684685510053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344216739406246247346737 258162554554684685510053)
                ·
                  refine ⟨48405478979003378533135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 258162554554684685510053 48405478979003378533135)
                  ·
                    rfl

theorem cell20_106053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_106053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106053 prefixEnd_106053 := by exact prefixLift 106053
  have htrace : WordTrace (prefixWord ++ tailWord_106053) baseStart_106053 baseEnd_106053 := by
    simpa [prefixWord, tailWord_106053, baseEnd_106053] using wordTrace_append hprefix tailTrace_106053
  have hstable : (prefixWord ++ tailWord_106053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106053).length < 2 ^ (prefixWord ++ tailWord_106053).sum := by decide
  have hdescent : baseEnd_106053 < baseStart_106053 := by decide
  rcases family_descends (prefixWord ++ tailWord_106053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106084 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 5]
def baseStart_106084 : Nat := 118140960795 + 106084 * 2 ^ 59
def prefixEnd_106084 : Nat := 4983230072969 + 3 ^ 40 * 106084 * 2
def baseEnd_106084 : Nat := 48419628223705048499675

theorem tailTrace_106084 : CollatzResearch.WordTrace tailWord_106084 prefixEnd_106084 48419628223705048499675 := by
  unfold tailWord_106084
  simp only [CollatzResearch.WordTrace]
  refine ⟨1934600673841630274942653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2579467565122173699923537 1934600673841630274942653)
  ·
    refine ⟨725475252690611353103495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1934600673841630274942653 725475252690611353103495)
    ·
      refine ⟨1088212879035917029655243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 725475252690611353103495 1088212879035917029655243)
      ·
        refine ⟨1632319318553875544482865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1088212879035917029655243 1632319318553875544482865)
        ·
          refine ⟨1224239488915406658362149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1632319318553875544482865 1224239488915406658362149)
          ·
            refine ⟨229544904171638748442903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1224239488915406658362149 229544904171638748442903)
            ·
              refine ⟨344317356257458122664355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229544904171638748442903 344317356257458122664355)
              ·
                refine ⟨516476034386187183996533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344317356257458122664355 516476034386187183996533)
                ·
                  refine ⟨48419628223705048499675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 516476034386187183996533 48419628223705048499675)
                  ·
                    rfl

theorem cell20_106084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_106084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106084 prefixEnd_106084 := by exact prefixLift 106084
  have htrace : WordTrace (prefixWord ++ tailWord_106084) baseStart_106084 baseEnd_106084 := by
    simpa [prefixWord, tailWord_106084, baseEnd_106084] using wordTrace_append hprefix tailTrace_106084
  have hstable : (prefixWord ++ tailWord_106084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106084).length < 2 ^ (prefixWord ++ tailWord_106084).sum := by decide
  have hdescent : baseEnd_106084 < baseStart_106084 := by decide
  rcases family_descends (prefixWord ++ tailWord_106084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106122 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_106122 : Nat := 118140960795 + 106122 * 2 ^ 59
def prefixEnd_106122 : Nat := 4983230072969 + 3 ^ 40 * 106122 * 2
def baseEnd_106122 : Nat := 48436972459145805232853

theorem tailTrace_106122 : CollatzResearch.WordTrace tailWord_106122 prefixEnd_106122 48436972459145805232853 := by
  unfold tailWord_106122
  simp only [CollatzResearch.WordTrace]
  refine ⟨967646830386398259942155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2580391547697062026512413 967646830386398259942155)
  ·
    refine ⟨1451470245579597389913233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 967646830386398259942155 1451470245579597389913233)
    ·
      refine ⟨1088602684184698042434925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1451470245579597389913233 1088602684184698042434925)
      ·
        refine ⟨408226006569261765913097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1088602684184698042434925 408226006569261765913097)
        ·
          refine ⟨306169504926946324434823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408226006569261765913097 306169504926946324434823)
          ·
            refine ⟨459254257390419486652235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306169504926946324434823 459254257390419486652235)
            ·
              refine ⟨688881386085629229978353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459254257390419486652235 688881386085629229978353)
              ·
                refine ⟨516661039564221922483765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688881386085629229978353 516661039564221922483765)
                ·
                  refine ⟨48436972459145805232853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 516661039564221922483765 48436972459145805232853)
                  ·
                    rfl

theorem cell20_106122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_106122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106122 prefixEnd_106122 := by exact prefixLift 106122
  have htrace : WordTrace (prefixWord ++ tailWord_106122) baseStart_106122 baseEnd_106122 := by
    simpa [prefixWord, tailWord_106122, baseEnd_106122] using wordTrace_append hprefix tailTrace_106122
  have hstable : (prefixWord ++ tailWord_106122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106122).length < 2 ^ (prefixWord ++ tailWord_106122).sum := by decide
  have hdescent : baseEnd_106122 < baseStart_106122 := by decide
  rcases family_descends (prefixWord ++ tailWord_106122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106132 : List Nat := [2, 4, 2, 2, 2, 2, 6]
def baseStart_106132 : Nat := 118140960795 + 106132 * 2 ^ 59
def prefixEnd_106132 : Nat := 4983230072969 + 3 ^ 40 * 106132 * 2
def baseEnd_106132 : Nat := 5382392970181134988831

theorem tailTrace_106132 : CollatzResearch.WordTrace tailWord_106132 prefixEnd_106132 5382392970181134988831 := by
  unfold tailWord_106132
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935476025754682373816325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2580634701006243165088433 1935476025754682373816325)
  ·
    refine ⟨362901754829002945090561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1935476025754682373816325 362901754829002945090561)
    ·
      refine ⟨272176316121752208817921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362901754829002945090561 272176316121752208817921)
      ·
        refine ⟨204132237091314156613441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272176316121752208817921 204132237091314156613441)
        ·
          refine ⟨153099177818485617460081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204132237091314156613441 153099177818485617460081)
          ·
            refine ⟨114824383363864213095061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153099177818485617460081 114824383363864213095061)
            ·
              refine ⟨5382392970181134988831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114824383363864213095061 5382392970181134988831)
              ·
                rfl

theorem cell20_106132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 6].length) (baseStart_106132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106132 prefixEnd_106132 := by exact prefixLift 106132
  have htrace : WordTrace (prefixWord ++ tailWord_106132) baseStart_106132 baseEnd_106132 := by
    simpa [prefixWord, tailWord_106132, baseEnd_106132] using wordTrace_append hprefix tailTrace_106132
  have hstable : (prefixWord ++ tailWord_106132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106132).length < 2 ^ (prefixWord ++ tailWord_106132).sum := by decide
  have hdescent : baseEnd_106132 < baseStart_106132 := by decide
  rcases family_descends (prefixWord ++ tailWord_106132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106136 : List Nat := [2, 1, 2, 4, 1, 2, 8]
def baseStart_106136 : Nat := 118140960795 + 106136 * 2 ^ 59
def prefixEnd_106136 : Nat := 4983230072969 + 3 ^ 40 * 106136 * 2
def baseEnd_106136 : Nat := 5382595826735997640681

theorem tailTrace_106136 : CollatzResearch.WordTrace tailWord_106136 prefixEnd_106136 5382595826735997640681 := by
  unfold tailWord_106136
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935548971747436715389131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2580731962329915620518841 1935548971747436715389131)
  ·
    refine ⟨2903323457621155073083697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1935548971747436715389131 2903323457621155073083697)
    ·
      refine ⟨2177492593215866304812773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2903323457621155073083697 2177492593215866304812773)
      ·
        refine ⟨408279861227974932152395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2177492593215866304812773 408279861227974932152395)
        ·
          refine ⟨612419791841962398228593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408279861227974932152395 612419791841962398228593)
          ·
            refine ⟨459314843881471798671445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 612419791841962398228593 459314843881471798671445)
            ·
              refine ⟨5382595826735997640681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 459314843881471798671445 5382595826735997640681)
              ·
                rfl

theorem cell20_106136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 8].length) (baseStart_106136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106136 prefixEnd_106136 := by exact prefixLift 106136
  have htrace : WordTrace (prefixWord ++ tailWord_106136) baseStart_106136 baseEnd_106136 := by
    simpa [prefixWord, tailWord_106136, baseEnd_106136] using wordTrace_append hprefix tailTrace_106136
  have hstable : (prefixWord ++ tailWord_106136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106136).length < 2 ^ (prefixWord ++ tailWord_106136).sum := by decide
  have hdescent : baseEnd_106136 < baseStart_106136 := by decide
  rcases family_descends (prefixWord ++ tailWord_106136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106184 : List Nat := [2, 1, 3, 1, 2, 2, 2, 5, 2]
def baseStart_106184 : Nat := 118140960795 + 106184 * 2 ^ 59
def prefixEnd_106184 : Nat := 4983230072969 + 3 ^ 40 * 106184 * 2
def baseEnd_106184 : Nat := 48465270948549145165933

theorem tailTrace_106184 : CollatzResearch.WordTrace tailWord_106184 prefixEnd_106184 48465270948549145165933 := by
  unfold tailWord_106184
  simp only [CollatzResearch.WordTrace]
  refine ⟨1936424323660488814262803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2581899098213985085683737 1936424323660488814262803)
  ·
    refine ⟨2904636485490733221394205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1936424323660488814262803 2904636485490733221394205)
    ·
      refine ⟨1089238682059024958022827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2904636485490733221394205 1089238682059024958022827)
      ·
        refine ⟨1633858023088537437034241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1089238682059024958022827 1633858023088537437034241)
        ·
          refine ⟨1225393517316403077775681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1633858023088537437034241 1225393517316403077775681)
          ·
            refine ⟨919045137987302308331761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1225393517316403077775681 919045137987302308331761)
            ·
              refine ⟨689283853490476731248821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 919045137987302308331761 689283853490476731248821)
              ·
                refine ⟨64620361264732193554577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 689283853490476731248821 64620361264732193554577)
                ·
                  refine ⟨48465270948549145165933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64620361264732193554577 48465270948549145165933)
                  ·
                    rfl

theorem cell20_106184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 2].length) (baseStart_106184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106184 prefixEnd_106184 := by exact prefixLift 106184
  have htrace : WordTrace (prefixWord ++ tailWord_106184) baseStart_106184 baseEnd_106184 := by
    simpa [prefixWord, tailWord_106184, baseEnd_106184] using wordTrace_append hprefix tailTrace_106184
  have hstable : (prefixWord ++ tailWord_106184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106184).length < 2 ^ (prefixWord ++ tailWord_106184).sum := by decide
  have hdescent : baseEnd_106184 < baseStart_106184 := by decide
  rcases family_descends (prefixWord ++ tailWord_106184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106201 : List Nat := [1, 2, 1, 2, 3, 3, 4, 2, 2]
def baseStart_106201 : Nat := 118140960795 + 106201 * 2 ^ 59
def prefixEnd_106201 : Nat := 4983230072969 + 3 ^ 40 * 106201 * 2
def baseEnd_106201 : Nat := 48473030211772641599197

theorem tailTrace_106201 : CollatzResearch.WordTrace tailWord_106201 prefixEnd_106201 48473030211772641599197 := by
  unfold tailWord_106201
  simp only [CollatzResearch.WordTrace]
  refine ⟨3873468688259389531894457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2582312458839593021262971 3873468688259389531894457)
  ·
    refine ⟨2905101516194542148920843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3873468688259389531894457 2905101516194542148920843)
    ·
      refine ⟨4357652274291813223381265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2905101516194542148920843 4357652274291813223381265)
      ·
        refine ⟨3268239205718859917535949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4357652274291813223381265 3268239205718859917535949)
        ·
          refine ⟨1225589702144572469075981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3268239205718859917535949 1225589702144572469075981)
          ·
            refine ⟨459596138304214675903493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1225589702144572469075981 459596138304214675903493)
            ·
              refine ⟨86174275932040251731905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 459596138304214675903493 86174275932040251731905)
              ·
                refine ⟨64630706949030188798929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86174275932040251731905 64630706949030188798929)
                ·
                  refine ⟨48473030211772641599197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64630706949030188798929 48473030211772641599197)
                  ·
                    rfl

theorem cell20_106201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 2].length) (baseStart_106201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106201 prefixEnd_106201 := by exact prefixLift 106201
  have htrace : WordTrace (prefixWord ++ tailWord_106201) baseStart_106201 baseEnd_106201 := by
    simpa [prefixWord, tailWord_106201, baseEnd_106201] using wordTrace_append hprefix tailTrace_106201
  have hstable : (prefixWord ++ tailWord_106201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106201).length < 2 ^ (prefixWord ++ tailWord_106201).sum := by decide
  have hdescent : baseEnd_106201 < baseStart_106201 := by decide
  rcases family_descends (prefixWord ++ tailWord_106201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106250 : List Nat := [3, 1, 2, 2, 1, 4, 7]
def baseStart_106250 : Nat := 118140960795 + 106250 * 2 ^ 59
def prefixEnd_106250 : Nat := 4983230072969 + 3 ^ 40 * 106250 * 2
def baseEnd_106250 : Nat := 5388377238549583218407

theorem tailTrace_106250 : CollatzResearch.WordTrace tailWord_106250 prefixEnd_106250 5388377238549583218407 := by
  unfold tailWord_106250
  simp only [CollatzResearch.WordTrace]
  refine ⟨968813966270467725107051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2583503910054580600285469 968813966270467725107051)
  ·
    refine ⟨1453220949405701587660577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 968813966270467725107051 1453220949405701587660577)
    ·
      refine ⟨1089915712054276190745433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1453220949405701587660577 1089915712054276190745433)
      ·
        refine ⟨817436784040707143059075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1089915712054276190745433 817436784040707143059075)
        ·
          refine ⟨1226155176061060714588613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817436784040707143059075 1226155176061060714588613)
          ·
            refine ⟨229904095511448883985365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1226155176061060714588613 229904095511448883985365)
            ·
              refine ⟨5388377238549583218407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 229904095511448883985365 5388377238549583218407)
              ·
                rfl

theorem cell20_106250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 7].length) (baseStart_106250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106250 prefixEnd_106250 := by exact prefixLift 106250
  have htrace : WordTrace (prefixWord ++ tailWord_106250) baseStart_106250 baseEnd_106250 := by
    simpa [prefixWord, tailWord_106250, baseEnd_106250] using wordTrace_append hprefix tailTrace_106250
  have hstable : (prefixWord ++ tailWord_106250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106250).length < 2 ^ (prefixWord ++ tailWord_106250).sum := by decide
  have hdescent : baseEnd_106250 < baseStart_106250 := by decide
  rcases family_descends (prefixWord ++ tailWord_106250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106294 : List Nat := [5, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_106294 : Nat := 118140960795 + 106294 * 2 ^ 59
def prefixEnd_106294 : Nat := 4983230072969 + 3 ^ 40 * 106294 * 2
def baseEnd_106294 : Nat := 48515477945877651498817

theorem tailTrace_106294 : CollatzResearch.WordTrace tailWord_106294 prefixEnd_106294 48515477945877651498817 := by
  unfold tailWord_106294
  simp only [CollatzResearch.WordTrace]
  refine ⟨242303792307654150939371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2584573784614977610019957 242303792307654150939371)
  ·
    refine ⟨363455688461481226409057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242303792307654150939371 363455688461481226409057)
    ·
      refine ⟨272591766346110919806793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363455688461481226409057 272591766346110919806793)
      ·
        refine ⟨204443824759583189855095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272591766346110919806793 204443824759583189855095)
        ·
          refine ⟨306665737139374784782643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204443824759583189855095 306665737139374784782643)
          ·
            refine ⟨459998605709062177173965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306665737139374784782643 459998605709062177173965)
            ·
              refine ⟨172499477140898316440237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 459998605709062177173965 172499477140898316440237)
              ·
                refine ⟨64687303927836868665089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172499477140898316440237 64687303927836868665089)
                ·
                  refine ⟨48515477945877651498817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64687303927836868665089 48515477945877651498817)
                  ·
                    rfl

theorem cell20_106294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_106294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106294 prefixEnd_106294 := by exact prefixLift 106294
  have htrace : WordTrace (prefixWord ++ tailWord_106294) baseStart_106294 baseEnd_106294 := by
    simpa [prefixWord, tailWord_106294, baseEnd_106294] using wordTrace_append hprefix tailTrace_106294
  have hstable : (prefixWord ++ tailWord_106294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106294).length < 2 ^ (prefixWord ++ tailWord_106294).sum := by decide
  have hdescent : baseEnd_106294 < baseStart_106294 := by decide
  rcases family_descends (prefixWord ++ tailWord_106294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106467 : List Nat := [1, 1, 1, 6, 1, 4, 1, 3, 2]
def baseStart_106467 : Nat := 118140960795 + 106467 * 2 ^ 59
def prefixEnd_106467 : Nat := 4983230072969 + 3 ^ 40 * 106467 * 2
def baseEnd_106467 : Nat := 48594439859857938731443

theorem tailTrace_106467 : CollatzResearch.WordTrace tailWord_106467 prefixEnd_106467 48594439859857938731443 := by
  unfold tailWord_106467
  simp only [CollatzResearch.WordTrace]
  refine ⟨3883170505295716961077655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2588780336863811307385103 3883170505295716961077655)
  ·
    refine ⟨5824755757943575441616483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3883170505295716961077655 5824755757943575441616483)
    ·
      refine ⟨8737133636915363162424725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5824755757943575441616483 8737133636915363162424725)
      ·
        refine ⟨409553139230407648238659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8737133636915363162424725 409553139230407648238659)
        ·
          refine ⟨614329708845611472357989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409553139230407648238659 614329708845611472357989)
          ·
            refine ⟨115186820408552151067123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 614329708845611472357989 115186820408552151067123)
            ·
              refine ⟨172780230612828226600685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115186820408552151067123 172780230612828226600685)
              ·
                refine ⟨64792586479810584975257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172780230612828226600685 64792586479810584975257)
                ·
                  refine ⟨48594439859857938731443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64792586479810584975257 48594439859857938731443)
                  ·
                    rfl

theorem cell20_106467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 2].length) (baseStart_106467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106467 prefixEnd_106467 := by exact prefixLift 106467
  have htrace : WordTrace (prefixWord ++ tailWord_106467) baseStart_106467 baseEnd_106467 := by
    simpa [prefixWord, tailWord_106467, baseEnd_106467] using wordTrace_append hprefix tailTrace_106467
  have hstable : (prefixWord ++ tailWord_106467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106467).length < 2 ^ (prefixWord ++ tailWord_106467).sum := by decide
  have hdescent : baseEnd_106467 < baseStart_106467 := by decide
  rcases family_descends (prefixWord ++ tailWord_106467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106478 : List Nat := [4, 1, 2, 1, 3, 1, 8]
def baseStart_106478 : Nat := 118140960795 + 106478 * 2 ^ 59
def prefixEnd_106478 : Nat := 4983230072969 + 3 ^ 40 * 106478 * 2
def baseEnd_106478 : Nat := 5399940062176754373859

theorem tailTrace_106478 : CollatzResearch.WordTrace tailWord_106478 prefixEnd_106478 5399940062176754373859 := by
  unfold tailWord_106478
  simp only [CollatzResearch.WordTrace]
  refine ⟨485446463531983229966011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2589047805503910559818725 485446463531983229966011)
  ·
    refine ⟨728169695297974844949017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 485446463531983229966011 728169695297974844949017)
    ·
      refine ⟨546127271473481133711763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 728169695297974844949017 546127271473481133711763)
      ·
        refine ⟨819190907210221700567645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546127271473481133711763 819190907210221700567645)
        ·
          refine ⟨307196590203833137712867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 819190907210221700567645 307196590203833137712867)
          ·
            refine ⟨460794885305749706569301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307196590203833137712867 460794885305749706569301)
            ·
              refine ⟨5399940062176754373859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 460794885305749706569301 5399940062176754373859)
              ·
                rfl

theorem cell20_106478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 8].length) (baseStart_106478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106478 prefixEnd_106478 := by exact prefixLift 106478
  have htrace : WordTrace (prefixWord ++ tailWord_106478) baseStart_106478 baseEnd_106478 := by
    simpa [prefixWord, tailWord_106478, baseEnd_106478] using wordTrace_append hprefix tailTrace_106478
  have hstable : (prefixWord ++ tailWord_106478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106478).length < 2 ^ (prefixWord ++ tailWord_106478).sum := by decide
  have hdescent : baseEnd_106478 < baseStart_106478 := by decide
  rcases family_descends (prefixWord ++ tailWord_106478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106536 : List Nat := [2, 1, 5, 3, 1, 1, 2, 2, 3]
def baseStart_106536 : Nat := 118140960795 + 106536 * 2 ^ 59
def prefixEnd_106536 : Nat := 4983230072969 + 3 ^ 40 * 106536 * 2
def baseEnd_106536 : Nat := 48625933340000365431161

theorem tailTrace_106536 : CollatzResearch.WordTrace tailWord_106536 prefixEnd_106536 48625933340000365431161 := by
  unfold tailWord_106536
  simp only [CollatzResearch.WordTrace]
  refine ⟨1942843571022870872669731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2590458094697161163559641 1942843571022870872669731)
  ·
    refine ⟨2914265356534306309004597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1942843571022870872669731 2914265356534306309004597)
    ·
      refine ⟨273212377175091216469181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2914265356534306309004597 273212377175091216469181)
      ·
        refine ⟨102454641440659206175943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273212377175091216469181 102454641440659206175943)
        ·
          refine ⟨153681962160988809263915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102454641440659206175943 153681962160988809263915)
          ·
            refine ⟨230522943241483213895873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153681962160988809263915 230522943241483213895873)
            ·
              refine ⟨172892207431112410421905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230522943241483213895873 172892207431112410421905)
              ·
                refine ⟨129669155573334307816429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172892207431112410421905 129669155573334307816429)
                ·
                  refine ⟨48625933340000365431161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129669155573334307816429 48625933340000365431161)
                  ·
                    rfl

theorem cell20_106536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 3].length) (baseStart_106536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106536 prefixEnd_106536 := by exact prefixLift 106536
  have htrace : WordTrace (prefixWord ++ tailWord_106536) baseStart_106536 baseEnd_106536 := by
    simpa [prefixWord, tailWord_106536, baseEnd_106536] using wordTrace_append hprefix tailTrace_106536
  have hstable : (prefixWord ++ tailWord_106536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106536).length < 2 ^ (prefixWord ++ tailWord_106536).sum := by decide
  have hdescent : baseEnd_106536 < baseStart_106536 := by decide
  rcases family_descends (prefixWord ++ tailWord_106536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106599 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 5]
def baseStart_106599 : Nat := 118140960795 + 106599 * 2 ^ 59
def prefixEnd_106599 : Nat := 4983230072969 + 3 ^ 40 * 106599 * 2
def baseEnd_106599 : Nat := 48654688256652146330903

theorem tailTrace_106599 : CollatzResearch.WordTrace tailWord_106599 prefixEnd_106599 48654688256652146330903 := by
  unfold tailWord_106599
  simp only [CollatzResearch.WordTrace]
  refine ⟨3887984940817503504882851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2591989960545002336588567 3887984940817503504882851)
  ·
    refine ⟨5831977411226255257324277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3887984940817503504882851 5831977411226255257324277)
    ·
      refine ⟨546747882302461430374151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5831977411226255257324277 546747882302461430374151)
      ·
        refine ⟨820121823453692145561227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546747882302461430374151 820121823453692145561227)
        ·
          refine ⟨1230182735180538218341841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820121823453692145561227 1230182735180538218341841)
          ·
            refine ⟨922637051385403663756381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1230182735180538218341841 922637051385403663756381)
            ·
              refine ⟨345988894269526373908643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 922637051385403663756381 345988894269526373908643)
              ·
                refine ⟨518983341404289560862965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345988894269526373908643 518983341404289560862965)
                ·
                  refine ⟨48654688256652146330903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 518983341404289560862965 48654688256652146330903)
                  ·
                    rfl

theorem cell20_106599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_106599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106599 prefixEnd_106599 := by exact prefixLift 106599
  have htrace : WordTrace (prefixWord ++ tailWord_106599) baseStart_106599 baseEnd_106599 := by
    simpa [prefixWord, tailWord_106599, baseEnd_106599] using wordTrace_append hprefix tailTrace_106599
  have hstable : (prefixWord ++ tailWord_106599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106599).length < 2 ^ (prefixWord ++ tailWord_106599).sum := by decide
  have hdescent : baseEnd_106599 < baseStart_106599 := by decide
  rcases family_descends (prefixWord ++ tailWord_106599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106602 : List Nat := [3, 1, 3, 2, 3, 1, 2, 1, 4]
def baseStart_106602 : Nat := 118140960795 + 106602 * 2 ^ 59
def prefixEnd_106602 : Nat := 4983230072969 + 3 ^ 40 * 106602 * 2
def baseEnd_106602 : Nat := 48656057538397469230891

theorem tailTrace_106602 : CollatzResearch.WordTrace tailWord_106602 prefixEnd_106602 48656057538397469230891 := by
  unfold tailWord_106602
  simp only [CollatzResearch.WordTrace]
  refine ⟨972023589951658754310515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2592062906537756678161373 972023589951658754310515)
  ·
    refine ⟨1458035384927488131465773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 972023589951658754310515 1458035384927488131465773)
    ·
      refine ⟨546763269347808049299665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1458035384927488131465773 546763269347808049299665)
      ·
        refine ⟨410072452010856036974749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546763269347808049299665 410072452010856036974749)
        ·
          refine ⟨153777169504071013865531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410072452010856036974749 153777169504071013865531)
          ·
            refine ⟨230665754256106520798297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153777169504071013865531 230665754256106520798297)
            ·
              refine ⟨172999315692079890598723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230665754256106520798297 172999315692079890598723)
              ·
                refine ⟨259498973538119835898085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172999315692079890598723 259498973538119835898085)
                ·
                  refine ⟨48656057538397469230891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 259498973538119835898085 48656057538397469230891)
                  ·
                    rfl

theorem cell20_106602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_106602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106602 prefixEnd_106602 := by exact prefixLift 106602
  have htrace : WordTrace (prefixWord ++ tailWord_106602) baseStart_106602 baseEnd_106602 := by
    simpa [prefixWord, tailWord_106602, baseEnd_106602] using wordTrace_append hprefix tailTrace_106602
  have hstable : (prefixWord ++ tailWord_106602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106602).length < 2 ^ (prefixWord ++ tailWord_106602).sum := by decide
  have hdescent : baseEnd_106602 < baseStart_106602 := by decide
  rcases family_descends (prefixWord ++ tailWord_106602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106647 : List Nat := [1, 1, 3, 3, 5, 1, 6]
def baseStart_106647 : Nat := 118140960795 + 106647 * 2 ^ 59
def prefixEnd_106647 : Nat := 4983230072969 + 3 ^ 40 * 106647 * 2
def baseEnd_106647 : Nat := 5408510751619701414523

theorem tailTrace_106647 : CollatzResearch.WordTrace tailWord_106647 prefixEnd_106647 5408510751619701414523 := by
  unfold tailWord_106647
  simp only [CollatzResearch.WordTrace]
  refine ⟨3889735644643607702630195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2593157096429071801753463 3889735644643607702630195)
  ·
    refine ⟨5834603466965411553945293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3889735644643607702630195 5834603466965411553945293)
    ·
      refine ⟨2187976300112029332729485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5834603466965411553945293 2187976300112029332729485)
      ·
        refine ⟨820491112542010999773557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2187976300112029332729485 820491112542010999773557)
        ·
          refine ⟨76921041800813531228771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 820491112542010999773557 76921041800813531228771)
          ·
            refine ⟨115381562701220296843157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76921041800813531228771 115381562701220296843157)
            ·
              refine ⟨5408510751619701414523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115381562701220296843157 5408510751619701414523)
              ·
                rfl

theorem cell20_106647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 6].length) (baseStart_106647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106647 prefixEnd_106647 := by exact prefixLift 106647
  have htrace : WordTrace (prefixWord ++ tailWord_106647) baseStart_106647 baseEnd_106647 := by
    simpa [prefixWord, tailWord_106647, baseEnd_106647] using wordTrace_append hprefix tailTrace_106647
  have hstable : (prefixWord ++ tailWord_106647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106647).length < 2 ^ (prefixWord ++ tailWord_106647).sum := by decide
  have hdescent : baseEnd_106647 < baseStart_106647 := by decide
  rcases family_descends (prefixWord ++ tailWord_106647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106657 : List Nat := [1, 2, 3, 3, 1, 3, 3, 2, 2]
def baseStart_106657 : Nat := 118140960795 + 106657 * 2 ^ 59
def prefixEnd_106657 : Nat := 4983230072969 + 3 ^ 40 * 106657 * 2
def baseEnd_106657 : Nat := 48681161037061722397333

theorem tailTrace_106657 : CollatzResearch.WordTrace tailWord_106657 prefixEnd_106657 48681161037061722397333 := by
  unfold tailWord_106657
  simp only [CollatzResearch.WordTrace]
  refine ⟨3890100374607379410494225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2593400249738252940329483 3890100374607379410494225)
  ·
    refine ⟨2917575280955534557870669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3890100374607379410494225 2917575280955534557870669)
    ·
      refine ⟨1094090730358325459201501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2917575280955534557870669 1094090730358325459201501)
      ·
        refine ⟨410284023884372047200563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1094090730358325459201501 410284023884372047200563)
        ·
          refine ⟨615426035826558070800845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410284023884372047200563 615426035826558070800845)
          ·
            refine ⟨230784763434959276550317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 615426035826558070800845 230784763434959276550317)
            ·
              refine ⟨86544286288109728706369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230784763434959276550317 86544286288109728706369)
              ·
                refine ⟨64908214716082296529777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86544286288109728706369 64908214716082296529777)
                ·
                  refine ⟨48681161037061722397333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64908214716082296529777 48681161037061722397333)
                  ·
                    rfl

theorem cell20_106657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 2].length) (baseStart_106657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106657 prefixEnd_106657 := by exact prefixLift 106657
  have htrace : WordTrace (prefixWord ++ tailWord_106657) baseStart_106657 baseEnd_106657 := by
    simpa [prefixWord, tailWord_106657, baseEnd_106657] using wordTrace_append hprefix tailTrace_106657
  have hstable : (prefixWord ++ tailWord_106657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106657).length < 2 ^ (prefixWord ++ tailWord_106657).sum := by decide
  have hdescent : baseEnd_106657 < baseStart_106657 := by decide
  rcases family_descends (prefixWord ++ tailWord_106657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106682 : List Nat := [3, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_106682 : Nat := 118140960795 + 106682 * 2 ^ 59
def prefixEnd_106682 : Nat := 4983230072969 + 3 ^ 40 * 106682 * 2
def baseEnd_106682 : Nat := 48692571718272746563897

theorem tailTrace_106682 : CollatzResearch.WordTrace tailWord_106682 prefixEnd_106682 48692571718272746563897 := by
  unfold tailWord_106682
  simp only [CollatzResearch.WordTrace]
  refine ⟨972753049879202170038575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2594008133011205786769533 972753049879202170038575)
  ·
    refine ⟨1459129574818803255057863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 972753049879202170038575 1459129574818803255057863)
    ·
      refine ⟨2188694362228204882586795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1459129574818803255057863 2188694362228204882586795)
      ·
        refine ⟨3283041543342307323880193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2188694362228204882586795 3283041543342307323880193)
        ·
          refine ⟨2462281157506730492910145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3283041543342307323880193 2462281157506730492910145)
          ·
            refine ⟨1846710868130047869682609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2462281157506730492910145 1846710868130047869682609)
            ·
              refine ⟨1385033151097535902261957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1846710868130047869682609 1385033151097535902261957)
              ·
                refine ⟨259693715830787981674117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1385033151097535902261957 259693715830787981674117)
                ·
                  refine ⟨48692571718272746563897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 259693715830787981674117 48692571718272746563897)
                  ·
                    rfl

theorem cell20_106682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_106682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106682 prefixEnd_106682 := by exact prefixLift 106682
  have htrace : WordTrace (prefixWord ++ tailWord_106682) baseStart_106682 baseEnd_106682 := by
    simpa [prefixWord, tailWord_106682, baseEnd_106682] using wordTrace_append hprefix tailTrace_106682
  have hstable : (prefixWord ++ tailWord_106682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106682).length < 2 ^ (prefixWord ++ tailWord_106682).sum := by decide
  have hdescent : baseEnd_106682 < baseStart_106682 := by decide
  rcases family_descends (prefixWord ++ tailWord_106682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106699 : List Nat := [1, 1, 1, 1, 3, 2, 4, 5, 2]
def baseStart_106699 : Nat := 118140960795 + 106699 * 2 ^ 59
def prefixEnd_106699 : Nat := 4983230072969 + 3 ^ 40 * 106699 * 2
def baseEnd_106699 : Nat := 48700330981496242997161

theorem tailTrace_106699 : CollatzResearch.WordTrace tailWord_106699 prefixEnd_106699 48700330981496242997161 := by
  unfold tailWord_106699
  simp only [CollatzResearch.WordTrace]
  refine ⟨3891632240455220583523151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2594421493636813722348767 3891632240455220583523151)
  ·
    refine ⟨5837448360682830875284727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3891632240455220583523151 5837448360682830875284727)
    ·
      refine ⟨8756172541024246312927091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5837448360682830875284727 8756172541024246312927091)
      ·
        refine ⟨13134258811536369469390637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8756172541024246312927091 13134258811536369469390637)
        ·
          refine ⟨4925347054326138551021489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13134258811536369469390637 4925347054326138551021489)
          ·
            refine ⟨3694010290744603913266117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4925347054326138551021489 3694010290744603913266117)
            ·
              refine ⟨692626929514613233737397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3694010290744603913266117 692626929514613233737397)
              ·
                refine ⟨64933774641994990662881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 692626929514613233737397 64933774641994990662881)
                ·
                  refine ⟨48700330981496242997161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64933774641994990662881 48700330981496242997161)
                  ·
                    rfl

theorem cell20_106699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 2].length) (baseStart_106699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106699 prefixEnd_106699 := by exact prefixLift 106699
  have htrace : WordTrace (prefixWord ++ tailWord_106699) baseStart_106699 baseEnd_106699 := by
    simpa [prefixWord, tailWord_106699, baseEnd_106699] using wordTrace_append hprefix tailTrace_106699
  have hstable : (prefixWord ++ tailWord_106699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106699).length < 2 ^ (prefixWord ++ tailWord_106699).sum := by decide
  have hdescent : baseEnd_106699 < baseStart_106699 := by decide
  rcases family_descends (prefixWord ++ tailWord_106699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106709 : List Nat := [1, 3, 2, 4, 2, 1, 2, 2, 3]
def baseStart_106709 : Nat := 118140960795 + 106709 * 2 ^ 59
def prefixEnd_106709 : Nat := 4983230072969 + 3 ^ 40 * 106709 * 2
def baseEnd_106709 : Nat := 48704895253980652663787

theorem tailTrace_106709 : CollatzResearch.WordTrace tailWord_106709 prefixEnd_106709 48704895253980652663787 := by
  unfold tailWord_106709
  simp only [CollatzResearch.WordTrace]
  refine ⟨3891996970418992291387181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2594664646945994860924787 3891996970418992291387181)
  ·
    refine ⟨1459498863907122109270193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3891996970418992291387181 1459498863907122109270193)
    ·
      refine ⟨1094624147930341581952645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1459498863907122109270193 1094624147930341581952645)
      ·
        refine ⟨205242027736939046616121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1094624147930341581952645 205242027736939046616121)
        ·
          refine ⟨153931520802704284962091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205242027736939046616121 153931520802704284962091)
          ·
            refine ⟨230897281204056427443137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153931520802704284962091 230897281204056427443137)
            ·
              refine ⟨173172960903042320582353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230897281204056427443137 173172960903042320582353)
              ·
                refine ⟨129879720677281740436765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173172960903042320582353 129879720677281740436765)
                ·
                  refine ⟨48704895253980652663787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129879720677281740436765 48704895253980652663787)
                  ·
                    rfl

theorem cell20_106709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_106709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106709 prefixEnd_106709 := by exact prefixLift 106709
  have htrace : WordTrace (prefixWord ++ tailWord_106709) baseStart_106709 baseEnd_106709 := by
    simpa [prefixWord, tailWord_106709, baseEnd_106709] using wordTrace_append hprefix tailTrace_106709
  have hstable : (prefixWord ++ tailWord_106709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106709).length < 2 ^ (prefixWord ++ tailWord_106709).sum := by decide
  have hdescent : baseEnd_106709 < baseStart_106709 := by decide
  rcases family_descends (prefixWord ++ tailWord_106709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106713 : List Nat := [1, 2, 1, 2, 3, 1, 3, 4, 3]
def baseStart_106713 : Nat := 118140960795 + 106713 * 2 ^ 59
def prefixEnd_106713 : Nat := 4983230072969 + 3 ^ 40 * 106713 * 2
def baseEnd_106713 : Nat := 48706720962974416530437

theorem tailTrace_106713 : CollatzResearch.WordTrace tailWord_106713 prefixEnd_106713 48706720962974416530437 := by
  unfold tailWord_106713
  simp only [CollatzResearch.WordTrace]
  refine ⟨3892142862404500974532793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2594761908269667316355195 3892142862404500974532793)
  ·
    refine ⟨2919107146803375730899595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3892142862404500974532793 2919107146803375730899595)
    ·
      refine ⟨4378660720205063596349393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2919107146803375730899595 4378660720205063596349393)
      ·
        refine ⟨3283995540153797697262045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4378660720205063596349393 3283995540153797697262045)
        ·
          refine ⟨1231498327557674136473267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3283995540153797697262045 1231498327557674136473267)
          ·
            refine ⟨1847247491336511204709901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231498327557674136473267 1847247491336511204709901)
            ·
              refine ⟨692717809251191701766213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1847247491336511204709901 692717809251191701766213)
              ·
                refine ⟨129884589234598444081165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 692717809251191701766213 129884589234598444081165)
                ·
                  refine ⟨48706720962974416530437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129884589234598444081165 48706720962974416530437)
                  ·
                    rfl

theorem cell20_106713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_106713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106713 prefixEnd_106713 := by exact prefixLift 106713
  have htrace : WordTrace (prefixWord ++ tailWord_106713) baseStart_106713 baseEnd_106713 := by
    simpa [prefixWord, tailWord_106713, baseEnd_106713] using wordTrace_append hprefix tailTrace_106713
  have hstable : (prefixWord ++ tailWord_106713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106713).length < 2 ^ (prefixWord ++ tailWord_106713).sum := by decide
  have hdescent : baseEnd_106713 < baseStart_106713 := by decide
  rcases family_descends (prefixWord ++ tailWord_106713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106720 : List Nat := [2, 1, 1, 3, 1, 3, 2, 3, 4]
def baseStart_106720 : Nat := 118140960795 + 106720 * 2 ^ 59
def prefixEnd_106720 : Nat := 4983230072969 + 3 ^ 40 * 106720 * 2
def baseEnd_106720 : Nat := 48709915953713503297075

theorem tailTrace_106720 : CollatzResearch.WordTrace tailWord_106720 prefixEnd_106720 48709915953713503297075 := by
  unfold tailWord_106720
  simp only [CollatzResearch.WordTrace]
  refine ⟨1946199086689570585018807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2594932115586094113358409 1946199086689570585018807)
  ·
    refine ⟨2919298630034355877528211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1946199086689570585018807 2919298630034355877528211)
    ·
      refine ⟨4378947945051533816292317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2919298630034355877528211 4378947945051533816292317)
      ·
        refine ⟨1642105479394325181109619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4378947945051533816292317 1642105479394325181109619)
        ·
          refine ⟨2463158219091487771664429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1642105479394325181109619 2463158219091487771664429)
          ·
            refine ⟨923684332159307914374161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2463158219091487771664429 923684332159307914374161)
            ·
              refine ⟨692763249119480935780621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 923684332159307914374161 692763249119480935780621)
              ·
                refine ⟨259786218419805350917733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 692763249119480935780621 259786218419805350917733)
                ·
                  refine ⟨48709915953713503297075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 259786218419805350917733 48709915953713503297075)
                  ·
                    rfl

theorem cell20_106720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_106720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106720 prefixEnd_106720 := by exact prefixLift 106720
  have htrace : WordTrace (prefixWord ++ tailWord_106720) baseStart_106720 baseEnd_106720 := by
    simpa [prefixWord, tailWord_106720, baseEnd_106720] using wordTrace_append hprefix tailTrace_106720
  have hstable : (prefixWord ++ tailWord_106720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106720).length < 2 ^ (prefixWord ++ tailWord_106720).sum := by decide
  have hdescent : baseEnd_106720 < baseStart_106720 := by decide
  rcases family_descends (prefixWord ++ tailWord_106720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106775 : List Nat := [1, 1, 3, 4, 1, 3, 2, 1, 4]
def baseStart_106775 : Nat := 118140960795 + 106775 * 2 ^ 59
def prefixEnd_106775 : Nat := 4983230072969 + 3 ^ 40 * 106775 * 2
def baseEnd_106775 : Nat := 48735019452377756463517

theorem tailTrace_106775 : CollatzResearch.WordTrace tailWord_106775 prefixEnd_106775 48735019452377756463517 := by
  unfold tailWord_106775
  simp only [CollatzResearch.WordTrace]
  refine ⟨3894404188179885563289779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2596269458786590375526519 3894404188179885563289779)
  ·
    refine ⟨5841606282269828344934669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3894404188179885563289779 5841606282269828344934669)
    ·
      refine ⟨2190602355851185629350501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5841606282269828344934669 2190602355851185629350501)
      ·
        refine ⟨410737941722097305503219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2190602355851185629350501 410737941722097305503219)
        ·
          refine ⟨616106912583145958254829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410737941722097305503219 616106912583145958254829)
          ·
            refine ⟨231040092218679734345561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 616106912583145958254829 231040092218679734345561)
            ·
              refine ⟨173280069164009800759171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231040092218679734345561 173280069164009800759171)
              ·
                refine ⟨259920103746014701138757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173280069164009800759171 259920103746014701138757)
                ·
                  refine ⟨48735019452377756463517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 259920103746014701138757 48735019452377756463517)
                  ·
                    rfl

theorem cell20_106775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 4].length) (baseStart_106775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106775 prefixEnd_106775 := by exact prefixLift 106775
  have htrace : WordTrace (prefixWord ++ tailWord_106775) baseStart_106775 baseEnd_106775 := by
    simpa [prefixWord, tailWord_106775, baseEnd_106775] using wordTrace_append hprefix tailTrace_106775
  have hstable : (prefixWord ++ tailWord_106775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106775).length < 2 ^ (prefixWord ++ tailWord_106775).sum := by decide
  have hdescent : baseEnd_106775 < baseStart_106775 := by decide
  rcases family_descends (prefixWord ++ tailWord_106775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106796 : List Nat := [2, 2, 1, 1, 1, 3, 4, 2, 4]
def baseStart_106796 : Nat := 118140960795 + 106796 * 2 ^ 59
def prefixEnd_106796 : Nat := 4983230072969 + 3 ^ 40 * 106796 * 2
def baseEnd_106796 : Nat := 48744604424595016763431

theorem tailTrace_106796 : CollatzResearch.WordTrace tailWord_106796 prefixEnd_106796 48744604424595016763431 := by
  unfold tailWord_106796
  simp only [CollatzResearch.WordTrace]
  refine ⟨1947585060551903074902121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2596780080735870766536161 1947585060551903074902121)
  ·
    refine ⟨1460688795413927306176591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1947585060551903074902121 1460688795413927306176591)
    ·
      refine ⟨2191033193120890959264887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1460688795413927306176591 2191033193120890959264887)
      ·
        refine ⟨3286549789681336438897331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2191033193120890959264887 3286549789681336438897331)
        ·
          refine ⟨4929824684522004658345997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3286549789681336438897331 4929824684522004658345997)
          ·
            refine ⟨1848684256695751746879749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4929824684522004658345997 1848684256695751746879749)
            ·
              refine ⟨346628298130453452539953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1848684256695751746879749 346628298130453452539953)
              ·
                refine ⟨259971223597840089404965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346628298130453452539953 259971223597840089404965)
                ·
                  refine ⟨48744604424595016763431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 259971223597840089404965 48744604424595016763431)
                  ·
                    rfl

theorem cell20_106796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_106796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106796 prefixEnd_106796 := by exact prefixLift 106796
  have htrace : WordTrace (prefixWord ++ tailWord_106796) baseStart_106796 baseEnd_106796 := by
    simpa [prefixWord, tailWord_106796, baseEnd_106796] using wordTrace_append hprefix tailTrace_106796
  have hstable : (prefixWord ++ tailWord_106796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106796).length < 2 ^ (prefixWord ++ tailWord_106796).sum := by decide
  have hdescent : baseEnd_106796 < baseStart_106796 := by decide
  rcases family_descends (prefixWord ++ tailWord_106796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106803 : List Nat := [1, 1, 1, 2, 5, 1, 3, 6]
def baseStart_106803 : Nat := 118140960795 + 106803 * 2 ^ 59
def prefixEnd_106803 : Nat := 4983230072969 + 3 ^ 40 * 106803 * 2
def baseEnd_106803 : Nat := 16249266471778034510023

theorem tailTrace_106803 : CollatzResearch.WordTrace tailWord_106803 prefixEnd_106803 16249266471778034510023 := by
  unfold tailWord_106803
  simp only [CollatzResearch.WordTrace]
  refine ⟨3895425432078446345309063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2596950288052297563539375 3895425432078446345309063)
  ·
    refine ⟨5843138148117669517963595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3895425432078446345309063 5843138148117669517963595)
    ·
      refine ⟨8764707222176504276945393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5843138148117669517963595 8764707222176504276945393)
      ·
        refine ⟨6573530416632378207709045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8764707222176504276945393 6573530416632378207709045)
        ·
          refine ⟨616268476559285456972723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6573530416632378207709045 616268476559285456972723)
          ·
            refine ⟨924402714838928185459085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616268476559285456972723 924402714838928185459085)
            ·
              refine ⟨346651018064598069547157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 924402714838928185459085 346651018064598069547157)
              ·
                refine ⟨16249266471778034510023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 346651018064598069547157 16249266471778034510023)
                ·
                  rfl

theorem cell20_106803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 6].length) (baseStart_106803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106803 prefixEnd_106803 := by exact prefixLift 106803
  have htrace : WordTrace (prefixWord ++ tailWord_106803) baseStart_106803 baseEnd_106803 := by
    simpa [prefixWord, tailWord_106803, baseEnd_106803] using wordTrace_append hprefix tailTrace_106803
  have hstable : (prefixWord ++ tailWord_106803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106803).length < 2 ^ (prefixWord ++ tailWord_106803).sum := by decide
  have hdescent : baseEnd_106803 < baseStart_106803 := by decide
  rcases family_descends (prefixWord ++ tailWord_106803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106809 : List Nat := [1, 2, 1, 6, 1, 3, 1, 3, 2]
def baseStart_106809 : Nat := 118140960795 + 106809 * 2 ^ 59
def prefixEnd_106809 : Nat := 4983230072969 + 3 ^ 40 * 106809 * 2
def baseEnd_106809 : Nat := 48750537978824749330045

theorem tailTrace_106809 : CollatzResearch.WordTrace tailWord_106809 prefixEnd_106809 48750537978824749330045 := by
  unfold tailWord_106809
  simp only [CollatzResearch.WordTrace]
  refine ⟨3895644270056709370027481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2597096180037806246684987 3895644270056709370027481)
  ·
    refine ⟨2921733202542532027520611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3895644270056709370027481 2921733202542532027520611)
    ·
      refine ⟨4382599803813798041280917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2921733202542532027520611 4382599803813798041280917)
      ·
        refine ⟨205434365803771783185043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4382599803813798041280917 205434365803771783185043)
        ·
          refine ⟨308151548705657674777565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205434365803771783185043 308151548705657674777565)
          ·
            refine ⟨115556830764621628041587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308151548705657674777565 115556830764621628041587)
            ·
              refine ⟨173335246146932442062381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115556830764621628041587 173335246146932442062381)
              ·
                refine ⟨65000717305099665773393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173335246146932442062381 65000717305099665773393)
                ·
                  refine ⟨48750537978824749330045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65000717305099665773393 48750537978824749330045)
                  ·
                    rfl

theorem cell20_106809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 2].length) (baseStart_106809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106809 prefixEnd_106809 := by exact prefixLift 106809
  have htrace : WordTrace (prefixWord ++ tailWord_106809) baseStart_106809 baseEnd_106809 := by
    simpa [prefixWord, tailWord_106809, baseEnd_106809] using wordTrace_append hprefix tailTrace_106809
  have hstable : (prefixWord ++ tailWord_106809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106809).length < 2 ^ (prefixWord ++ tailWord_106809).sum := by decide
  have hdescent : baseEnd_106809 < baseStart_106809 := by decide
  rcases family_descends (prefixWord ++ tailWord_106809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106858 : List Nat := [3, 1, 3, 3, 1, 1, 2, 6]
def baseStart_106858 : Nat := 118140960795 + 106858 * 2 ^ 59
def prefixEnd_106858 : Nat := 4983230072969 + 3 ^ 40 * 106858 * 2
def baseEnd_106858 : Nat := 16257634304666118898837

theorem tailTrace_106858 : CollatzResearch.WordTrace tailWord_106858 prefixEnd_106858 16257634304666118898837 := by
  unfold tailWord_106858
  simp only [CollatzResearch.WordTrace]
  refine ⟨974357861719797684640307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2598287631252793825707485 974357861719797684640307)
  ·
    refine ⟨1461536792579696526960461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 974357861719797684640307 1461536792579696526960461)
    ·
      refine ⟨548076297217386197610173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1461536792579696526960461 548076297217386197610173)
      ·
        refine ⟨205528611456519824103815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 548076297217386197610173 205528611456519824103815)
        ·
          refine ⟨308292917184779736155723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205528611456519824103815 308292917184779736155723)
          ·
            refine ⟨462439375777169604233585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308292917184779736155723 462439375777169604233585)
            ·
              refine ⟨346829531832877203175189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462439375777169604233585 346829531832877203175189)
              ·
                refine ⟨16257634304666118898837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 346829531832877203175189 16257634304666118898837)
                ·
                  rfl

theorem cell20_106858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_106858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106858 prefixEnd_106858 := by exact prefixLift 106858
  have htrace : WordTrace (prefixWord ++ tailWord_106858) baseStart_106858 baseEnd_106858 := by
    simpa [prefixWord, tailWord_106858, baseEnd_106858] using wordTrace_append hprefix tailTrace_106858
  have hstable : (prefixWord ++ tailWord_106858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106858).length < 2 ^ (prefixWord ++ tailWord_106858).sum := by decide
  have hdescent : baseEnd_106858 < baseStart_106858 := by decide
  rcases family_descends (prefixWord ++ tailWord_106858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106902 : List Nat := [5, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_106902 : Nat := 118140960795 + 106902 * 2 ^ 59
def prefixEnd_106902 : Nat := 4983230072969 + 3 ^ 40 * 106902 * 2
def baseEnd_106902 : Nat := 48792985712929759229665

theorem tailTrace_106902 : CollatzResearch.WordTrace tailWord_106902 prefixEnd_106902 48792985712929759229665 := by
  unfold tailWord_106902
  simp only [CollatzResearch.WordTrace]
  refine ⟨243689766169986640822685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2599357505813190835441973 243689766169986640822685)
  ·
    refine ⟨91383662313744990308507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243689766169986640822685 91383662313744990308507)
    ·
      refine ⟨137075493470617485462761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91383662313744990308507 137075493470617485462761)
      ·
        refine ⟨102806620102963114097071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137075493470617485462761 102806620102963114097071)
        ·
          refine ⟨154209930154444671145607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102806620102963114097071 154209930154444671145607)
          ·
            refine ⟨231314895231667006718411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154209930154444671145607 231314895231667006718411)
            ·
              refine ⟨346972342847500510077617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231314895231667006718411 346972342847500510077617)
              ·
                refine ⟨260229257135625382558213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346972342847500510077617 260229257135625382558213)
                ·
                  refine ⟨48792985712929759229665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 260229257135625382558213 48792985712929759229665)
                  ·
                    rfl

theorem cell20_106902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_106902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106902 prefixEnd_106902 := by exact prefixLift 106902
  have htrace : WordTrace (prefixWord ++ tailWord_106902) baseStart_106902 baseEnd_106902 := by
    simpa [prefixWord, tailWord_106902, baseEnd_106902] using wordTrace_append hprefix tailTrace_106902
  have hstable : (prefixWord ++ tailWord_106902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106902).length < 2 ^ (prefixWord ++ tailWord_106902).sum := by decide
  have hdescent : baseEnd_106902 < baseStart_106902 := by decide
  rcases family_descends (prefixWord ++ tailWord_106902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106903 : List Nat := [1, 1, 3, 3, 1, 1, 4, 3, 3]
def baseStart_106903 : Nat := 118140960795 + 106903 * 2 ^ 59
def prefixEnd_106903 : Nat := 4983230072969 + 3 ^ 40 * 106903 * 2
def baseEnd_106903 : Nat := 48793442140178200196327

theorem tailTrace_106903 : CollatzResearch.WordTrace tailWord_106903 prefixEnd_106903 48793442140178200196327 := by
  unfold tailWord_106903
  simp only [CollatzResearch.WordTrace]
  refine ⟨3899072731716163423949363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2599381821144108949299575 3899072731716163423949363)
  ·
    refine ⟨5848609097574245135924045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3899072731716163423949363 5848609097574245135924045)
    ·
      refine ⟨2193228411590341925971517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5848609097574245135924045 2193228411590341925971517)
      ·
        refine ⟨822460654346378222239319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2193228411590341925971517 822460654346378222239319)
        ·
          refine ⟨1233690981519567333358979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822460654346378222239319 1233690981519567333358979)
          ·
            refine ⟨1850536472279351000038469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233690981519567333358979 1850536472279351000038469)
            ·
              refine ⟨346975588552378312507213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1850536472279351000038469 346975588552378312507213)
              ·
                refine ⟨130115845707141867190205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346975588552378312507213 130115845707141867190205)
                ·
                  refine ⟨48793442140178200196327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130115845707141867190205 48793442140178200196327)
                  ·
                    rfl

theorem cell20_106903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 3].length) (baseStart_106903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106903 prefixEnd_106903 := by exact prefixLift 106903
  have htrace : WordTrace (prefixWord ++ tailWord_106903) baseStart_106903 baseEnd_106903 := by
    simpa [prefixWord, tailWord_106903, baseEnd_106903] using wordTrace_append hprefix tailTrace_106903
  have hstable : (prefixWord ++ tailWord_106903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106903).length < 2 ^ (prefixWord ++ tailWord_106903).sum := by decide
  have hdescent : baseEnd_106903 < baseStart_106903 := by decide
  rcases family_descends (prefixWord ++ tailWord_106903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106924 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 5]
def baseStart_106924 : Nat := 118140960795 + 106924 * 2 ^ 59
def prefixEnd_106924 : Nat := 4983230072969 + 3 ^ 40 * 106924 * 2
def baseEnd_106924 : Nat := 48803027112395460496241

theorem tailTrace_106924 : CollatzResearch.WordTrace tailWord_106924 prefixEnd_106924 48803027112395460496241 := by
  unfold tailWord_106924
  simp only [CollatzResearch.WordTrace]
  refine ⟨1949919332320042005231913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2599892443093389340309217 1949919332320042005231913)
  ·
    refine ⟨1462439499240031503923935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1949919332320042005231913 1462439499240031503923935)
    ·
      refine ⟨2193659248860047255885903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1462439499240031503923935 2193659248860047255885903)
      ·
        refine ⟨3290488873290070883828855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2193659248860047255885903 3290488873290070883828855)
        ·
          refine ⟨4935733309935106325743283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3290488873290070883828855 4935733309935106325743283)
          ·
            refine ⟨7403599964902659488614925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4935733309935106325743283 7403599964902659488614925)
            ·
              refine ⟨2776349986838497308230597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7403599964902659488614925 2776349986838497308230597)
              ·
                refine ⟨520565622532218245293237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2776349986838497308230597 520565622532218245293237)
                ·
                  refine ⟨48803027112395460496241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 520565622532218245293237 48803027112395460496241)
                  ·
                    rfl

theorem cell20_106924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_106924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106924 prefixEnd_106924 := by exact prefixLift 106924
  have htrace : WordTrace (prefixWord ++ tailWord_106924) baseStart_106924 baseEnd_106924 := by
    simpa [prefixWord, tailWord_106924, baseEnd_106924] using wordTrace_append hprefix tailTrace_106924
  have hstable : (prefixWord ++ tailWord_106924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106924).length < 2 ^ (prefixWord ++ tailWord_106924).sum := by decide
  have hdescent : baseEnd_106924 < baseStart_106924 := by decide
  rcases family_descends (prefixWord ++ tailWord_106924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106941 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 5]
def baseStart_106941 : Nat := 118140960795 + 106941 * 2 ^ 59
def prefixEnd_106941 : Nat := 4983230072969 + 3 ^ 40 * 106941 * 2
def baseEnd_106941 : Nat := 48810786375618956929505

theorem tailTrace_106941 : CollatzResearch.WordTrace tailWord_106941 prefixEnd_106941 48810786375618956929505 := by
  unfold tailWord_106941
  simp only [CollatzResearch.WordTrace]
  refine ⟨3900458705578495913832677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2600305803718997275888451 3900458705578495913832677)
  ·
    refine ⟨731336007295967983843627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3900458705578495913832677 731336007295967983843627)
    ·
      refine ⟨1097004010943951975765441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 731336007295967983843627 1097004010943951975765441)
      ·
        refine ⟨822753008207963981824081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1097004010943951975765441 822753008207963981824081)
        ·
          refine ⟨617064756155972986368061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 822753008207963981824081 617064756155972986368061)
          ·
            refine ⟨231399283558489869888023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 617064756155972986368061 231399283558489869888023)
            ·
              refine ⟨347098925337734804832035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231399283558489869888023 347098925337734804832035)
              ·
                refine ⟨520648388006602207248053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347098925337734804832035 520648388006602207248053)
                ·
                  refine ⟨48810786375618956929505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 520648388006602207248053 48810786375618956929505)
                  ·
                    rfl

theorem cell20_106941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_106941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_106941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_106941 prefixEnd_106941 := by exact prefixLift 106941
  have htrace : WordTrace (prefixWord ++ tailWord_106941) baseStart_106941 baseEnd_106941 := by
    simpa [prefixWord, tailWord_106941, baseEnd_106941] using wordTrace_append hprefix tailTrace_106941
  have hstable : (prefixWord ++ tailWord_106941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106941).length < 2 ^ (prefixWord ++ tailWord_106941).sum := by decide
  have hdescent : baseEnd_106941 < baseStart_106941 := by decide
  rcases family_descends (prefixWord ++ tailWord_106941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107000 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 5]
def baseStart_107000 : Nat := 118140960795 + 107000 * 2 ^ 59
def prefixEnd_107000 : Nat := 4983230072969 + 3 ^ 40 * 107000 * 2
def baseEnd_107000 : Nat := 48837715583276973962597

theorem tailTrace_107000 : CollatzResearch.WordTrace tailWord_107000 prefixEnd_107000 48837715583276973962597 := by
  unfold tailWord_107000
  simp only [CollatzResearch.WordTrace]
  refine ⟨1951305306182374495115227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2601740408243165993486969 1951305306182374495115227)
  ·
    refine ⟨2926957959273561742672841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1951305306182374495115227 2926957959273561742672841)
    ·
      refine ⟨2195218469455171307004631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2926957959273561742672841 2195218469455171307004631)
      ·
        refine ⟨3292827704182756960506947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2195218469455171307004631 3292827704182756960506947)
        ·
          refine ⟨4939241556274135440760421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3292827704182756960506947 4939241556274135440760421)
          ·
            refine ⟨926107791801400395142579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4939241556274135440760421 926107791801400395142579)
            ·
              refine ⟨1389161687702100592713869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926107791801400395142579 1389161687702100592713869)
              ·
                refine ⟨520935632888287722267701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1389161687702100592713869 520935632888287722267701)
                ·
                  refine ⟨48837715583276973962597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 520935632888287722267701 48837715583276973962597)
                  ·
                    rfl

theorem cell20_107000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_107000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107000 prefixEnd_107000 := by exact prefixLift 107000
  have htrace : WordTrace (prefixWord ++ tailWord_107000) baseStart_107000 baseEnd_107000 := by
    simpa [prefixWord, tailWord_107000, baseEnd_107000] using wordTrace_append hprefix tailTrace_107000
  have hstable : (prefixWord ++ tailWord_107000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107000).length < 2 ^ (prefixWord ++ tailWord_107000).sum := by decide
  have hdescent : baseEnd_107000 < baseStart_107000 := by decide
  rcases family_descends (prefixWord ++ tailWord_107000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107041 : List Nat := [1, 2, 3, 2, 2, 1, 2, 5, 2]
def baseStart_107041 : Nat := 118140960795 + 107041 * 2 ^ 59
def prefixEnd_107041 : Nat := 4983230072969 + 3 ^ 40 * 107041 * 2
def baseEnd_107041 : Nat := 48856429100463053595763

theorem tailTrace_107041 : CollatzResearch.WordTrace tailWord_107041 prefixEnd_107041 48856429100463053595763 := by
  unfold tailWord_107041
  simp only [CollatzResearch.WordTrace]
  refine ⟨3904106005216212992472977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2602737336810808661648651 3904106005216212992472977)
  ·
    refine ⟨2928079503912159744354733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3904106005216212992472977 2928079503912159744354733)
    ·
      refine ⟨1098029813967059904133025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2928079503912159744354733 1098029813967059904133025)
      ·
        refine ⟨823522360475294928099769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1098029813967059904133025 823522360475294928099769)
        ·
          refine ⟨617641770356471196074827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823522360475294928099769 617641770356471196074827)
          ·
            refine ⟨926462655534706794112241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617641770356471196074827 926462655534706794112241)
            ·
              refine ⟨694846991651030095584181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926462655534706794112241 694846991651030095584181)
              ·
                refine ⟨65141905467284071461017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 694846991651030095584181 65141905467284071461017)
                ·
                  refine ⟨48856429100463053595763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65141905467284071461017 48856429100463053595763)
                  ·
                    rfl

theorem cell20_107041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 2].length) (baseStart_107041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107041 prefixEnd_107041 := by exact prefixLift 107041
  have htrace : WordTrace (prefixWord ++ tailWord_107041) baseStart_107041 baseEnd_107041 := by
    simpa [prefixWord, tailWord_107041, baseEnd_107041] using wordTrace_append hprefix tailTrace_107041
  have hstable : (prefixWord ++ tailWord_107041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107041).length < 2 ^ (prefixWord ++ tailWord_107041).sum := by decide
  have hdescent : baseEnd_107041 < baseStart_107041 := by decide
  rcases family_descends (prefixWord ++ tailWord_107041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107054 : List Nat := [4, 1, 3, 1, 3, 2, 2, 2, 2]
def baseStart_107054 : Nat := 118140960795 + 107054 * 2 ^ 59
def prefixEnd_107054 : Nat := 4983230072969 + 3 ^ 40 * 107054 * 2
def baseEnd_107054 : Nat := 48862362654692786162377

theorem tailTrace_107054 : CollatzResearch.WordTrace tailWord_107054 prefixEnd_107054 48862362654692786162377 := by
  unfold tailWord_107054
  simp only [CollatzResearch.WordTrace]
  refine ⟨488072519271139526587027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2603053436112744141797477 488072519271139526587027)
  ·
    refine ⟨732108778906709289880541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 488072519271139526587027 732108778906709289880541)
    ·
      refine ⟨274540792090015983705203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 732108778906709289880541 274540792090015983705203)
      ·
        refine ⟨411811188135023975557805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274540792090015983705203 411811188135023975557805)
        ·
          refine ⟨154429195550633990834177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 411811188135023975557805 154429195550633990834177)
          ·
            refine ⟨115821896662975493125633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154429195550633990834177 115821896662975493125633)
            ·
              refine ⟨86866422497231619844225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115821896662975493125633 86866422497231619844225)
              ·
                refine ⟨65149816872923714883169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86866422497231619844225 65149816872923714883169)
                ·
                  refine ⟨48862362654692786162377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65149816872923714883169 48862362654692786162377)
                  ·
                    rfl

theorem cell20_107054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_107054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107054 prefixEnd_107054 := by exact prefixLift 107054
  have htrace : WordTrace (prefixWord ++ tailWord_107054) baseStart_107054 baseEnd_107054 := by
    simpa [prefixWord, tailWord_107054, baseEnd_107054] using wordTrace_append hprefix tailTrace_107054
  have hstable : (prefixWord ++ tailWord_107054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107054).length < 2 ^ (prefixWord ++ tailWord_107054).sum := by decide
  have hdescent : baseEnd_107054 < baseStart_107054 := by decide
  rcases family_descends (prefixWord ++ tailWord_107054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107058 : List Nat := [3, 2, 1, 1, 2, 1, 6, 2, 2]
def baseStart_107058 : Nat := 118140960795 + 107058 * 2 ^ 59
def prefixEnd_107058 : Nat := 4983230072969 + 3 ^ 40 * 107058 * 2
def baseEnd_107058 : Nat := 48864188363686550029027

theorem tailTrace_107058 : CollatzResearch.WordTrace tailWord_107058 prefixEnd_107058 48864188363686550029027 := by
  unfold tailWord_107058
  simp only [CollatzResearch.WordTrace]
  refine ⟨976181511538656223960457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2603150697436416597227885 976181511538656223960457)
  ·
    refine ⟨732136133653992167970343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 976181511538656223960457 732136133653992167970343)
    ·
      refine ⟨1098204200480988251955515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 732136133653992167970343 1098204200480988251955515)
      ·
        refine ⟨1647306300721482377933273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1098204200480988251955515 1647306300721482377933273)
        ·
          refine ⟨1235479725541111783449955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1647306300721482377933273 1235479725541111783449955)
          ·
            refine ⟨1853219588311667675174933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235479725541111783449955 1853219588311667675174933)
            ·
              refine ⟨86869668202109422273825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1853219588311667675174933 86869668202109422273825)
              ·
                refine ⟨65152251151582066705369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86869668202109422273825 65152251151582066705369)
                ·
                  refine ⟨48864188363686550029027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65152251151582066705369 48864188363686550029027)
                  ·
                    rfl

theorem cell20_107058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_107058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107058 prefixEnd_107058 := by exact prefixLift 107058
  have htrace : WordTrace (prefixWord ++ tailWord_107058) baseStart_107058 baseEnd_107058 := by
    simpa [prefixWord, tailWord_107058, baseEnd_107058] using wordTrace_append hprefix tailTrace_107058
  have hstable : (prefixWord ++ tailWord_107058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107058).length < 2 ^ (prefixWord ++ tailWord_107058).sum := by decide
  have hdescent : baseEnd_107058 < baseStart_107058 := by decide
  rcases family_descends (prefixWord ++ tailWord_107058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107083 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 6]
def baseStart_107083 : Nat := 118140960795 + 107083 * 2 ^ 59
def prefixEnd_107083 : Nat := 4983230072969 + 3 ^ 40 * 107083 * 2
def baseEnd_107083 : Nat := 48875599044897574195591

theorem tailTrace_107083 : CollatzResearch.WordTrace tailWord_107083 prefixEnd_107083 48875599044897574195591 := by
  unfold tailWord_107083
  simp only [CollatzResearch.WordTrace]
  refine ⟨3905637871064054165501903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2603758580709369443667935 3905637871064054165501903)
  ·
    refine ⟨5858456806596081248252855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3905637871064054165501903 5858456806596081248252855)
    ·
      refine ⟨8787685209894121872379283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5858456806596081248252855 8787685209894121872379283)
      ·
        refine ⟨13181527814841182808568925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8787685209894121872379283 13181527814841182808568925)
        ·
          refine ⟨4943072930565443553213347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13181527814841182808568925 4943072930565443553213347)
          ·
            refine ⟨7414609395848165329820021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4943072930565443553213347 7414609395848165329820021)
            ·
              refine ⟨695119630860765499670627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7414609395848165329820021 695119630860765499670627)
              ·
                refine ⟨1042679446291148249505941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 695119630860765499670627 1042679446291148249505941)
                ·
                  refine ⟨48875599044897574195591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1042679446291148249505941 48875599044897574195591)
                  ·
                    rfl

theorem cell20_107083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_107083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107083 prefixEnd_107083 := by exact prefixLift 107083
  have htrace : WordTrace (prefixWord ++ tailWord_107083) baseStart_107083 baseEnd_107083 := by
    simpa [prefixWord, tailWord_107083, baseEnd_107083] using wordTrace_append hprefix tailTrace_107083
  have hstable : (prefixWord ++ tailWord_107083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107083).length < 2 ^ (prefixWord ++ tailWord_107083).sum := by decide
  have hdescent : baseEnd_107083 < baseStart_107083 := by decide
  rcases family_descends (prefixWord ++ tailWord_107083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107102 : List Nat := [4, 4, 1, 2, 2, 1, 1, 2, 3]
def baseStart_107102 : Nat := 118140960795 + 107102 * 2 ^ 59
def prefixEnd_107102 : Nat := 4983230072969 + 3 ^ 40 * 107102 * 2
def baseEnd_107102 : Nat := 48884271162617952562181

theorem tailTrace_107102 : CollatzResearch.WordTrace tailWord_107102 prefixEnd_107102 48884271162617952562181 := by
  unfold tailWord_107102
  simp only [CollatzResearch.WordTrace]
  refine ⟨488291357249402551305445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2604220571996813606962373 488291357249402551305445)
  ·
    refine ⟨91554629484262978369771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 488291357249402551305445 91554629484262978369771)
    ·
      refine ⟨137331944226394467554657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91554629484262978369771 137331944226394467554657)
      ·
        refine ⟨102998958169795850665993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137331944226394467554657 102998958169795850665993)
        ·
          refine ⟨77249218627346887999495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102998958169795850665993 77249218627346887999495)
          ·
            refine ⟨115873827941020331999243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77249218627346887999495 115873827941020331999243)
            ·
              refine ⟨173810741911530497998865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115873827941020331999243 173810741911530497998865)
              ·
                refine ⟨130358056433647873499149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173810741911530497998865 130358056433647873499149)
                ·
                  refine ⟨48884271162617952562181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130358056433647873499149 48884271162617952562181)
                  ·
                    rfl

theorem cell20_107102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_107102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107102 prefixEnd_107102 := by exact prefixLift 107102
  have htrace : WordTrace (prefixWord ++ tailWord_107102) baseStart_107102 baseEnd_107102 := by
    simpa [prefixWord, tailWord_107102, baseEnd_107102] using wordTrace_append hprefix tailTrace_107102
  have hstable : (prefixWord ++ tailWord_107102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107102).length < 2 ^ (prefixWord ++ tailWord_107102).sum := by decide
  have hdescent : baseEnd_107102 < baseStart_107102 := by decide
  rcases family_descends (prefixWord ++ tailWord_107102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107106 : List Nat := [3, 3, 2, 3, 1, 2, 1, 2, 3]
def baseStart_107106 : Nat := 118140960795 + 107106 * 2 ^ 59
def prefixEnd_107106 : Nat := 4983230072969 + 3 ^ 40 * 107106 * 2
def baseEnd_107106 : Nat := 48886096871611716428831

theorem tailTrace_107106 : CollatzResearch.WordTrace tailWord_107106 prefixEnd_107106 48886096871611716428831 := by
  unfold tailWord_107106
  simp only [CollatzResearch.WordTrace]
  refine ⟨976619187495182273397293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2604317833320486062392781 976619187495182273397293)
  ·
    refine ⟨366232195310693352523985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 976619187495182273397293 366232195310693352523985)
    ·
      refine ⟨274674146483020014392989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366232195310693352523985 274674146483020014392989)
      ·
        refine ⟨103002804931132505397371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274674146483020014392989 103002804931132505397371)
        ·
          refine ⟨154504207396698758096057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103002804931132505397371 154504207396698758096057)
          ·
            refine ⟨115878155547524068572043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154504207396698758096057 115878155547524068572043)
            ·
              refine ⟨173817233321286102858065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115878155547524068572043 173817233321286102858065)
              ·
                refine ⟨130362924990964577143549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173817233321286102858065 130362924990964577143549)
                ·
                  refine ⟨48886096871611716428831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130362924990964577143549 48886096871611716428831)
                  ·
                    rfl

theorem cell20_107106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_107106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107106 prefixEnd_107106 := by exact prefixLift 107106
  have htrace : WordTrace (prefixWord ++ tailWord_107106) baseStart_107106 baseEnd_107106 := by
    simpa [prefixWord, tailWord_107106, baseEnd_107106] using wordTrace_append hprefix tailTrace_107106
  have hstable : (prefixWord ++ tailWord_107106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107106).length < 2 ^ (prefixWord ++ tailWord_107106).sum := by decide
  have hdescent : baseEnd_107106 < baseStart_107106 := by decide
  rcases family_descends (prefixWord ++ tailWord_107106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107117 : List Nat := [1, 5, 1, 1, 3, 2, 2, 1, 4]
def baseStart_107117 : Nat := 118140960795 + 107117 * 2 ^ 59
def prefixEnd_107117 : Nat := 4983230072969 + 3 ^ 40 * 107117 * 2
def baseEnd_107117 : Nat := 48891117571344567062119

theorem tailTrace_107117 : CollatzResearch.WordTrace tailWord_107117 prefixEnd_107117 48891117571344567062119 := by
  unfold tailWord_107117
  simp only [CollatzResearch.WordTrace]
  refine ⟨3906877952940877972239605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2604585301960585314826403 3906877952940877972239605)
  ·
    refine ⟨366269808088207309897463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3906877952940877972239605 366269808088207309897463)
    ·
      refine ⟨549404712132310964846195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366269808088207309897463 549404712132310964846195)
      ·
        refine ⟨824107068198466447269293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549404712132310964846195 824107068198466447269293)
        ·
          refine ⟨309040150574424917725985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 824107068198466447269293 309040150574424917725985)
          ·
            refine ⟨231780112930818688294489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309040150574424917725985 231780112930818688294489)
            ·
              refine ⟨173835084698114016220867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231780112930818688294489 173835084698114016220867)
              ·
                refine ⟨260752627047171024331301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173835084698114016220867 260752627047171024331301)
                ·
                  refine ⟨48891117571344567062119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 260752627047171024331301 48891117571344567062119)
                  ·
                    rfl

theorem cell20_107117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_107117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107117 prefixEnd_107117 := by exact prefixLift 107117
  have htrace : WordTrace (prefixWord ++ tailWord_107117) baseStart_107117 baseEnd_107117 := by
    simpa [prefixWord, tailWord_107117, baseEnd_107117] using wordTrace_append hprefix tailTrace_107117
  have hstable : (prefixWord ++ tailWord_107117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107117).length < 2 ^ (prefixWord ++ tailWord_107117).sum := by decide
  have hdescent : baseEnd_107117 < baseStart_107117 := by decide
  rcases family_descends (prefixWord ++ tailWord_107117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107172 : List Nat := [2, 3, 1, 2, 2, 1, 5, 2, 2]
def baseStart_107172 : Nat := 118140960795 + 107172 * 2 ^ 59
def prefixEnd_107172 : Nat := 4983230072969 + 3 ^ 40 * 107172 * 2
def baseEnd_107172 : Nat := 48916221070008820228561

theorem tailTrace_107172 : CollatzResearch.WordTrace tailWord_107172 prefixEnd_107172 48916221070008820228561 := by
  unfold tailWord_107172
  simp only [CollatzResearch.WordTrace]
  refine ⟨1954441983870811182745885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2605922645161081576994513 1954441983870811182745885)
  ·
    refine ⟨732915743951554193529707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1954441983870811182745885 732915743951554193529707)
    ·
      refine ⟨1099373615927331290294561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 732915743951554193529707 1099373615927331290294561)
      ·
        refine ⟨824530211945498467720921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1099373615927331290294561 824530211945498467720921)
        ·
          refine ⟨618397658959123850790691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 824530211945498467720921 618397658959123850790691)
          ·
            refine ⟨927596488438685776186037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618397658959123850790691 927596488438685776186037)
            ·
              refine ⟨86962170791126791517441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 927596488438685776186037 86962170791126791517441)
              ·
                refine ⟨65221628093345093638081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86962170791126791517441 65221628093345093638081)
                ·
                  refine ⟨48916221070008820228561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65221628093345093638081 48916221070008820228561)
                  ·
                    rfl

theorem cell20_107172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_107172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107172 prefixEnd_107172 := by exact prefixLift 107172
  have htrace : WordTrace (prefixWord ++ tailWord_107172) baseStart_107172 baseEnd_107172 := by
    simpa [prefixWord, tailWord_107172, baseEnd_107172] using wordTrace_append hprefix tailTrace_107172
  have hstable : (prefixWord ++ tailWord_107172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107172).length < 2 ^ (prefixWord ++ tailWord_107172).sum := by decide
  have hdescent : baseEnd_107172 < baseStart_107172 := by decide
  rcases family_descends (prefixWord ++ tailWord_107172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107182 : List Nat := [4, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_107182 : Nat := 118140960795 + 107182 * 2 ^ 59
def prefixEnd_107182 : Nat := 4983230072969 + 3 ^ 40 * 107182 * 2
def baseEnd_107182 : Nat := 48920785342493229895187

theorem tailTrace_107182 : CollatzResearch.WordTrace tailWord_107182 prefixEnd_107182 48920785342493229895187 := by
  unfold tailWord_107182
  simp only [CollatzResearch.WordTrace]
  refine ⟨488656087213174259169475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2606165798470262715570533 488656087213174259169475)
  ·
    refine ⟨732984130819761388754213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 488656087213174259169475 732984130819761388754213)
    ·
      refine ⟨137434524528705260391415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 732984130819761388754213 137434524528705260391415)
      ·
        refine ⟨206151786793057890587123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137434524528705260391415 206151786793057890587123)
        ·
          refine ⟨309227680189586835880685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206151786793057890587123 309227680189586835880685)
          ·
            refine ⟨115960380071095063455257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309227680189586835880685 115960380071095063455257)
            ·
              refine ⟨86970285053321297591443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115960380071095063455257 86970285053321297591443)
              ·
                refine ⟨130455427579981946387165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86970285053321297591443 130455427579981946387165)
                ·
                  refine ⟨48920785342493229895187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130455427579981946387165 48920785342493229895187)
                  ·
                    rfl

theorem cell20_107182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_107182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107182 prefixEnd_107182 := by exact prefixLift 107182
  have htrace : WordTrace (prefixWord ++ tailWord_107182) baseStart_107182 baseEnd_107182 := by
    simpa [prefixWord, tailWord_107182, baseEnd_107182] using wordTrace_append hprefix tailTrace_107182
  have hstable : (prefixWord ++ tailWord_107182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107182).length < 2 ^ (prefixWord ++ tailWord_107182).sum := by decide
  have hdescent : baseEnd_107182 < baseStart_107182 := by decide
  rcases family_descends (prefixWord ++ tailWord_107182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107183 : List Nat := [1, 1, 2, 1, 2, 6, 2, 5]
def baseStart_107183 : Nat := 118140960795 + 107183 * 2 ^ 59
def prefixEnd_107183 : Nat := 4983230072969 + 3 ^ 40 * 107183 * 2
def baseEnd_107183 : Nat := 16307080589913890287283

theorem tailTrace_107183 : CollatzResearch.WordTrace tailWord_107183 prefixEnd_107183 16307080589913890287283 := by
  unfold tailWord_107183
  simp only [CollatzResearch.WordTrace]
  refine ⟨3909285170701771244142203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2606190113801180829428135 3909285170701771244142203)
  ·
    refine ⟨5863927756052656866213305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3909285170701771244142203 5863927756052656866213305)
    ·
      refine ⟨4397945817039492649659979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5863927756052656866213305 4397945817039492649659979)
      ·
        refine ⟨6596918725559238974489969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4397945817039492649659979 6596918725559238974489969)
        ·
          refine ⟨4947689044169429230867477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6596918725559238974489969 4947689044169429230867477)
          ·
            refine ⟨231922923945441995196913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4947689044169429230867477 231922923945441995196913)
            ·
              refine ⟨173942192959081496397685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231922923945441995196913 173942192959081496397685)
              ·
                refine ⟨16307080589913890287283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173942192959081496397685 16307080589913890287283)
                ·
                  rfl

theorem cell20_107183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 5].length) (baseStart_107183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107183 prefixEnd_107183 := by exact prefixLift 107183
  have htrace : WordTrace (prefixWord ++ tailWord_107183) baseStart_107183 baseEnd_107183 := by
    simpa [prefixWord, tailWord_107183, baseEnd_107183] using wordTrace_append hprefix tailTrace_107183
  have hstable : (prefixWord ++ tailWord_107183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107183).length < 2 ^ (prefixWord ++ tailWord_107183).sum := by decide
  have hdescent : baseEnd_107183 < baseStart_107183 := by decide
  rcases family_descends (prefixWord ++ tailWord_107183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107221 : List Nat := [1, 3, 2, 5, 9]
def baseStart_107221 : Nat := 118140960795 + 107221 * 2 ^ 59
def prefixEnd_107221 : Nat := 4983230072969 + 3 ^ 40 * 107221 * 2
def baseEnd_107221 : Nat := 604180074138054661667

theorem tailTrace_107221 : CollatzResearch.WordTrace tailWord_107221 prefixEnd_107221 604180074138054661667 := by
  unfold tailWord_107221
  simp only [CollatzResearch.WordTrace]
  refine ⟨3910671144564103734025517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2607114096376069156017011 3910671144564103734025517)
  ·
    refine ⟨1466501679211538900259569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3910671144564103734025517 1466501679211538900259569)
    ·
      refine ⟨1099876259408654175194677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1466501679211538900259569 1099876259408654175194677)
      ·
        refine ⟨103113399319561328924501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1099876259408654175194677 103113399319561328924501)
        ·
          refine ⟨604180074138054661667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 103113399319561328924501 604180074138054661667)
          ·
            rfl

theorem cell20_107221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 9].length) (baseStart_107221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107221 prefixEnd_107221 := by exact prefixLift 107221
  have htrace : WordTrace (prefixWord ++ tailWord_107221) baseStart_107221 baseEnd_107221 := by
    simpa [prefixWord, tailWord_107221, baseEnd_107221] using wordTrace_append hprefix tailTrace_107221
  have hstable : (prefixWord ++ tailWord_107221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107221).length < 2 ^ (prefixWord ++ tailWord_107221).sum := by decide
  have hdescent : baseEnd_107221 < baseStart_107221 := by decide
  rcases family_descends (prefixWord ++ tailWord_107221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107231 : List Nat := [1, 1, 2, 3, 2, 4, 1, 4, 2]
def baseStart_107231 : Nat := 118140960795 + 107231 * 2 ^ 59
def prefixEnd_107231 : Nat := 4983230072969 + 3 ^ 40 * 107231 * 2
def baseEnd_107231 : Nat := 48943150277666837261653

theorem tailTrace_107231 : CollatzResearch.WordTrace tailWord_107231 prefixEnd_107231 48943150277666837261653 := by
  unfold tailWord_107231
  simp only [CollatzResearch.WordTrace]
  refine ⟨3911035874527875441889547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2607357249685250294593031 3911035874527875441889547)
  ·
    refine ⟨5866553811791813162834321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3911035874527875441889547 5866553811791813162834321)
    ·
      refine ⟨4399915358843859872125741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5866553811791813162834321 4399915358843859872125741)
      ·
        refine ⟨1649968259566447452047153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4399915358843859872125741 1649968259566447452047153)
        ·
          refine ⟨1237476194674835589035365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1649968259566447452047153 1237476194674835589035365)
          ·
            refine ⟨232026786501531672944131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1237476194674835589035365 232026786501531672944131)
            ·
              refine ⟨348040179752297509416197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232026786501531672944131 348040179752297509416197)
              ·
                refine ⟨65257533703555783015537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 348040179752297509416197 65257533703555783015537)
                ·
                  refine ⟨48943150277666837261653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65257533703555783015537 48943150277666837261653)
                  ·
                    rfl

theorem cell20_107231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 2].length) (baseStart_107231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107231 prefixEnd_107231 := by exact prefixLift 107231
  have htrace : WordTrace (prefixWord ++ tailWord_107231) baseStart_107231 baseEnd_107231 := by
    simpa [prefixWord, tailWord_107231, baseEnd_107231] using wordTrace_append hprefix tailTrace_107231
  have hstable : (prefixWord ++ tailWord_107231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107231).length < 2 ^ (prefixWord ++ tailWord_107231).sum := by decide
  have hdescent : baseEnd_107231 < baseStart_107231 := by decide
  rcases family_descends (prefixWord ++ tailWord_107231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107245 : List Nat := [1, 5, 1, 2, 1, 1, 1, 5, 3]
def baseStart_107245 : Nat := 118140960795 + 107245 * 2 ^ 59
def prefixEnd_107245 : Nat := 4983230072969 + 3 ^ 40 * 107245 * 2
def baseEnd_107245 : Nat := 48949540259145010794929

theorem tailTrace_107245 : CollatzResearch.WordTrace tailWord_107245 prefixEnd_107245 48949540259145010794929 := by
  unfold tailWord_107245
  simp only [CollatzResearch.WordTrace]
  refine ⟨3911546496477155832899189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2607697664318103888599459 3911546496477155832899189)
  ·
    refine ⟨366707484044733359334299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3911546496477155832899189 366707484044733359334299)
    ·
      refine ⟨550061226067100039001449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366707484044733359334299 550061226067100039001449)
      ·
        refine ⟨412545919550325029251087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550061226067100039001449 412545919550325029251087)
        ·
          refine ⟨618818879325487543876631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412545919550325029251087 618818879325487543876631)
          ·
            refine ⟨928228318988231315814947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618818879325487543876631 928228318988231315814947)
            ·
              refine ⟨1392342478482346973722421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 928228318988231315814947 1392342478482346973722421)
              ·
                refine ⟨130532107357720028786477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1392342478482346973722421 130532107357720028786477)
                ·
                  refine ⟨48949540259145010794929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130532107357720028786477 48949540259145010794929)
                  ·
                    rfl

theorem cell20_107245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_107245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107245 prefixEnd_107245 := by exact prefixLift 107245
  have htrace : WordTrace (prefixWord ++ tailWord_107245) baseStart_107245 baseEnd_107245 := by
    simpa [prefixWord, tailWord_107245, baseEnd_107245] using wordTrace_append hprefix tailTrace_107245
  have hstable : (prefixWord ++ tailWord_107245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107245).length < 2 ^ (prefixWord ++ tailWord_107245).sum := by decide
  have hdescent : baseEnd_107245 < baseStart_107245 := by decide
  rcases family_descends (prefixWord ++ tailWord_107245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107290 : List Nat := [3, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_107290 : Nat := 118140960795 + 107290 * 2 ^ 59
def prefixEnd_107290 : Nat := 4983230072969 + 3 ^ 40 * 107290 * 2
def baseEnd_107290 : Nat := 48970079485324854294745

theorem tailTrace_107290 : CollatzResearch.WordTrace tailWord_107290 prefixEnd_107290 48970079485324854294745 := by
  unfold tailWord_107290
  simp only [CollatzResearch.WordTrace]
  refine ⟨978296945328532129571831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2608791854209419012191549 978296945328532129571831)
  ·
    refine ⟨1467445417992798194357747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 978296945328532129571831 1467445417992798194357747)
    ·
      refine ⟨2201168126989197291536621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1467445417992798194357747 2201168126989197291536621)
      ·
        refine ⟨825438047620948984326233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2201168126989197291536621 825438047620948984326233)
        ·
          refine ⟨619078535715711738244675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 825438047620948984326233 619078535715711738244675)
          ·
            refine ⟨928617803573567607367013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619078535715711738244675 928617803573567607367013)
            ·
              refine ⟨174115838170043926381315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 928617803573567607367013 174115838170043926381315)
              ·
                refine ⟨261173757255065889571973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174115838170043926381315 261173757255065889571973)
                ·
                  refine ⟨48970079485324854294745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 261173757255065889571973 48970079485324854294745)
                  ·
                    rfl

theorem cell20_107290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_107290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107290 prefixEnd_107290 := by exact prefixLift 107290
  have htrace : WordTrace (prefixWord ++ tailWord_107290) baseStart_107290 baseEnd_107290 := by
    simpa [prefixWord, tailWord_107290, baseEnd_107290] using wordTrace_append hprefix tailTrace_107290
  have hstable : (prefixWord ++ tailWord_107290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107290).length < 2 ^ (prefixWord ++ tailWord_107290).sum := by decide
  have hdescent : baseEnd_107290 < baseStart_107290 := by decide
  rcases family_descends (prefixWord ++ tailWord_107290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107341 : List Nat := [1, 6, 1, 2, 3, 1, 1, 1, 4]
def baseStart_107341 : Nat := 118140960795 + 107341 * 2 ^ 59
def prefixEnd_107341 : Nat := 4983230072969 + 3 ^ 40 * 107341 * 2
def baseEnd_107341 : Nat := 48993357274995343594537

theorem tailTrace_107341 : CollatzResearch.WordTrace tailWord_107341 prefixEnd_107341 48993357274995343594537 := by
  unfold tailWord_107341
  simp only [CollatzResearch.WordTrace]
  refine ⟨3915047904129364228393877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2610031936086242818929251 3915047904129364228393877)
  ·
    refine ⟨183517870506063948205963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3915047904129364228393877 183517870506063948205963)
    ·
      refine ⟨275276805759095922308945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183517870506063948205963 275276805759095922308945)
      ·
        refine ⟨206457604319321941731709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275276805759095922308945 206457604319321941731709)
        ·
          refine ⟨77421601619745728149391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206457604319321941731709 77421601619745728149391)
          ·
            refine ⟨116132402429618592224087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77421601619745728149391 116132402429618592224087)
            ·
              refine ⟨174198603644427888336131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116132402429618592224087 174198603644427888336131)
              ·
                refine ⟨261297905466641832504197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174198603644427888336131 261297905466641832504197)
                ·
                  refine ⟨48993357274995343594537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 261297905466641832504197 48993357274995343594537)
                  ·
                    rfl

theorem cell20_107341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_107341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107341 prefixEnd_107341 := by exact prefixLift 107341
  have htrace : WordTrace (prefixWord ++ tailWord_107341) baseStart_107341 baseEnd_107341 := by
    simpa [prefixWord, tailWord_107341, baseEnd_107341] using wordTrace_append hprefix tailTrace_107341
  have hstable : (prefixWord ++ tailWord_107341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107341).length < 2 ^ (prefixWord ++ tailWord_107341).sum := by decide
  have hdescent : baseEnd_107341 < baseStart_107341 := by decide
  rcases family_descends (prefixWord ++ tailWord_107341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107345 : List Nat := [1, 2, 2, 1, 6, 2, 1, 1, 4]
def baseStart_107345 : Nat := 118140960795 + 107345 * 2 ^ 59
def prefixEnd_107345 : Nat := 4983230072969 + 3 ^ 40 * 107345 * 2
def baseEnd_107345 : Nat := 48995182983989107461187

theorem tailTrace_107345 : CollatzResearch.WordTrace tailWord_107345 prefixEnd_107345 48995182983989107461187 := by
  unfold tailWord_107345
  simp only [CollatzResearch.WordTrace]
  refine ⟨3915193796114872911539489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2610129197409915274359659 3915193796114872911539489)
  ·
    refine ⟨2936395347086154683654617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3915193796114872911539489 2936395347086154683654617)
    ·
      refine ⟨2202296510314616012740963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2936395347086154683654617 2202296510314616012740963)
      ·
        refine ⟨3303444765471924019111445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2202296510314616012740963 3303444765471924019111445)
        ·
          refine ⟨154848973381496438395849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3303444765471924019111445 154848973381496438395849)
          ·
            refine ⟨116136730036122328796887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154848973381496438395849 116136730036122328796887)
            ·
              refine ⟨174205095054183493195331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116136730036122328796887 174205095054183493195331)
              ·
                refine ⟨261307642581275239792997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174205095054183493195331 261307642581275239792997)
                ·
                  refine ⟨48995182983989107461187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 261307642581275239792997 48995182983989107461187)
                  ·
                    rfl

theorem cell20_107345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 4].length) (baseStart_107345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107345 prefixEnd_107345 := by exact prefixLift 107345
  have htrace : WordTrace (prefixWord ++ tailWord_107345) baseStart_107345 baseEnd_107345 := by
    simpa [prefixWord, tailWord_107345, baseEnd_107345] using wordTrace_append hprefix tailTrace_107345
  have hstable : (prefixWord ++ tailWord_107345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107345).length < 2 ^ (prefixWord ++ tailWord_107345).sum := by decide
  have hdescent : baseEnd_107345 < baseStart_107345 := by decide
  rcases family_descends (prefixWord ++ tailWord_107345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107390 : List Nat := [4, 2, 3, 1, 2, 8]
def baseStart_107390 : Nat := 118140960795 + 107390 * 2 ^ 59
def prefixEnd_107390 : Nat := 4983230072969 + 3 ^ 40 * 107390 * 2
def baseEnd_107390 : Nat := 1815397118895146331889

theorem tailTrace_107390 : CollatzResearch.WordTrace tailWord_107390 prefixEnd_107390 1815397118895146331889 := by
  unfold tailWord_107390
  simp only [CollatzResearch.WordTrace]
  refine ⟨489604385118980699615953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2611223387301230397951749 489604385118980699615953)
  ·
    refine ⟨367203288839235524711965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 489604385118980699615953 367203288839235524711965)
    ·
      refine ⟨137701233314713321766987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367203288839235524711965 137701233314713321766987)
      ·
        refine ⟨206551849972069982650481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137701233314713321766987 206551849972069982650481)
        ·
          refine ⟨154913887479052486987861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206551849972069982650481 154913887479052486987861)
          ·
            refine ⟨1815397118895146331889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 154913887479052486987861 1815397118895146331889)
            ·
              rfl

theorem cell20_107390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 8].length) (baseStart_107390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107390 prefixEnd_107390 := by exact prefixLift 107390
  have htrace : WordTrace (prefixWord ++ tailWord_107390) baseStart_107390 baseEnd_107390 := by
    simpa [prefixWord, tailWord_107390, baseEnd_107390] using wordTrace_append hprefix tailTrace_107390
  have hstable : (prefixWord ++ tailWord_107390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107390).length < 2 ^ (prefixWord ++ tailWord_107390).sum := by decide
  have hdescent : baseEnd_107390 < baseStart_107390 := by decide
  rcases family_descends (prefixWord ++ tailWord_107390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107397 : List Nat := [1, 3, 1, 1, 3, 4, 2, 2, 3]
def baseStart_107397 : Nat := 118140960795 + 107397 * 2 ^ 59
def prefixEnd_107397 : Nat := 4983230072969 + 3 ^ 40 * 107397 * 2
def baseEnd_107397 : Nat := 49018917200908037727641

theorem tailTrace_107397 : CollatzResearch.WordTrace tailWord_107397 prefixEnd_107397 49018917200908037727641 := by
  unfold tailWord_107397
  simp only [CollatzResearch.WordTrace]
  refine ⟨3917090391926485792432445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2611393594617657194954963 3917090391926485792432445)
  ·
    refine ⟨1468908896972432172162167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3917090391926485792432445 1468908896972432172162167)
    ·
      refine ⟨2203363345458648258243251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1468908896972432172162167 2203363345458648258243251)
      ·
        refine ⟨3305045018187972387364877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2203363345458648258243251 3305045018187972387364877)
        ·
          refine ⟨1239391881820489645261829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3305045018187972387364877 1239391881820489645261829)
          ·
            refine ⟨232385977841341808486593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1239391881820489645261829 232385977841341808486593)
            ·
              refine ⟨174289483381006356364945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232385977841341808486593 174289483381006356364945)
              ·
                refine ⟨130717112535754767273709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174289483381006356364945 130717112535754767273709)
                ·
                  refine ⟨49018917200908037727641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130717112535754767273709 49018917200908037727641)
                  ·
                    rfl

theorem cell20_107397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_107397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107397 prefixEnd_107397 := by exact prefixLift 107397
  have htrace : WordTrace (prefixWord ++ tailWord_107397) baseStart_107397 baseEnd_107397 := by
    simpa [prefixWord, tailWord_107397, baseEnd_107397] using wordTrace_append hprefix tailTrace_107397
  have hstable : (prefixWord ++ tailWord_107397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107397).length < 2 ^ (prefixWord ++ tailWord_107397).sum := by decide
  have hdescent : baseEnd_107397 < baseStart_107397 := by decide
  rcases family_descends (prefixWord ++ tailWord_107397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107400 : List Nat := [2, 1, 3, 3, 2, 1, 4, 2, 2]
def baseStart_107400 : Nat := 118140960795 + 107400 * 2 ^ 59
def prefixEnd_107400 : Nat := 4983230072969 + 3 ^ 40 * 107400 * 2
def baseEnd_107400 : Nat := 49020286482653360627629

theorem tailTrace_107400 : CollatzResearch.WordTrace tailWord_107400 prefixEnd_107400 49020286482653360627629 := by
  unfold tailWord_107400
  simp only [CollatzResearch.WordTrace]
  refine ⟨1958599905457808652395827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2611466540610411536527769 1958599905457808652395827)
  ·
    refine ⟨2937899858186712978593741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1958599905457808652395827 2937899858186712978593741)
    ·
      refine ⟨1101712446820017366972653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2937899858186712978593741 1101712446820017366972653)
      ·
        refine ⟨413142167557506512614745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1101712446820017366972653 413142167557506512614745)
        ·
          refine ⟨309856625668129884461059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413142167557506512614745 309856625668129884461059)
          ·
            refine ⟨464784938502194826691589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309856625668129884461059 464784938502194826691589)
            ·
              refine ⟨87147175969161530004673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 464784938502194826691589 87147175969161530004673)
              ·
                refine ⟨65360381976871147503505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87147175969161530004673 65360381976871147503505)
                ·
                  refine ⟨49020286482653360627629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65360381976871147503505 49020286482653360627629)
                  ·
                    rfl

theorem cell20_107400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 2].length) (baseStart_107400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107400 prefixEnd_107400 := by exact prefixLift 107400
  have htrace : WordTrace (prefixWord ++ tailWord_107400) baseStart_107400 baseEnd_107400 := by
    simpa [prefixWord, tailWord_107400, baseEnd_107400] using wordTrace_append hprefix tailTrace_107400
  have hstable : (prefixWord ++ tailWord_107400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107400).length < 2 ^ (prefixWord ++ tailWord_107400).sum := by decide
  have hdescent : baseEnd_107400 < baseStart_107400 := by decide
  rcases family_descends (prefixWord ++ tailWord_107400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107456 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 5]
def baseStart_107456 : Nat := 118140960795 + 107456 * 2 ^ 59
def prefixEnd_107456 : Nat := 4983230072969 + 3 ^ 40 * 107456 * 2
def baseEnd_107456 : Nat := 49045846408566054760733

theorem tailTrace_107456 : CollatzResearch.WordTrace tailWord_107456 prefixEnd_107456 49045846408566054760733 := by
  unfold tailWord_107456
  simp only [CollatzResearch.WordTrace]
  refine ⟨1959621149356369434415111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2612828199141825912553481 1959621149356369434415111)
  ·
    refine ⟨2939431724034554151622667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1959621149356369434415111 2939431724034554151622667)
    ·
      refine ⟨4409147586051831227434001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2939431724034554151622667 4409147586051831227434001)
      ·
        refine ⟨3306860689538873420575501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4409147586051831227434001 3306860689538873420575501)
        ·
          refine ⟨1240072758577077532715813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3306860689538873420575501 1240072758577077532715813)
          ·
            refine ⟨232513642233202037384215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1240072758577077532715813 232513642233202037384215)
            ·
              refine ⟨348770463349803056076323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232513642233202037384215 348770463349803056076323)
              ·
                refine ⟨523155695024704584114485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348770463349803056076323 523155695024704584114485)
                ·
                  refine ⟨49045846408566054760733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 523155695024704584114485 49045846408566054760733)
                  ·
                    rfl

theorem cell20_107456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_107456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107456 prefixEnd_107456 := by exact prefixLift 107456
  have htrace : WordTrace (prefixWord ++ tailWord_107456) baseStart_107456 baseEnd_107456 := by
    simpa [prefixWord, tailWord_107456, baseEnd_107456] using wordTrace_append hprefix tailTrace_107456
  have hstable : (prefixWord ++ tailWord_107456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107456).length < 2 ^ (prefixWord ++ tailWord_107456).sum := by decide
  have hdescent : baseEnd_107456 < baseStart_107456 := by decide
  rcases family_descends (prefixWord ++ tailWord_107456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107463 : List Nat := [1, 1, 4, 1, 1, 2, 3, 3, 4]
def baseStart_107463 : Nat := 118140960795 + 107463 * 2 ^ 59
def prefixEnd_107463 : Nat := 4983230072969 + 3 ^ 40 * 107463 * 2
def baseEnd_107463 : Nat := 49049041399305141527371

theorem tailTrace_107463 : CollatzResearch.WordTrace tailWord_107463 prefixEnd_107463 49049041399305141527371 := by
  unfold tailWord_107463
  simp only [CollatzResearch.WordTrace]
  refine ⟨3919497609687379064335043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2612998406458252709556695 3919497609687379064335043)
  ·
    refine ⟨5879246414531068596502565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3919497609687379064335043 5879246414531068596502565)
    ·
      refine ⟨1102358702724575361844231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5879246414531068596502565 1102358702724575361844231)
      ·
        refine ⟨1653538054086863042766347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1102358702724575361844231 1653538054086863042766347)
        ·
          refine ⟨2480307081130294564149521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1653538054086863042766347 2480307081130294564149521)
          ·
            refine ⟨1860230310847720923112141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2480307081130294564149521 1860230310847720923112141)
            ·
              refine ⟨697586366567895346167053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1860230310847720923112141 697586366567895346167053)
              ·
                refine ⟨261594887462960754812645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 697586366567895346167053 261594887462960754812645)
                ·
                  refine ⟨49049041399305141527371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 261594887462960754812645 49049041399305141527371)
                  ·
                    rfl

theorem cell20_107463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_107463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107463 prefixEnd_107463 := by exact prefixLift 107463
  have htrace : WordTrace (prefixWord ++ tailWord_107463) baseStart_107463 baseEnd_107463 := by
    simpa [prefixWord, tailWord_107463, baseEnd_107463] using wordTrace_append hprefix tailTrace_107463
  have hstable : (prefixWord ++ tailWord_107463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107463).length < 2 ^ (prefixWord ++ tailWord_107463).sum := by decide
  have hdescent : baseEnd_107463 < baseStart_107463 := by decide
  rcases family_descends (prefixWord ++ tailWord_107463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107473 : List Nat := [1, 2, 2, 1, 2, 1, 7, 1, 3]
def baseStart_107473 : Nat := 118140960795 + 107473 * 2 ^ 59
def prefixEnd_107473 : Nat := 4983230072969 + 3 ^ 40 * 107473 * 2
def baseEnd_107473 : Nat := 49053605671789551193997

theorem tailTrace_107473 : CollatzResearch.WordTrace tailWord_107473 prefixEnd_107473 49053605671789551193997 := by
  unfold tailWord_107473
  simp only [CollatzResearch.WordTrace]
  refine ⟨3919862339651150772199073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2613241559767433848132715 3919862339651150772199073)
  ·
    refine ⟨2939896754738363079149305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3919862339651150772199073 2939896754738363079149305)
    ·
      refine ⟨2204922566053772309361979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2939896754738363079149305 2204922566053772309361979)
      ·
        refine ⟨3307383849080658464042969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2204922566053772309361979 3307383849080658464042969)
        ·
          refine ⟨2480537886810493848032227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3307383849080658464042969 2480537886810493848032227)
          ·
            refine ⟨3720806830215740772048341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2480537886810493848032227 3720806830215740772048341)
            ·
              refine ⟨87206410083181424344883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3720806830215740772048341 87206410083181424344883)
              ·
                refine ⟨130809615124772136517325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87206410083181424344883 130809615124772136517325)
                ·
                  refine ⟨49053605671789551193997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130809615124772136517325 49053605671789551193997)
                  ·
                    rfl

theorem cell20_107473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 3].length) (baseStart_107473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107473 prefixEnd_107473 := by exact prefixLift 107473
  have htrace : WordTrace (prefixWord ++ tailWord_107473) baseStart_107473 baseEnd_107473 := by
    simpa [prefixWord, tailWord_107473, baseEnd_107473] using wordTrace_append hprefix tailTrace_107473
  have hstable : (prefixWord ++ tailWord_107473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107473).length < 2 ^ (prefixWord ++ tailWord_107473).sum := by decide
  have hdescent : baseEnd_107473 < baseStart_107473 := by decide
  rcases family_descends (prefixWord ++ tailWord_107473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107487 : List Nat := [1, 1, 2, 3, 5, 1, 1, 6]
def baseStart_107487 : Nat := 118140960795 + 107487 * 2 ^ 59
def prefixEnd_107487 : Nat := 4983230072969 + 3 ^ 40 * 107487 * 2
def baseEnd_107487 : Nat := 16353331884422574909091

theorem tailTrace_107487 : CollatzResearch.WordTrace tailWord_107487 prefixEnd_107487 16353331884422574909091 := by
  unfold tailWord_107487
  simp only [CollatzResearch.WordTrace]
  refine ⟨3920372961600431163208715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2613581974400287442139143 3920372961600431163208715)
  ·
    refine ⟨5880559442400646744813073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3920372961600431163208715 5880559442400646744813073)
    ·
      refine ⟨4410419581800485058609805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5880559442400646744813073 4410419581800485058609805)
      ·
        refine ⟨1653907343175181896978677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4410419581800485058609805 1653907343175181896978677)
        ·
          refine ⟨155053813422673302841751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1653907343175181896978677 155053813422673302841751)
          ·
            refine ⟨232580720134009954262627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155053813422673302841751 232580720134009954262627)
            ·
              refine ⟨348871080201014931393941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232580720134009954262627 348871080201014931393941)
              ·
                refine ⟨16353331884422574909091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 348871080201014931393941 16353331884422574909091)
                ·
                  rfl

theorem cell20_107487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 6].length) (baseStart_107487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107487 prefixEnd_107487 := by exact prefixLift 107487
  have htrace : WordTrace (prefixWord ++ tailWord_107487) baseStart_107487 baseEnd_107487 := by
    simpa [prefixWord, tailWord_107487, baseEnd_107487] using wordTrace_append hprefix tailTrace_107487
  have hstable : (prefixWord ++ tailWord_107487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107487).length < 2 ^ (prefixWord ++ tailWord_107487).sum := by decide
  have hdescent : baseEnd_107487 < baseStart_107487 := by decide
  rcases family_descends (prefixWord ++ tailWord_107487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107493 : List Nat := [1, 3, 1, 6, 1, 2, 1, 3, 2]
def baseStart_107493 : Nat := 118140960795 + 107493 * 2 ^ 59
def prefixEnd_107493 : Nat := 4983230072969 + 3 ^ 40 * 107493 * 2
def baseEnd_107493 : Nat := 49062734216758370527249

theorem tailTrace_107493 : CollatzResearch.WordTrace tailWord_107493 prefixEnd_107493 49062734216758370527249 := by
  unfold tailWord_107493
  simp only [CollatzResearch.WordTrace]
  refine ⟨3920591799578694187927133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2613727866385796125284755 3920591799578694187927133)
  ·
    refine ⟨1470221924842010320472675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3920591799578694187927133 1470221924842010320472675)
    ·
      refine ⟨2205332887263015480709013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1470221924842010320472675 2205332887263015480709013)
      ·
        refine ⟨103374979090453850658235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2205332887263015480709013 103374979090453850658235)
        ·
          refine ⟨155062468635680775987353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103374979090453850658235 155062468635680775987353)
          ·
            refine ⟨116296851476760581990515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155062468635680775987353 116296851476760581990515)
            ·
              refine ⟨174445277215140872985773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116296851476760581990515 174445277215140872985773)
              ·
                refine ⟨65416978955677827369665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174445277215140872985773 65416978955677827369665)
                ·
                  refine ⟨49062734216758370527249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65416978955677827369665 49062734216758370527249)
                  ·
                    rfl

theorem cell20_107493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_107493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107493 prefixEnd_107493 := by exact prefixLift 107493
  have htrace : WordTrace (prefixWord ++ tailWord_107493) baseStart_107493 baseEnd_107493 := by
    simpa [prefixWord, tailWord_107493, baseEnd_107493] using wordTrace_append hprefix tailTrace_107493
  have hstable : (prefixWord ++ tailWord_107493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107493).length < 2 ^ (prefixWord ++ tailWord_107493).sum := by decide
  have hdescent : baseEnd_107493 < baseStart_107493 := by decide
  rcases family_descends (prefixWord ++ tailWord_107493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107528 : List Nat := [2, 1, 3, 2, 1, 5, 2, 1, 3]
def baseStart_107528 : Nat := 118140960795 + 107528 * 2 ^ 59
def prefixEnd_107528 : Nat := 4983230072969 + 3 ^ 40 * 107528 * 2
def baseEnd_107528 : Nat := 49078709170453804360439

theorem tailTrace_107528 : CollatzResearch.WordTrace tailWord_107528 prefixEnd_107528 49078709170453804360439 := by
  unfold tailWord_107528
  simp only [CollatzResearch.WordTrace]
  refine ⟨1960934177225947582725619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2614578902967930110300825 1960934177225947582725619)
  ·
    refine ⟨2941401265838921374088429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1960934177225947582725619 2941401265838921374088429)
    ·
      refine ⟨1103025474689595515283161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2941401265838921374088429 1103025474689595515283161)
      ·
        refine ⟨827269106017196636462371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1103025474689595515283161 827269106017196636462371)
        ·
          refine ⟨1240903659025794954693557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827269106017196636462371 1240903659025794954693557)
          ·
            refine ⟨116334718033668277002521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1240903659025794954693557 116334718033668277002521)
            ·
              refine ⟨87251038525251207751891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116334718033668277002521 87251038525251207751891)
              ·
                refine ⟨130876557787876811627837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87251038525251207751891 130876557787876811627837)
                ·
                  refine ⟨49078709170453804360439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130876557787876811627837 49078709170453804360439)
                  ·
                    rfl

theorem cell20_107528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 3].length) (baseStart_107528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107528 prefixEnd_107528 := by exact prefixLift 107528
  have htrace : WordTrace (prefixWord ++ tailWord_107528) baseStart_107528 baseEnd_107528 := by
    simpa [prefixWord, tailWord_107528, baseEnd_107528] using wordTrace_append hprefix tailTrace_107528
  have hstable : (prefixWord ++ tailWord_107528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107528).length < 2 ^ (prefixWord ++ tailWord_107528).sum := by decide
  have hdescent : baseEnd_107528 < baseStart_107528 := by decide
  rcases family_descends (prefixWord ++ tailWord_107528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107546 : List Nat := [3, 1, 1, 3, 1, 2, 1, 8]
def baseStart_107546 : Nat := 118140960795 + 107546 * 2 ^ 59
def prefixEnd_107546 : Nat := 4983230072969 + 3 ^ 40 * 107546 * 2
def baseEnd_107546 : Nat := 16362308286975247253455

theorem tailTrace_107546 : CollatzResearch.WordTrace tailWord_107546 prefixEnd_107546 16362308286975247253455 := by
  unfold tailWord_107546
  simp only [CollatzResearch.WordTrace]
  refine ⟨980631217096671059901623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2615016578924456159737661 980631217096671059901623)
  ·
    refine ⟨1470946825645006589852435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 980631217096671059901623 1470946825645006589852435)
    ·
      refine ⟨2206420238467509884778653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1470946825645006589852435 2206420238467509884778653)
      ·
        refine ⟨827407589425316206791995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2206420238467509884778653 827407589425316206791995)
        ·
          refine ⟨1241111384137974310187993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827407589425316206791995 1241111384137974310187993)
          ·
            refine ⟨930833538103480732640995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1241111384137974310187993 930833538103480732640995)
            ·
              refine ⟨1396250307155221098961493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930833538103480732640995 1396250307155221098961493)
              ·
                refine ⟨16362308286975247253455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1396250307155221098961493 16362308286975247253455)
                ·
                  rfl

theorem cell20_107546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_107546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107546 prefixEnd_107546 := by exact prefixLift 107546
  have htrace : WordTrace (prefixWord ++ tailWord_107546) baseStart_107546 baseEnd_107546 := by
    simpa [prefixWord, tailWord_107546, baseEnd_107546] using wordTrace_append hprefix tailTrace_107546
  have hstable : (prefixWord ++ tailWord_107546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107546).length < 2 ^ (prefixWord ++ tailWord_107546).sum := by decide
  have hdescent : baseEnd_107546 < baseStart_107546 := by decide
  rcases family_descends (prefixWord ++ tailWord_107546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107625 : List Nat := [1, 2, 1, 1, 1, 8, 1, 2, 3]
def baseStart_107625 : Nat := 118140960795 + 107625 * 2 ^ 59
def prefixEnd_107625 : Nat := 4983230072969 + 3 ^ 40 * 107625 * 2
def baseEnd_107625 : Nat := 49122982613552578126709

theorem tailTrace_107625 : CollatzResearch.WordTrace tailWord_107625 prefixEnd_107625 49122982613552578126709 := by
  unfold tailWord_107625
  simp only [CollatzResearch.WordTrace]
  refine ⟨3925406235100480731732329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2616937490066987154488219 3925406235100480731732329)
  ·
    refine ⟨2944054676325360548799247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3925406235100480731732329 2944054676325360548799247)
    ·
      refine ⟨4416082014488040823198871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2944054676325360548799247 4416082014488040823198871)
      ·
        refine ⟨6624123021732061234798307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4416082014488040823198871 6624123021732061234798307)
        ·
          refine ⟨9936184532598091852197461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6624123021732061234798307 9936184532598091852197461)
          ·
            refine ⟨116439662491383888892939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 9936184532598091852197461 116439662491383888892939)
            ·
              refine ⟨174659493737075833339409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116439662491383888892939 174659493737075833339409)
              ·
                refine ⟨130994620302806875004557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174659493737075833339409 130994620302806875004557)
                ·
                  refine ⟨49122982613552578126709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130994620302806875004557 49122982613552578126709)
                  ·
                    rfl

theorem cell20_107625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 3].length) (baseStart_107625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107625 prefixEnd_107625 := by exact prefixLift 107625
  have htrace : WordTrace (prefixWord ++ tailWord_107625) baseStart_107625 baseEnd_107625 := by
    simpa [prefixWord, tailWord_107625, baseEnd_107625] using wordTrace_append hprefix tailTrace_107625
  have hstable : (prefixWord ++ tailWord_107625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107625).length < 2 ^ (prefixWord ++ tailWord_107625).sum := by decide
  have hdescent : baseEnd_107625 < baseStart_107625 := by decide
  rcases family_descends (prefixWord ++ tailWord_107625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107632 : List Nat := [2, 1, 1, 1, 5, 1, 1, 6, 2]
def baseStart_107632 : Nat := 118140960795 + 107632 * 2 ^ 59
def prefixEnd_107632 : Nat := 4983230072969 + 3 ^ 40 * 107632 * 2
def baseEnd_107632 : Nat := 49126177604291664893347

theorem tailTrace_107632 : CollatzResearch.WordTrace tailWord_107632 prefixEnd_107632 49126177604291664893347 := by
  unfold tailWord_107632
  simp only [CollatzResearch.WordTrace]
  refine ⟨1962830773037560463618575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2617107697383413951491433 1962830773037560463618575)
  ·
    refine ⟨2944246159556340695427863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1962830773037560463618575 2944246159556340695427863)
    ·
      refine ⟨4416369239334511043141795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2944246159556340695427863 4416369239334511043141795)
      ·
        refine ⟨6624553859001766564712693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4416369239334511043141795 6624553859001766564712693)
        ·
          refine ⟨621051924281415615441815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6624553859001766564712693 621051924281415615441815)
          ·
            refine ⟨931577886422123423162723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621051924281415615441815 931577886422123423162723)
            ·
              refine ⟨1397366829633185134744085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 931577886422123423162723 1397366829633185134744085)
              ·
                refine ⟨65501570139055553191129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1397366829633185134744085 65501570139055553191129)
                ·
                  refine ⟨49126177604291664893347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65501570139055553191129 49126177604291664893347)
                  ·
                    rfl

theorem cell20_107632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 2].length) (baseStart_107632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107632 prefixEnd_107632 := by exact prefixLift 107632
  have htrace : WordTrace (prefixWord ++ tailWord_107632) baseStart_107632 baseEnd_107632 := by
    simpa [prefixWord, tailWord_107632, baseEnd_107632] using wordTrace_append hprefix tailTrace_107632
  have hstable : (prefixWord ++ tailWord_107632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107632).length < 2 ^ (prefixWord ++ tailWord_107632).sum := by decide
  have hdescent : baseEnd_107632 < baseStart_107632 := by decide
  rcases family_descends (prefixWord ++ tailWord_107632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107666 : List Nat := [3, 2, 3, 1, 1, 4, 1, 3, 2]
def baseStart_107666 : Nat := 118140960795 + 107666 * 2 ^ 59
def prefixEnd_107666 : Nat := 4983230072969 + 3 ^ 40 * 107666 * 2
def baseEnd_107666 : Nat := 49141696130738657759875

theorem tailTrace_107666 : CollatzResearch.WordTrace tailWord_107666 prefixEnd_107666 49141696130738657759875 := by
  unfold tailWord_107666
  simp only [CollatzResearch.WordTrace]
  refine ⟨981725406987986183493713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2617934418634629822649901 981725406987986183493713)
  ·
    refine ⟨736294055240989637620285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 981725406987986183493713 736294055240989637620285)
    ·
      refine ⟨276110270715371114107607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 736294055240989637620285 276110270715371114107607)
      ·
        refine ⟨414165406073056671161411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276110270715371114107607 414165406073056671161411)
        ·
          refine ⟨621248109109585006742117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414165406073056671161411 621248109109585006742117)
          ·
            refine ⟨116484020458047188764147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 621248109109585006742117 116484020458047188764147)
            ·
              refine ⟨174726030687070783146221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116484020458047188764147 174726030687070783146221)
              ·
                refine ⟨65522261507651543679833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174726030687070783146221 65522261507651543679833)
                ·
                  refine ⟨49141696130738657759875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65522261507651543679833 49141696130738657759875)
                  ·
                    rfl

theorem cell20_107666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_107666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107666 prefixEnd_107666 := by exact prefixLift 107666
  have htrace : WordTrace (prefixWord ++ tailWord_107666) baseStart_107666 baseEnd_107666 := by
    simpa [prefixWord, tailWord_107666, baseEnd_107666] using wordTrace_append hprefix tailTrace_107666
  have hstable : (prefixWord ++ tailWord_107666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107666).length < 2 ^ (prefixWord ++ tailWord_107666).sum := by decide
  have hdescent : baseEnd_107666 < baseStart_107666 := by decide
  rcases family_descends (prefixWord ++ tailWord_107666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107667 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 5]
def baseStart_107667 : Nat := 118140960795 + 107667 * 2 ^ 59
def prefixEnd_107667 : Nat := 4983230072969 + 3 ^ 40 * 107667 * 2
def baseEnd_107667 : Nat := 49142152557987098726537

theorem tailTrace_107667 : CollatzResearch.WordTrace tailWord_107667 prefixEnd_107667 49142152557987098726537 := by
  unfold tailWord_107667
  simp only [CollatzResearch.WordTrace]
  refine ⟨3926938100948321904761255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2617958733965547936507503 3926938100948321904761255)
  ·
    refine ⟨5890407151422482857141883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3926938100948321904761255 5890407151422482857141883)
    ·
      refine ⟨8835610727133724285712825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5890407151422482857141883 8835610727133724285712825)
      ·
        refine ⟨6626708045350293214284619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8835610727133724285712825 6626708045350293214284619)
        ·
          refine ⟨9940062068025439821426929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6626708045350293214284619 9940062068025439821426929)
          ·
            refine ⟨7455046551019079866070197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9940062068025439821426929 7455046551019079866070197)
            ·
              refine ⟨698910614158038737444081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7455046551019079866070197 698910614158038737444081)
              ·
                refine ⟨524182960618529053083061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698910614158038737444081 524182960618529053083061)
                ·
                  refine ⟨49142152557987098726537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 524182960618529053083061 49142152557987098726537)
                  ·
                    rfl

theorem cell20_107667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_107667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107667 prefixEnd_107667 := by exact prefixLift 107667
  have htrace : WordTrace (prefixWord ++ tailWord_107667) baseStart_107667 baseEnd_107667 := by
    simpa [prefixWord, tailWord_107667, baseEnd_107667] using wordTrace_append hprefix tailTrace_107667
  have hstable : (prefixWord ++ tailWord_107667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107667).length < 2 ^ (prefixWord ++ tailWord_107667).sum := by decide
  have hdescent : baseEnd_107667 < baseStart_107667 := by decide
  rcases family_descends (prefixWord ++ tailWord_107667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107684 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 5]
def baseStart_107684 : Nat := 118140960795 + 107684 * 2 ^ 59
def prefixEnd_107684 : Nat := 4983230072969 + 3 ^ 40 * 107684 * 2
def baseEnd_107684 : Nat := 49149911821210595159801

theorem tailTrace_107684 : CollatzResearch.WordTrace tailWord_107684 prefixEnd_107684 49149911821210595159801 := by
  unfold tailWord_107684
  simp only [CollatzResearch.WordTrace]
  refine ⟨1963779070943366904065053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2618372094591155872086737 1963779070943366904065053)
  ·
    refine ⟨736417151603762589024395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1963779070943366904065053 736417151603762589024395)
    ·
      refine ⟨1104625727405643883536593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 736417151603762589024395 1104625727405643883536593)
      ·
        refine ⟨828469295554232912652445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1104625727405643883536593 828469295554232912652445)
        ·
          refine ⟨310675985832837342244667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 828469295554232912652445 310675985832837342244667)
          ·
            refine ⟨466013978749256013367001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310675985832837342244667 466013978749256013367001)
            ·
              refine ⟨349510484061942010025251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466013978749256013367001 349510484061942010025251)
              ·
                refine ⟨524265726092913015037877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349510484061942010025251 524265726092913015037877)
                ·
                  refine ⟨49149911821210595159801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 524265726092913015037877 49149911821210595159801)
                  ·
                    rfl

theorem cell20_107684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_107684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107684 prefixEnd_107684 := by exact prefixLift 107684
  have htrace : WordTrace (prefixWord ++ tailWord_107684) baseStart_107684 baseEnd_107684 := by
    simpa [prefixWord, tailWord_107684, baseEnd_107684] using wordTrace_append hprefix tailTrace_107684
  have hstable : (prefixWord ++ tailWord_107684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107684).length < 2 ^ (prefixWord ++ tailWord_107684).sum := by decide
  have hdescent : baseEnd_107684 < baseStart_107684 := by decide
  rcases family_descends (prefixWord ++ tailWord_107684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107687 : List Nat := [1, 1, 6, 2, 1, 3, 1, 1, 4]
def baseStart_107687 : Nat := 118140960795 + 107687 * 2 ^ 59
def prefixEnd_107687 : Nat := 4983230072969 + 3 ^ 40 * 107687 * 2
def baseEnd_107687 : Nat := 49151281102955918059789

theorem tailTrace_107687 : CollatzResearch.WordTrace tailWord_107687 prefixEnd_107687 49151281102955918059789 := by
  unfold tailWord_107687
  simp only [CollatzResearch.WordTrace]
  refine ⟨3927667560875865320489315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2618445040583910213659543 3927667560875865320489315)
  ·
    refine ⟨5891501341313797980733973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3927667560875865320489315 5891501341313797980733973)
    ·
      refine ⟨276164125374084280346905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5891501341313797980733973 276164125374084280346905)
      ·
        refine ⟨207123094030563210260179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276164125374084280346905 207123094030563210260179)
        ·
          refine ⟨310684641045844815390269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207123094030563210260179 310684641045844815390269)
          ·
            refine ⟨116506740392191805771351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310684641045844815390269 116506740392191805771351)
            ·
              refine ⟨174760110588287708657027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116506740392191805771351 174760110588287708657027)
              ·
                refine ⟨262140165882431562985541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174760110588287708657027 262140165882431562985541)
                ·
                  refine ⟨49151281102955918059789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 262140165882431562985541 49151281102955918059789)
                  ·
                    rfl

theorem cell20_107687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 4].length) (baseStart_107687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107687 prefixEnd_107687 := by exact prefixLift 107687
  have htrace : WordTrace (prefixWord ++ tailWord_107687) baseStart_107687 baseEnd_107687 := by
    simpa [prefixWord, tailWord_107687, baseEnd_107687] using wordTrace_append hprefix tailTrace_107687
  have hstable : (prefixWord ++ tailWord_107687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107687).length < 2 ^ (prefixWord ++ tailWord_107687).sum := by decide
  have hdescent : baseEnd_107687 < baseStart_107687 := by decide
  rcases family_descends (prefixWord ++ tailWord_107687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107698 : List Nat := [3, 2, 1, 1, 1, 4, 1, 7]
def baseStart_107698 : Nat := 118140960795 + 107698 * 2 ^ 59
def prefixEnd_107698 : Nat := 4983230072969 + 3 ^ 40 * 107698 * 2
def baseEnd_107698 : Nat := 16385433934229589564359

theorem tailTrace_107698 : CollatzResearch.WordTrace tailWord_107698 prefixEnd_107698 16385433934229589564359 := by
  unfold tailWord_107698
  simp only [CollatzResearch.WordTrace]
  refine ⟨982017190959003549784937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2618712509224009466093165 982017190959003549784937)
  ·
    refine ⟨736512893219252662338703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 982017190959003549784937 736512893219252662338703)
    ·
      refine ⟨1104769339828878993508055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 736512893219252662338703 1104769339828878993508055)
      ·
        refine ⟨1657154009743318490262083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104769339828878993508055 1657154009743318490262083)
        ·
          refine ⟨2485731014614977735393125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1657154009743318490262083 2485731014614977735393125)
          ·
            refine ⟨466074565240308325386211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2485731014614977735393125 466074565240308325386211)
            ·
              refine ⟨699111847860462488079317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466074565240308325386211 699111847860462488079317)
              ·
                refine ⟨16385433934229589564359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 699111847860462488079317 16385433934229589564359)
                ·
                  rfl

theorem cell20_107698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_107698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107698 prefixEnd_107698 := by exact prefixLift 107698
  have htrace : WordTrace (prefixWord ++ tailWord_107698) baseStart_107698 baseEnd_107698 := by
    simpa [prefixWord, tailWord_107698, baseEnd_107698] using wordTrace_append hprefix tailTrace_107698
  have hstable : (prefixWord ++ tailWord_107698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107698).length < 2 ^ (prefixWord ++ tailWord_107698).sum := by decide
  have hdescent : baseEnd_107698 < baseStart_107698 := by decide
  rcases family_descends (prefixWord ++ tailWord_107698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107732 : List Nat := [2, 4, 1, 4, 2, 7]
def baseStart_107732 : Nat := 118140960795 + 107732 * 2 ^ 59
def prefixEnd_107732 : Nat := 4983230072969 + 3 ^ 40 * 107732 * 2
def baseEnd_107732 : Nat := 1821178530708731909615

theorem tailTrace_107732 : CollatzResearch.WordTrace tailWord_107732 prefixEnd_107732 1821178530708731909615 := by
  unfold tailWord_107732
  simp only [CollatzResearch.WordTrace]
  refine ⟨1964654422856419002938725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2619539230475225337251633 1964654422856419002938725)
  ·
    refine ⟨368372704285578563051011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1964654422856419002938725 368372704285578563051011)
    ·
      refine ⟨552559056428367844576517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368372704285578563051011 552559056428367844576517)
      ·
        refine ⟨103604823080318970858097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 552559056428367844576517 103604823080318970858097)
        ·
          refine ⟨77703617310239228143573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103604823080318970858097 77703617310239228143573)
          ·
            refine ⟨1821178530708731909615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 77703617310239228143573 1821178530708731909615)
            ·
              rfl

theorem cell20_107732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 7].length) (baseStart_107732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107732 prefixEnd_107732 := by exact prefixLift 107732
  have htrace : WordTrace (prefixWord ++ tailWord_107732) baseStart_107732 baseEnd_107732 := by
    simpa [prefixWord, tailWord_107732, baseEnd_107732] using wordTrace_append hprefix tailTrace_107732
  have hstable : (prefixWord ++ tailWord_107732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107732).length < 2 ^ (prefixWord ++ tailWord_107732).sum := by decide
  have hdescent : baseEnd_107732 < baseStart_107732 := by decide
  rcases family_descends (prefixWord ++ tailWord_107732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107736 : List Nat := [2, 1, 2, 2, 5, 8]
def baseStart_107736 : Nat := 118140960795 + 107736 * 2 ^ 59
def prefixEnd_107736 : Nat := 4983230072969 + 3 ^ 40 * 107736 * 2
def baseEnd_107736 : Nat := 1821246149560352793565

theorem tailTrace_107736 : CollatzResearch.WordTrace tailWord_107736 prefixEnd_107736 1821246149560352793565 := by
  unfold tailWord_107736
  simp only [CollatzResearch.WordTrace]
  refine ⟨1964727368849173344511531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2619636491798897792682041 1964727368849173344511531)
  ·
    refine ⟨2947091053273760016767297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1964727368849173344511531 2947091053273760016767297)
    ·
      refine ⟨2210318289955320012575473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2947091053273760016767297 2210318289955320012575473)
      ·
        refine ⟨1657738717466490009431605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2210318289955320012575473 1657738717466490009431605)
        ·
          refine ⟨155413004762483438384213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1657738717466490009431605 155413004762483438384213)
          ·
            refine ⟨1821246149560352793565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 155413004762483438384213 1821246149560352793565)
            ·
              rfl

theorem cell20_107736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 8].length) (baseStart_107736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107736 prefixEnd_107736 := by exact prefixLift 107736
  have htrace : WordTrace (prefixWord ++ tailWord_107736) baseStart_107736 baseEnd_107736 := by
    simpa [prefixWord, tailWord_107736, baseEnd_107736] using wordTrace_append hprefix tailTrace_107736
  have hstable : (prefixWord ++ tailWord_107736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107736).length < 2 ^ (prefixWord ++ tailWord_107736).sum := by decide
  have hdescent : baseEnd_107736 < baseStart_107736 := by decide
  rcases family_descends (prefixWord ++ tailWord_107736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107743 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 5]
def baseStart_107743 : Nat := 118140960795 + 107743 * 2 ^ 59
def prefixEnd_107743 : Nat := 4983230072969 + 3 ^ 40 * 107743 * 2
def baseEnd_107743 : Nat := 49176841028868612192893

theorem tailTrace_107743 : CollatzResearch.WordTrace tailWord_107743 prefixEnd_107743 49176841028868612192893 := by
  unfold tailWord_107743
  simp only [CollatzResearch.WordTrace]
  refine ⟨3929710048672986884527883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2619806699115324589685255 3929710048672986884527883)
  ·
    refine ⟨5894565073009480326791825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3929710048672986884527883 5894565073009480326791825)
    ·
      refine ⟨4420923804757110245093869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5894565073009480326791825 4420923804757110245093869)
      ·
        refine ⟨1657846426783916341910201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4420923804757110245093869 1657846426783916341910201)
        ·
          refine ⟨1243384820087937256432651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1657846426783916341910201 1243384820087937256432651)
          ·
            refine ⟨1865077230131905884648977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243384820087937256432651 1865077230131905884648977)
            ·
              refine ⟨1398807922598929413486733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1865077230131905884648977 1398807922598929413486733)
              ·
                refine ⟨524552970974598530057525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1398807922598929413486733 524552970974598530057525)
                ·
                  refine ⟨49176841028868612192893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 524552970974598530057525 49176841028868612192893)
                  ·
                    rfl

theorem cell20_107743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_107743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107743 prefixEnd_107743 := by exact prefixLift 107743
  have htrace : WordTrace (prefixWord ++ tailWord_107743) baseStart_107743 baseEnd_107743 := by
    simpa [prefixWord, tailWord_107743, baseEnd_107743] using wordTrace_append hprefix tailTrace_107743
  have hstable : (prefixWord ++ tailWord_107743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107743).length < 2 ^ (prefixWord ++ tailWord_107743).sum := by decide
  have hdescent : baseEnd_107743 < baseStart_107743 := by decide
  rcases family_descends (prefixWord ++ tailWord_107743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107781 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 5]
def baseStart_107781 : Nat := 118140960795 + 107781 * 2 ^ 59
def prefixEnd_107781 : Nat := 4983230072969 + 3 ^ 40 * 107781 * 2
def baseEnd_107781 : Nat := 49194185264309368926071

theorem tailTrace_107781 : CollatzResearch.WordTrace tailWord_107781 prefixEnd_107781 49194185264309368926071 := by
  unfold tailWord_107781
  simp only [CollatzResearch.WordTrace]
  refine ⟨3931096022535319374411197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2620730681690212916274131 3931096022535319374411197)
  ·
    refine ⟨1474161008450744765404199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3931096022535319374411197 1474161008450744765404199)
    ·
      refine ⟨2211241512676117148106299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1474161008450744765404199 2211241512676117148106299)
      ·
        refine ⟨3316862269014175722159449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2211241512676117148106299 3316862269014175722159449)
        ·
          refine ⟨2487646701760631791619587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3316862269014175722159449 2487646701760631791619587)
          ·
            refine ⟨3731470052640947687429381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487646701760631791619587 3731470052640947687429381)
            ·
              refine ⟨699650634870177691393009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3731470052640947687429381 699650634870177691393009)
              ·
                refine ⟨524737976152633268544757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 699650634870177691393009 524737976152633268544757)
                ·
                  refine ⟨49194185264309368926071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 524737976152633268544757 49194185264309368926071)
                  ·
                    rfl

theorem cell20_107781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_107781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107781 prefixEnd_107781 := by exact prefixLift 107781
  have htrace : WordTrace (prefixWord ++ tailWord_107781) baseStart_107781 baseEnd_107781 := by
    simpa [prefixWord, tailWord_107781, baseEnd_107781] using wordTrace_append hprefix tailTrace_107781
  have hstable : (prefixWord ++ tailWord_107781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107781).length < 2 ^ (prefixWord ++ tailWord_107781).sum := by decide
  have hdescent : baseEnd_107781 < baseStart_107781 := by decide
  rcases family_descends (prefixWord ++ tailWord_107781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107794 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 5]
def baseStart_107794 : Nat := 118140960795 + 107794 * 2 ^ 59
def prefixEnd_107794 : Nat := 4983230072969 + 3 ^ 40 * 107794 * 2
def baseEnd_107794 : Nat := 49200118818539101492685

theorem tailTrace_107794 : CollatzResearch.WordTrace tailWord_107794 prefixEnd_107794 49200118818539101492685 := by
  unfold tailWord_107794
  simp only [CollatzResearch.WordTrace]
  refine ⟨982892542872055648658609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2621046780992148396422957 982892542872055648658609)
  ·
    refine ⟨737169407154041736493957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 982892542872055648658609 737169407154041736493957)
    ·
      refine ⟨138219263841382825592617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 737169407154041736493957 138219263841382825592617)
      ·
        refine ⟨103664447881037119194463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138219263841382825592617 103664447881037119194463)
        ·
          refine ⟨155496671821555678791695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103664447881037119194463 155496671821555678791695)
          ·
            refine ⟨233245007732333518187543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155496671821555678791695 233245007732333518187543)
            ·
              refine ⟨349867511598500277281315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233245007732333518187543 349867511598500277281315)
              ·
                refine ⟨524801267397750415921973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349867511598500277281315 524801267397750415921973)
                ·
                  refine ⟨49200118818539101492685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 524801267397750415921973 49200118818539101492685)
                  ·
                    rfl

theorem cell20_107794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_107794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107794 prefixEnd_107794 := by exact prefixLift 107794
  have htrace : WordTrace (prefixWord ++ tailWord_107794) baseStart_107794 baseEnd_107794 := by
    simpa [prefixWord, tailWord_107794, baseEnd_107794] using wordTrace_append hprefix tailTrace_107794
  have hstable : (prefixWord ++ tailWord_107794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107794).length < 2 ^ (prefixWord ++ tailWord_107794).sum := by decide
  have hdescent : baseEnd_107794 < baseStart_107794 := by decide
  rcases family_descends (prefixWord ++ tailWord_107794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107812 : List Nat := [2, 3, 1, 3, 1, 1, 2, 7]
def baseStart_107812 : Nat := 118140960795 + 107812 * 2 ^ 59
def prefixEnd_107812 : Nat := 4983230072969 + 3 ^ 40 * 107812 * 2
def baseEnd_107812 : Nat := 16402778169670346297537

theorem tailTrace_107812 : CollatzResearch.WordTrace tailWord_107812 prefixEnd_107812 16402778169670346297537 := by
  unfold tailWord_107812
  simp only [CollatzResearch.WordTrace]
  refine ⟨1966113342711505834394845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2621484456948674445859793 1966113342711505834394845)
  ·
    refine ⟨737292503516814687898067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1966113342711505834394845 737292503516814687898067)
    ·
      refine ⟨1105938755275222031847101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 737292503516814687898067 1105938755275222031847101)
      ·
        refine ⟨414727033228208261942663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1105938755275222031847101 414727033228208261942663)
        ·
          refine ⟨622090549842312392913995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414727033228208261942663 622090549842312392913995)
          ·
            refine ⟨933135824763468589370993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622090549842312392913995 933135824763468589370993)
            ·
              refine ⟨699851868572601442028245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 933135824763468589370993 699851868572601442028245)
              ·
                refine ⟨16402778169670346297537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 699851868572601442028245 16402778169670346297537)
                ·
                  rfl

theorem cell20_107812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_107812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107812 prefixEnd_107812 := by exact prefixLift 107812
  have htrace : WordTrace (prefixWord ++ tailWord_107812) baseStart_107812 baseEnd_107812 := by
    simpa [prefixWord, tailWord_107812, baseEnd_107812] using wordTrace_append hprefix tailTrace_107812
  have hstable : (prefixWord ++ tailWord_107812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107812).length < 2 ^ (prefixWord ++ tailWord_107812).sum := by decide
  have hdescent : baseEnd_107812 < baseStart_107812 := by decide
  rcases family_descends (prefixWord ++ tailWord_107812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107829 : List Nat := [1, 3, 3, 1, 2, 2, 4, 4]
def baseStart_107829 : Nat := 118140960795 + 107829 * 2 ^ 59
def prefixEnd_107829 : Nat := 4983230072969 + 3 ^ 40 * 107829 * 2
def baseEnd_107829 : Nat := 16405364590744845108625

theorem tailTrace_107829 : CollatzResearch.WordTrace tailWord_107829 prefixEnd_107829 16405364590744845108625 := by
  unfold tailWord_107829
  simp only [CollatzResearch.WordTrace]
  refine ⟨3932846726361423572158541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2621897817574282381439027 3932846726361423572158541)
  ·
    refine ⟨1474817522385533839559453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3932846726361423572158541 1474817522385533839559453)
    ·
      refine ⟨553056570894575189834795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1474817522385533839559453 553056570894575189834795)
      ·
        refine ⟨829584856341862784752193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553056570894575189834795 829584856341862784752193)
        ·
          refine ⟨622188642256397088564145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 829584856341862784752193 622188642256397088564145)
          ·
            refine ⟨466641481692297816423109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622188642256397088564145 466641481692297816423109)
            ·
              refine ⟨87495277817305840579333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 466641481692297816423109 87495277817305840579333)
              ·
                refine ⟨16405364590744845108625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87495277817305840579333 16405364590744845108625)
                ·
                  rfl

theorem cell20_107829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 4].length) (baseStart_107829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107829 prefixEnd_107829 := by exact prefixLift 107829
  have htrace : WordTrace (prefixWord ++ tailWord_107829) baseStart_107829 baseEnd_107829 := by
    simpa [prefixWord, tailWord_107829, baseEnd_107829] using wordTrace_append hprefix tailTrace_107829
  have hstable : (prefixWord ++ tailWord_107829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107829).length < 2 ^ (prefixWord ++ tailWord_107829).sum := by decide
  have hdescent : baseEnd_107829 < baseStart_107829 := by decide
  rcases family_descends (prefixWord ++ tailWord_107829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107839 : List Nat := [1, 1, 2, 2, 4, 4, 1, 3, 2]
def baseStart_107839 : Nat := 118140960795 + 107839 * 2 ^ 59
def prefixEnd_107839 : Nat := 4983230072969 + 3 ^ 40 * 107839 * 2
def baseEnd_107839 : Nat := 49220658044718944992501

theorem tailTrace_107839 : CollatzResearch.WordTrace tailWord_107839 prefixEnd_107839 49220658044718944992501 := by
  unfold tailWord_107839
  simp only [CollatzResearch.WordTrace]
  refine ⟨3933211456325195280022571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2622140970883463520015047 3933211456325195280022571)
  ·
    refine ⟨5899817184487792920033857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3933211456325195280022571 5899817184487792920033857)
    ·
      refine ⟨4424862888365844690025393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5899817184487792920033857 4424862888365844690025393)
      ·
        refine ⟨3318647166274383517519045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4424862888365844690025393 3318647166274383517519045)
        ·
          refine ⟨622246343676446909534821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3318647166274383517519045 622246343676446909534821)
          ·
            refine ⟨116671189439333795537779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 622246343676446909534821 116671189439333795537779)
            ·
              refine ⟨175006784159000693306669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116671189439333795537779 175006784159000693306669)
              ·
                refine ⟨65627544059625259990001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175006784159000693306669 65627544059625259990001)
                ·
                  refine ⟨49220658044718944992501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65627544059625259990001 49220658044718944992501)
                  ·
                    rfl

theorem cell20_107839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 2].length) (baseStart_107839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107839 prefixEnd_107839 := by exact prefixLift 107839
  have htrace : WordTrace (prefixWord ++ tailWord_107839) baseStart_107839 baseEnd_107839 := by
    simpa [prefixWord, tailWord_107839, baseEnd_107839] using wordTrace_append hprefix tailTrace_107839
  have hstable : (prefixWord ++ tailWord_107839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107839).length < 2 ^ (prefixWord ++ tailWord_107839).sum := by decide
  have hdescent : baseEnd_107839 < baseStart_107839 := by decide
  rcases family_descends (prefixWord ++ tailWord_107839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107857 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 5]
def baseStart_107857 : Nat := 118140960795 + 107857 * 2 ^ 59
def prefixEnd_107857 : Nat := 4983230072969 + 3 ^ 40 * 107857 * 2
def baseEnd_107857 : Nat := 49228873735190882392427

theorem tailTrace_107857 : CollatzResearch.WordTrace tailWord_107857 prefixEnd_107857 49228873735190882392427 := by
  unfold tailWord_107857
  simp only [CollatzResearch.WordTrace]
  refine ⟨3933867970259984354177825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2622578646839989569451883 3933867970259984354177825)
  ·
    refine ⟨2950400977694988265633369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3933867970259984354177825 2950400977694988265633369)
    ·
      refine ⟨2212800733271241199225027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2950400977694988265633369 2212800733271241199225027)
      ·
        refine ⟨3319201099906861798837541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2212800733271241199225027 3319201099906861798837541)
        ·
          refine ⟨622350206232536587282039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3319201099906861798837541 622350206232536587282039)
          ·
            refine ⟨933525309348804880923059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622350206232536587282039 933525309348804880923059)
            ·
              refine ⟨1400287964023207321384589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 933525309348804880923059 1400287964023207321384589)
              ·
                refine ⟨525107986508702745519221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1400287964023207321384589 525107986508702745519221)
                ·
                  refine ⟨49228873735190882392427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 525107986508702745519221 49228873735190882392427)
                  ·
                    rfl

theorem cell20_107857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_107857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107857 prefixEnd_107857 := by exact prefixLift 107857
  have htrace : WordTrace (prefixWord ++ tailWord_107857) baseStart_107857 baseEnd_107857 := by
    simpa [prefixWord, tailWord_107857, baseEnd_107857] using wordTrace_append hprefix tailTrace_107857
  have hstable : (prefixWord ++ tailWord_107857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107857).length < 2 ^ (prefixWord ++ tailWord_107857).sum := by decide
  have hdescent : baseEnd_107857 < baseStart_107857 := by decide
  rcases family_descends (prefixWord ++ tailWord_107857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107862 : List Nat := [5, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_107862 : Nat := 118140960795 + 107862 * 2 ^ 59
def prefixEnd_107862 : Nat := 4983230072969 + 3 ^ 40 * 107862 * 2
def baseEnd_107862 : Nat := 49231155871433087225741

theorem tailTrace_107862 : CollatzResearch.WordTrace tailWord_107862 prefixEnd_107862 49231155871433087225741 := by
  unfold tailWord_107862
  simp only [CollatzResearch.WordTrace]
  refine ⟨245878145952616888006865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2622700223494580138739893 245878145952616888006865)
  ·
    refine ⟨184408609464462666005149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245878145952616888006865 184408609464462666005149)
    ·
      refine ⟨69153228549173499751931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184408609464462666005149 69153228549173499751931)
      ·
        refine ⟨103729842823760249627897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69153228549173499751931 103729842823760249627897)
        ·
          refine ⟨77797382117820187220923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103729842823760249627897 77797382117820187220923)
          ·
            refine ⟨116696073176730280831385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77797382117820187220923 116696073176730280831385)
            ·
              refine ⟨87522054882547710623539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116696073176730280831385 87522054882547710623539)
              ·
                refine ⟨131283082323821565935309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87522054882547710623539 131283082323821565935309)
                ·
                  refine ⟨49231155871433087225741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131283082323821565935309 49231155871433087225741)
                  ·
                    rfl

theorem cell20_107862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_107862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107862 prefixEnd_107862 := by exact prefixLift 107862
  have htrace : WordTrace (prefixWord ++ tailWord_107862) baseStart_107862 baseEnd_107862 := by
    simpa [prefixWord, tailWord_107862, baseEnd_107862] using wordTrace_append hprefix tailTrace_107862
  have hstable : (prefixWord ++ tailWord_107862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107862).length < 2 ^ (prefixWord ++ tailWord_107862).sum := by decide
  have hdescent : baseEnd_107862 < baseStart_107862 := by decide
  rcases family_descends (prefixWord ++ tailWord_107862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107905 : List Nat := [1, 2, 4, 3, 3, 7]
def baseStart_107905 : Nat := 118140960795 + 107905 * 2 ^ 59
def prefixEnd_107905 : Nat := 4983230072969 + 3 ^ 40 * 107905 * 2
def baseEnd_107905 : Nat := 1824103046041335140453

theorem tailTrace_107905 : CollatzResearch.WordTrace tailWord_107905 prefixEnd_107905 1824103046041335140453 := by
  unfold tailWord_107905
  simp only [CollatzResearch.WordTrace]
  refine ⟨3935618674086088551925169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2623745782724059034616779 3935618674086088551925169)
  ·
    refine ⟨2951714005564566413943877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3935618674086088551925169 2951714005564566413943877)
    ·
      refine ⟨553446376043356202614477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2951714005564566413943877 553446376043356202614477)
      ·
        refine ⟨207542391016258575980429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 553446376043356202614477 207542391016258575980429)
        ·
          refine ⟨77828396631096965992661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207542391016258575980429 77828396631096965992661)
          ·
            refine ⟨1824103046041335140453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 77828396631096965992661 1824103046041335140453)
            ·
              rfl

theorem cell20_107905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 7].length) (baseStart_107905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107905 prefixEnd_107905 := by exact prefixLift 107905
  have htrace : WordTrace (prefixWord ++ tailWord_107905) baseStart_107905 baseEnd_107905 := by
    simpa [prefixWord, tailWord_107905, baseEnd_107905] using wordTrace_append hprefix tailTrace_107905
  have hstable : (prefixWord ++ tailWord_107905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107905).length < 2 ^ (prefixWord ++ tailWord_107905).sum := by decide
  have hdescent : baseEnd_107905 < baseStart_107905 := by decide
  rcases family_descends (prefixWord ++ tailWord_107905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107912 : List Nat := [2, 1, 3, 3, 1, 2, 1, 4, 3]
def baseStart_107912 : Nat := 118140960795 + 107912 * 2 ^ 59
def prefixEnd_107912 : Nat := 4983230072969 + 3 ^ 40 * 107912 * 2
def baseEnd_107912 : Nat := 49253977233855135558869

theorem tailTrace_107912 : CollatzResearch.WordTrace tailWord_107912 prefixEnd_107912 49253977233855135558869 := by
  unfold tailWord_107912
  simp only [CollatzResearch.WordTrace]
  refine ⟨1967936992530364373714995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2623915990040485831619993 1967936992530364373714995)
  ·
    refine ⟨2951905488795546560572493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1967936992530364373714995 2951905488795546560572493)
    ·
      refine ⟨1106964558298329960214685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2951905488795546560572493 1106964558298329960214685)
      ·
        refine ⟨415111709361873735080507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1106964558298329960214685 415111709361873735080507)
        ·
          refine ⟨622667564042810602620761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415111709361873735080507 622667564042810602620761)
          ·
            refine ⟨467000673032107951965571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622667564042810602620761 467000673032107951965571)
            ·
              refine ⟨700501009548161927948357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467000673032107951965571 700501009548161927948357)
              ·
                refine ⟨131343939290280361490317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 700501009548161927948357 131343939290280361490317)
                ·
                  refine ⟨49253977233855135558869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131343939290280361490317 49253977233855135558869)
                  ·
                    rfl

theorem cell20_107912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_107912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107912 prefixEnd_107912 := by exact prefixLift 107912
  have htrace : WordTrace (prefixWord ++ tailWord_107912) baseStart_107912 baseEnd_107912 := by
    simpa [prefixWord, tailWord_107912, baseEnd_107912] using wordTrace_append hprefix tailTrace_107912
  have hstable : (prefixWord ++ tailWord_107912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107912).length < 2 ^ (prefixWord ++ tailWord_107912).sum := by decide
  have hdescent : baseEnd_107912 < baseStart_107912 := by decide
  rcases family_descends (prefixWord ++ tailWord_107912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107943 : List Nat := [1, 1, 6, 1, 1, 1, 5, 4]
def baseStart_107943 : Nat := 118140960795 + 107943 * 2 ^ 59
def prefixEnd_107943 : Nat := 4983230072969 + 3 ^ 40 * 107943 * 2
def baseEnd_107943 : Nat := 16422708826185601841803

theorem tailTrace_107943 : CollatzResearch.WordTrace tailWord_107943 prefixEnd_107943 16422708826185601841803 := by
  unfold tailWord_107943
  simp only [CollatzResearch.WordTrace]
  refine ⟨3937004647948421041808483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2624669765298947361205655 3937004647948421041808483)
  ·
    refine ⟨5905506971922631562712725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3937004647948421041808483 5905506971922631562712725)
    ·
      refine ⟨276820639308873354502159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5905506971922631562712725 276820639308873354502159)
      ·
        refine ⟨415230958963310031753239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276820639308873354502159 415230958963310031753239)
        ·
          refine ⟨622846438444965047629859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415230958963310031753239 622846438444965047629859)
          ·
            refine ⟨934269657667447571444789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622846438444965047629859 934269657667447571444789)
            ·
              refine ⟨87587780406323209822949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 934269657667447571444789 87587780406323209822949)
              ·
                refine ⟨16422708826185601841803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87587780406323209822949 16422708826185601841803)
                ·
                  rfl

theorem cell20_107943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 4].length) (baseStart_107943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_107943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_107943 prefixEnd_107943 := by exact prefixLift 107943
  have htrace : WordTrace (prefixWord ++ tailWord_107943) baseStart_107943 baseEnd_107943 := by
    simpa [prefixWord, tailWord_107943, baseEnd_107943] using wordTrace_append hprefix tailTrace_107943
  have hstable : (prefixWord ++ tailWord_107943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107943).length < 2 ^ (prefixWord ++ tailWord_107943).sum := by decide
  have hdescent : baseEnd_107943 < baseStart_107943 := by decide
  rcases family_descends (prefixWord ++ tailWord_107943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108029 : List Nat := [1, 4, 1, 1, 1, 5, 3, 2, 2]
def baseStart_108029 : Nat := 118140960795 + 108029 * 2 ^ 59
def prefixEnd_108029 : Nat := 4983230072969 + 3 ^ 40 * 108029 * 2
def baseEnd_108029 : Nat := 49307379221922728658391

theorem tailTrace_108029 : CollatzResearch.WordTrace tailWord_108029 prefixEnd_108029 49307379221922728658391 := by
  unfold tailWord_108029
  simp only [CollatzResearch.WordTrace]
  refine ⟨3940141325636857729439141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2626760883757905152959427 3940141325636857729439141)
  ·
    refine ⟨738776498556910824269839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3940141325636857729439141 738776498556910824269839)
    ·
      refine ⟨1108164747835366236404759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 738776498556910824269839 1108164747835366236404759)
      ·
        refine ⟨1662247121753049354607139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1108164747835366236404759 1662247121753049354607139)
        ·
          refine ⟨2493370682629574031910709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1662247121753049354607139 2493370682629574031910709)
          ·
            refine ⟨233753501496522565491629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2493370682629574031910709 233753501496522565491629)
            ·
              refine ⟨87657563061195962059361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233753501496522565491629 87657563061195962059361)
              ·
                refine ⟨65743172295896971544521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87657563061195962059361 65743172295896971544521)
                ·
                  refine ⟨49307379221922728658391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65743172295896971544521 49307379221922728658391)
                  ·
                    rfl

theorem cell20_108029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_108029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108029 prefixEnd_108029 := by exact prefixLift 108029
  have htrace : WordTrace (prefixWord ++ tailWord_108029) baseStart_108029 baseEnd_108029 := by
    simpa [prefixWord, tailWord_108029, baseEnd_108029] using wordTrace_append hprefix tailTrace_108029
  have hstable : (prefixWord ++ tailWord_108029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108029).length < 2 ^ (prefixWord ++ tailWord_108029).sum := by decide
  have hdescent : baseEnd_108029 < baseStart_108029 := by decide
  rcases family_descends (prefixWord ++ tailWord_108029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108078 : List Nat := [4, 1, 3, 1, 2, 9]
def baseStart_108078 : Nat := 118140960795 + 108078 * 2 ^ 59
def prefixEnd_108078 : Nat := 4983230072969 + 3 ^ 40 * 108078 * 2
def baseEnd_108078 : Nat := 1827027561373938371291

theorem tailTrace_108078 : CollatzResearch.WordTrace tailWord_108078 prefixEnd_108078 1827027561373938371291 := by
  unfold tailWord_108078
  simp only [CollatzResearch.WordTrace]
  refine ⟨492741062807417387246611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2627952334972892731981925 492741062807417387246611)
  ·
    refine ⟨739111594211126080869917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 492741062807417387246611 739111594211126080869917)
    ·
      refine ⟨277166847829172280326219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 739111594211126080869917 277166847829172280326219)
      ·
        refine ⟨415750271743758420489329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277166847829172280326219 415750271743758420489329)
        ·
          refine ⟨311812703807818815366997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415750271743758420489329 311812703807818815366997)
          ·
            refine ⟨1827027561373938371291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 311812703807818815366997 1827027561373938371291)
            ·
              rfl

theorem cell20_108078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 9].length) (baseStart_108078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108078 prefixEnd_108078 := by exact prefixLift 108078
  have htrace : WordTrace (prefixWord ++ tailWord_108078) baseStart_108078 baseEnd_108078 := by
    simpa [prefixWord, tailWord_108078, baseEnd_108078] using wordTrace_append hprefix tailTrace_108078
  have hstable : (prefixWord ++ tailWord_108078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108078).length < 2 ^ (prefixWord ++ tailWord_108078).sum := by decide
  have hdescent : baseEnd_108078 < baseStart_108078 := by decide
  rcases family_descends (prefixWord ++ tailWord_108078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108088 : List Nat := [2, 1, 2, 1, 4, 3, 1, 4, 2]
def baseStart_108088 : Nat := 118140960795 + 108088 * 2 ^ 59
def prefixEnd_108088 : Nat := 4983230072969 + 3 ^ 40 * 108088 * 2
def baseEnd_108088 : Nat := 49334308429580745691483

theorem tailTrace_108088 : CollatzResearch.WordTrace tailWord_108088 prefixEnd_108088 49334308429580745691483 := by
  unfold tailWord_108088
  simp only [CollatzResearch.WordTrace]
  refine ⟨1971146616211555402918459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2628195488282073870557945 1971146616211555402918459)
  ·
    refine ⟨2956719924317333104377689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1971146616211555402918459 2956719924317333104377689)
    ·
      refine ⟨2217539943237999828283267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2956719924317333104377689 2217539943237999828283267)
      ·
        refine ⟨3326309914856999742424901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2217539943237999828283267 3326309914856999742424901)
        ·
          refine ⟨623683109035687451704669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3326309914856999742424901 623683109035687451704669)
          ·
            refine ⟨233881165888382794389251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 623683109035687451704669 233881165888382794389251)
            ·
              refine ⟨350821748832574191583877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233881165888382794389251 350821748832574191583877)
              ·
                refine ⟨65779077906107660921977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 350821748832574191583877 65779077906107660921977)
                ·
                  refine ⟨49334308429580745691483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65779077906107660921977 49334308429580745691483)
                  ·
                    rfl

theorem cell20_108088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 2].length) (baseStart_108088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108088 prefixEnd_108088 := by exact prefixLift 108088
  have htrace : WordTrace (prefixWord ++ tailWord_108088) baseStart_108088 baseEnd_108088 := by
    simpa [prefixWord, tailWord_108088, baseEnd_108088] using wordTrace_append hprefix tailTrace_108088
  have hstable : (prefixWord ++ tailWord_108088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108088).length < 2 ^ (prefixWord ++ tailWord_108088).sum := by decide
  have hdescent : baseEnd_108088 < baseStart_108088 := by decide
  rcases family_descends (prefixWord ++ tailWord_108088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108157 : List Nat := [1, 4, 1, 1, 4, 2, 3, 1, 3]
def baseStart_108157 : Nat := 118140960795 + 108157 * 2 ^ 59
def prefixEnd_108157 : Nat := 4983230072969 + 3 ^ 40 * 108157 * 2
def baseEnd_108157 : Nat := 49365801909723172391201

theorem tailTrace_108157 : CollatzResearch.WordTrace tailWord_108157 prefixEnd_108157 49365801909723172391201 := by
  unfold tailWord_108157
  simp only [CollatzResearch.WordTrace]
  refine ⟨3944809869173135590098725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2629873246115423726732483 3944809869173135590098725)
  ·
    refine ⟨739651850469962923143511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3944809869173135590098725 739651850469962923143511)
    ·
      refine ⟨1109477775704944384715267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 739651850469962923143511 1109477775704944384715267)
      ·
        refine ⟨1664216663557416577072901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1109477775704944384715267 1664216663557416577072901)
        ·
          refine ⟨312040624417015608201169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1664216663557416577072901 312040624417015608201169)
          ·
            refine ⟨234030468312761706150877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312040624417015608201169 234030468312761706150877)
            ·
              refine ⟨87761425617285639806579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234030468312761706150877 87761425617285639806579)
              ·
                refine ⟨131642138425928459709869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87761425617285639806579 131642138425928459709869)
                ·
                  refine ⟨49365801909723172391201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131642138425928459709869 49365801909723172391201)
                  ·
                    rfl

theorem cell20_108157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_108157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108157 prefixEnd_108157 := by exact prefixLift 108157
  have htrace : WordTrace (prefixWord ++ tailWord_108157) baseStart_108157 baseEnd_108157 := by
    simpa [prefixWord, tailWord_108157, baseEnd_108157] using wordTrace_append hprefix tailTrace_108157
  have hstable : (prefixWord ++ tailWord_108157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108157).length < 2 ^ (prefixWord ++ tailWord_108157).sum := by decide
  have hdescent : baseEnd_108157 < baseStart_108157 := by decide
  rcases family_descends (prefixWord ++ tailWord_108157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108185 : List Nat := [1, 2, 1, 2, 1, 2, 2, 7, 2]
def baseStart_108185 : Nat := 118140960795 + 108185 * 2 ^ 59
def prefixEnd_108185 : Nat := 4983230072969 + 3 ^ 40 * 108185 * 2
def baseEnd_108185 : Nat := 49378581872679519457753

theorem tailTrace_108185 : CollatzResearch.WordTrace tailWord_108185 prefixEnd_108185 49378581872679519457753 := by
  unfold tailWord_108185
  simp only [CollatzResearch.WordTrace]
  refine ⟨3945831113071696372118009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2630554075381130914745339 3945831113071696372118009)
  ·
    refine ⟨2959373334803772279088507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3945831113071696372118009 2959373334803772279088507)
    ·
      refine ⟨4439060002205658418632761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2959373334803772279088507 4439060002205658418632761)
      ·
        refine ⟨3329295001654243813974571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4439060002205658418632761 3329295001654243813974571)
        ·
          refine ⟨4993942502481365720961857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3329295001654243813974571 4993942502481365720961857)
          ·
            refine ⟨3745456876861024290721393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4993942502481365720961857 3745456876861024290721393)
            ·
              refine ⟨2809092657645768218041045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3745456876861024290721393 2809092657645768218041045)
              ·
                refine ⟨65838109163572692610337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2809092657645768218041045 65838109163572692610337)
                ·
                  refine ⟨49378581872679519457753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65838109163572692610337 49378581872679519457753)
                  ·
                    rfl

theorem cell20_108185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 2].length) (baseStart_108185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108185 prefixEnd_108185 := by exact prefixLift 108185
  have htrace : WordTrace (prefixWord ++ tailWord_108185) baseStart_108185 baseEnd_108185 := by
    simpa [prefixWord, tailWord_108185, baseEnd_108185] using wordTrace_append hprefix tailTrace_108185
  have hstable : (prefixWord ++ tailWord_108185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108185).length < 2 ^ (prefixWord ++ tailWord_108185).sum := by decide
  have hdescent : baseEnd_108185 < baseStart_108185 := by decide
  rcases family_descends (prefixWord ++ tailWord_108185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108192 : List Nat := [2, 1, 1, 4, 3, 3, 6]
def baseStart_108192 : Nat := 118140960795 + 108192 * 2 ^ 59
def prefixEnd_108192 : Nat := 4983230072969 + 3 ^ 40 * 108192 * 2
def baseEnd_108192 : Nat := 5486864095935400691599

theorem tailTrace_108192 : CollatzResearch.WordTrace tailWord_108192 prefixEnd_108192 5486864095935400691599 := by
  unfold tailWord_108192
  simp only [CollatzResearch.WordTrace]
  refine ⟨1973043212023168283811415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2630724282697557711748553 1973043212023168283811415)
  ·
    refine ⟨2959564818034752425717123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1973043212023168283811415 2959564818034752425717123)
    ·
      refine ⟨4439347227052128638575685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2959564818034752425717123 4439347227052128638575685)
      ·
        refine ⟨832377605072274119732941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4439347227052128638575685 832377605072274119732941)
        ·
          refine ⟨312141601902102794899853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 832377605072274119732941 312141601902102794899853)
          ·
            refine ⟨117053100713288548087445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312141601902102794899853 117053100713288548087445)
            ·
              refine ⟨5486864095935400691599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117053100713288548087445 5486864095935400691599)
              ·
                rfl

theorem cell20_108192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 6].length) (baseStart_108192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108192 prefixEnd_108192 := by exact prefixLift 108192
  have htrace : WordTrace (prefixWord ++ tailWord_108192) baseStart_108192 baseEnd_108192 := by
    simpa [prefixWord, tailWord_108192, baseEnd_108192] using wordTrace_append hprefix tailTrace_108192
  have hstable : (prefixWord ++ tailWord_108192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108192).length < 2 ^ (prefixWord ++ tailWord_108192).sum := by decide
  have hdescent : baseEnd_108192 < baseStart_108192 := by decide
  rcases family_descends (prefixWord ++ tailWord_108192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108253 : List Nat := [1, 4, 3, 3, 1, 2, 2, 2, 2]
def baseStart_108253 : Nat := 118140960795 + 108253 * 2 ^ 59
def prefixEnd_108253 : Nat := 4983230072969 + 3 ^ 40 * 108253 * 2
def baseEnd_108253 : Nat := 49409618925573505190809

theorem tailTrace_108253 : CollatzResearch.WordTrace tailWord_108253 prefixEnd_108253 49409618925573505190809 := by
  unfold tailWord_108253
  simp only [CollatzResearch.WordTrace]
  refine ⟨3948311276825343985593413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2632207517883562657062275 3948311276825343985593413)
  ·
    refine ⟨740308364404751997298765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3948311276825343985593413 740308364404751997298765)
    ·
      refine ⟨277615636651781998987037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 740308364404751997298765 277615636651781998987037)
      ·
        refine ⟨104105863744418249620139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277615636651781998987037 104105863744418249620139)
        ·
          refine ⟨156158795616627374430209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104105863744418249620139 156158795616627374430209)
          ·
            refine ⟨117119096712470530822657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156158795616627374430209 117119096712470530822657)
            ·
              refine ⟨87839322534352898116993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117119096712470530822657 87839322534352898116993)
              ·
                refine ⟨65879491900764673587745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87839322534352898116993 65879491900764673587745)
                ·
                  refine ⟨49409618925573505190809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65879491900764673587745 49409618925573505190809)
                  ·
                    rfl

theorem cell20_108253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_108253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108253 prefixEnd_108253 := by exact prefixLift 108253
  have htrace : WordTrace (prefixWord ++ tailWord_108253) baseStart_108253 baseEnd_108253 := by
    simpa [prefixWord, tailWord_108253, baseEnd_108253] using wordTrace_append hprefix tailTrace_108253
  have hstable : (prefixWord ++ tailWord_108253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108253).length < 2 ^ (prefixWord ++ tailWord_108253).sum := by decide
  have hdescent : baseEnd_108253 < baseStart_108253 := by decide
  rcases family_descends (prefixWord ++ tailWord_108253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108275 : List Nat := [1, 1, 1, 2, 2, 3, 4, 3, 3]
def baseStart_108275 : Nat := 118140960795 + 108275 * 2 ^ 59
def prefixEnd_108275 : Nat := 4983230072969 + 3 ^ 40 * 108275 * 2
def baseEnd_108275 : Nat := 49419660325039206457385

theorem tailTrace_108275 : CollatzResearch.WordTrace tailWord_108275 prefixEnd_108275 49419660325039206457385 := by
  unfold tailWord_108275
  simp only [CollatzResearch.WordTrace]
  refine ⟨3949113682745641742894279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2632742455163761161929519 3949113682745641742894279)
  ·
    refine ⟨5923670524118462614341419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3949113682745641742894279 5923670524118462614341419)
    ·
      refine ⟨8885505786177693921512129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5923670524118462614341419 8885505786177693921512129)
      ·
        refine ⟨6664129339633270441134097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8885505786177693921512129 6664129339633270441134097)
        ·
          refine ⟨4998097004724952830850573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6664129339633270441134097 4998097004724952830850573)
          ·
            refine ⟨1874286376771857311568965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4998097004724952830850573 1874286376771857311568965)
            ·
              refine ⟨351428695644723245919181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1874286376771857311568965 351428695644723245919181)
              ·
                refine ⟨131785760866771217219693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351428695644723245919181 131785760866771217219693)
                ·
                  refine ⟨49419660325039206457385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131785760866771217219693 49419660325039206457385)
                  ·
                    rfl

theorem cell20_108275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 3].length) (baseStart_108275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108275 prefixEnd_108275 := by exact prefixLift 108275
  have htrace : WordTrace (prefixWord ++ tailWord_108275) baseStart_108275 baseEnd_108275 := by
    simpa [prefixWord, tailWord_108275, baseEnd_108275] using wordTrace_append hprefix tailTrace_108275
  have hstable : (prefixWord ++ tailWord_108275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108275).length < 2 ^ (prefixWord ++ tailWord_108275).sum := by decide
  have hdescent : baseEnd_108275 < baseStart_108275 := by decide
  rcases family_descends (prefixWord ++ tailWord_108275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108289 : List Nat := [1, 2, 4, 1, 1, 1, 2, 8]
def baseStart_108289 : Nat := 118140960795 + 108289 * 2 ^ 59
def prefixEnd_108289 : Nat := 4983230072969 + 3 ^ 40 * 108289 * 2
def baseEnd_108289 : Nat := 16475350102172459996887

theorem tailTrace_108289 : CollatzResearch.WordTrace tailWord_108289 prefixEnd_108289 16475350102172459996887 := by
  unfold tailWord_108289
  simp only [CollatzResearch.WordTrace]
  refine ⟨3949624304694922133903921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2633082869796614755935947 3949624304694922133903921)
  ·
    refine ⟨2962218228521191600427941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3949624304694922133903921 2962218228521191600427941)
    ·
      refine ⟨555415917847723425080239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2962218228521191600427941 555415917847723425080239)
      ·
        refine ⟨833123876771585137620359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555415917847723425080239 833123876771585137620359)
        ·
          refine ⟨1249685815157377706430539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833123876771585137620359 1249685815157377706430539)
          ·
            refine ⟨1874528722736066559645809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1249685815157377706430539 1874528722736066559645809)
            ·
              refine ⟨1405896542052049919734357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1874528722736066559645809 1405896542052049919734357)
              ·
                refine ⟨16475350102172459996887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1405896542052049919734357 16475350102172459996887)
                ·
                  rfl

theorem cell20_108289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 8].length) (baseStart_108289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108289 prefixEnd_108289 := by exact prefixLift 108289
  have htrace : WordTrace (prefixWord ++ tailWord_108289) baseStart_108289 baseEnd_108289 := by
    simpa [prefixWord, tailWord_108289, baseEnd_108289] using wordTrace_append hprefix tailTrace_108289
  have hstable : (prefixWord ++ tailWord_108289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108289).length < 2 ^ (prefixWord ++ tailWord_108289).sum := by decide
  have hdescent : baseEnd_108289 < baseStart_108289 := by decide
  rcases family_descends (prefixWord ++ tailWord_108289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108295 : List Nat := [1, 1, 4, 4, 2, 1, 2, 3, 2]
def baseStart_108295 : Nat := 118140960795 + 108295 * 2 ^ 59
def prefixEnd_108295 : Nat := 4983230072969 + 3 ^ 40 * 108295 * 2
def baseEnd_108295 : Nat := 49428788870008025790637

theorem tailTrace_108295 : CollatzResearch.WordTrace tailWord_108295 prefixEnd_108295 49428788870008025790637 := by
  unfold tailWord_108295
  simp only [CollatzResearch.WordTrace]
  refine ⟨3949843142673185158622339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2633228761782123439081559 3949843142673185158622339)
  ·
    refine ⟨5924764714009777737933509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3949843142673185158622339 5924764714009777737933509)
    ·
      refine ⟨1110893383876833325862533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5924764714009777737933509 1110893383876833325862533)
      ·
        refine ⟨208292509476906248599225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1110893383876833325862533 208292509476906248599225)
        ·
          refine ⟨156219382107679686449419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208292509476906248599225 156219382107679686449419)
          ·
            refine ⟨234329073161519529674129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156219382107679686449419 234329073161519529674129)
            ·
              refine ⟨175746804871139647255597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234329073161519529674129 175746804871139647255597)
              ·
                refine ⟨65905051826677367720849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175746804871139647255597 65905051826677367720849)
                ·
                  refine ⟨49428788870008025790637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65905051826677367720849 49428788870008025790637)
                  ·
                    rfl

theorem cell20_108295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 2].length) (baseStart_108295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108295 prefixEnd_108295 := by exact prefixLift 108295
  have htrace : WordTrace (prefixWord ++ tailWord_108295) baseStart_108295 baseEnd_108295 := by
    simpa [prefixWord, tailWord_108295, baseEnd_108295] using wordTrace_append hprefix tailTrace_108295
  have hstable : (prefixWord ++ tailWord_108295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108295).length < 2 ^ (prefixWord ++ tailWord_108295).sum := by decide
  have hdescent : baseEnd_108295 < baseStart_108295 := by decide
  rcases family_descends (prefixWord ++ tailWord_108295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108299 : List Nat := [1, 1, 1, 1, 5, 1, 3, 5, 2]
def baseStart_108299 : Nat := 118140960795 + 108299 * 2 ^ 59
def prefixEnd_108299 : Nat := 4983230072969 + 3 ^ 40 * 108299 * 2
def baseEnd_108299 : Nat := 49430614579001789657287

theorem tailTrace_108299 : CollatzResearch.WordTrace tailWord_108299 prefixEnd_108299 49430614579001789657287 := by
  unfold tailWord_108299
  simp only [CollatzResearch.WordTrace]
  refine ⟨3949989034658693841767951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2633326023105795894511967 3949989034658693841767951)
  ·
    refine ⟨5924983551988040762651927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3949989034658693841767951 5924983551988040762651927)
    ·
      refine ⟨8887475327982061143977891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5924983551988040762651927 8887475327982061143977891)
      ·
        refine ⟨13331212991973091715966837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8887475327982061143977891 13331212991973091715966837)
        ·
          refine ⟨1249801217997477348371891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13331212991973091715966837 1249801217997477348371891)
          ·
            refine ⟨1874701826996216022557837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1249801217997477348371891 1874701826996216022557837)
            ·
              refine ⟨703013185123581008459189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1874701826996216022557837 703013185123581008459189)
              ·
                refine ⟨65907486105335719543049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 703013185123581008459189 65907486105335719543049)
                ·
                  refine ⟨49430614579001789657287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65907486105335719543049 49430614579001789657287)
                  ·
                    rfl

theorem cell20_108299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 2].length) (baseStart_108299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108299 prefixEnd_108299 := by exact prefixLift 108299
  have htrace : WordTrace (prefixWord ++ tailWord_108299) baseStart_108299 baseEnd_108299 := by
    simpa [prefixWord, tailWord_108299, baseEnd_108299] using wordTrace_append hprefix tailTrace_108299
  have hstable : (prefixWord ++ tailWord_108299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108299).length < 2 ^ (prefixWord ++ tailWord_108299).sum := by decide
  have hdescent : baseEnd_108299 < baseStart_108299 := by decide
  rcases family_descends (prefixWord ++ tailWord_108299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108301 : List Nat := [1, 7, 2, 1, 2, 1, 1, 2, 3]
def baseStart_108301 : Nat := 118140960795 + 108301 * 2 ^ 59
def prefixEnd_108301 : Nat := 4983230072969 + 3 ^ 40 * 108301 * 2
def baseEnd_108301 : Nat := 49431527433498671590613

theorem tailTrace_108301 : CollatzResearch.WordTrace tailWord_108301 prefixEnd_108301 49431527433498671590613 := by
  unfold tailWord_108301
  simp only [CollatzResearch.WordTrace]
  refine ⟨3950061980651448183340757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2633374653767632122227171 3950061980651448183340757)
  ·
    refine ⟨92579577671518316797049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 3950061980651448183340757 92579577671518316797049)
    ·
      refine ⟨69434683253638737597787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92579577671518316797049 69434683253638737597787)
      ·
        refine ⟨104152024880458106396681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69434683253638737597787 104152024880458106396681)
        ·
          refine ⟨78114018660343579797511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104152024880458106396681 78114018660343579797511)
          ·
            refine ⟨117171027990515369696267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78114018660343579797511 117171027990515369696267)
            ·
              refine ⟨175756541985773054544401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117171027990515369696267 175756541985773054544401)
              ·
                refine ⟨131817406489329790908301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175756541985773054544401 131817406489329790908301)
                ·
                  refine ⟨49431527433498671590613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131817406489329790908301 49431527433498671590613)
                  ·
                    rfl

theorem cell20_108301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_108301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108301 prefixEnd_108301 := by exact prefixLift 108301
  have htrace : WordTrace (prefixWord ++ tailWord_108301) baseStart_108301 baseEnd_108301 := by
    simpa [prefixWord, tailWord_108301, baseEnd_108301] using wordTrace_append hprefix tailTrace_108301
  have hstable : (prefixWord ++ tailWord_108301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108301).length < 2 ^ (prefixWord ++ tailWord_108301).sum := by decide
  have hdescent : baseEnd_108301 < baseStart_108301 := by decide
  rcases family_descends (prefixWord ++ tailWord_108301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108340 : List Nat := [2, 5, 1, 1, 2, 3, 2, 4]
def baseStart_108340 : Nat := 118140960795 + 108340 * 2 ^ 59
def prefixEnd_108340 : Nat := 4983230072969 + 3 ^ 40 * 108340 * 2
def baseEnd_108340 : Nat := 16483109365395956430151

theorem tailTrace_108340 : CollatzResearch.WordTrace tailWord_108340 prefixEnd_108340 16483109365395956430151 := by
  unfold tailWord_108340
  simp only [CollatzResearch.WordTrace]
  refine ⟨1975742213755078922005237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2634322951673438562673649 1975742213755078922005237)
  ·
    refine ⟨185225832539538648937991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1975742213755078922005237 185225832539538648937991)
    ·
      refine ⟨277838748809307973406987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185225832539538648937991 277838748809307973406987)
      ·
        refine ⟨416758123213961960110481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277838748809307973406987 416758123213961960110481)
        ·
          refine ⟨312568592410471470082861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416758123213961960110481 312568592410471470082861)
          ·
            refine ⟨117213222153926801281073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312568592410471470082861 117213222153926801281073)
            ·
              refine ⟨87909916615445100960805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117213222153926801281073 87909916615445100960805)
              ·
                refine ⟨16483109365395956430151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87909916615445100960805 16483109365395956430151)
                ·
                  rfl

theorem cell20_108340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_108340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108340 prefixEnd_108340 := by exact prefixLift 108340
  have htrace : WordTrace (prefixWord ++ tailWord_108340) baseStart_108340 baseEnd_108340 := by
    simpa [prefixWord, tailWord_108340, baseEnd_108340] using wordTrace_append hprefix tailTrace_108340
  have hstable : (prefixWord ++ tailWord_108340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108340).length < 2 ^ (prefixWord ++ tailWord_108340).sum := by decide
  have hdescent : baseEnd_108340 < baseStart_108340 := by decide
  rcases family_descends (prefixWord ++ tailWord_108340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108344 : List Nat := [2, 1, 2, 1, 3, 3, 4, 4]
def baseStart_108344 : Nat := 118140960795 + 108344 * 2 ^ 59
def prefixEnd_108344 : Nat := 4983230072969 + 3 ^ 40 * 108344 * 2
def baseEnd_108344 : Nat := 16483717935060544385701

theorem tailTrace_108344 : CollatzResearch.WordTrace tailWord_108344 prefixEnd_108344 16483717935060544385701 := by
  unfold tailWord_108344
  simp only [CollatzResearch.WordTrace]
  refine ⟨1975815159747833263578043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2634420212997111018104057 1975815159747833263578043)
  ·
    refine ⟨2963722739621749895367065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1975815159747833263578043 2963722739621749895367065)
    ·
      refine ⟨2222792054716312421525299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2963722739621749895367065 2222792054716312421525299)
      ·
        refine ⟨3334188082074468632287949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2222792054716312421525299 3334188082074468632287949)
        ·
          refine ⟨1250320530777925737107981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3334188082074468632287949 1250320530777925737107981)
          ·
            refine ⟨468870199041722151415493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1250320530777925737107981 468870199041722151415493)
            ·
              refine ⟨87913162320322903390405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 468870199041722151415493 87913162320322903390405)
              ·
                refine ⟨16483717935060544385701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87913162320322903390405 16483717935060544385701)
                ·
                  rfl

theorem cell20_108344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_108344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108344 prefixEnd_108344 := by exact prefixLift 108344
  have htrace : WordTrace (prefixWord ++ tailWord_108344) baseStart_108344 baseEnd_108344 := by
    simpa [prefixWord, tailWord_108344, baseEnd_108344] using wordTrace_append hprefix tailTrace_108344
  have hstable : (prefixWord ++ tailWord_108344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108344).length < 2 ^ (prefixWord ++ tailWord_108344).sum := by decide
  have hdescent : baseEnd_108344 < baseStart_108344 := by decide
  rcases family_descends (prefixWord ++ tailWord_108344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108410 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_108410 : Nat := 118140960795 + 108410 * 2 ^ 59
def prefixEnd_108410 : Nat := 4983230072969 + 3 ^ 40 * 108410 * 2
def baseEnd_108410 : Nat := 49481278003578736956833

theorem tailTrace_108410 : CollatzResearch.WordTrace tailWord_108410 prefixEnd_108410 49481278003578736956833 := by
  unfold tailWord_108410
  simp only [CollatzResearch.WordTrace]
  refine ⟨988509384314139949764671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2636025024837706532705789 988509384314139949764671)
  ·
    refine ⟨1482764076471209924647007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 988509384314139949764671 1482764076471209924647007)
    ·
      refine ⟨2224146114706814886970511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1482764076471209924647007 2224146114706814886970511)
      ·
        refine ⟨3336219172060222330455767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2224146114706814886970511 3336219172060222330455767)
        ·
          refine ⟨5004328758090333495683651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3336219172060222330455767 5004328758090333495683651)
          ·
            refine ⟨7506493137135500243525477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004328758090333495683651 7506493137135500243525477)
            ·
              refine ⟨1407467463212906295661027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7506493137135500243525477 1407467463212906295661027)
              ·
                refine ⟨2111201194819359443491541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1407467463212906295661027 2111201194819359443491541)
                ·
                  refine ⟨49481278003578736956833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2111201194819359443491541 49481278003578736956833)
                  ·
                    rfl

theorem cell20_108410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_108410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108410 prefixEnd_108410 := by exact prefixLift 108410
  have htrace : WordTrace (prefixWord ++ tailWord_108410) baseStart_108410 baseEnd_108410 := by
    simpa [prefixWord, tailWord_108410, baseEnd_108410] using wordTrace_append hprefix tailTrace_108410
  have hstable : (prefixWord ++ tailWord_108410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108410).length < 2 ^ (prefixWord ++ tailWord_108410).sum := by decide
  have hdescent : baseEnd_108410 < baseStart_108410 := by decide
  rcases family_descends (prefixWord ++ tailWord_108410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108413 : List Nat := [1, 4, 1, 1, 2, 1, 1, 7, 2]
def baseStart_108413 : Nat := 118140960795 + 108413 * 2 ^ 59
def prefixEnd_108413 : Nat := 4983230072969 + 3 ^ 40 * 108413 * 2
def baseEnd_108413 : Nat := 49482647285324059856821

theorem tailTrace_108413 : CollatzResearch.WordTrace tailWord_108413 prefixEnd_108413 49482647285324059856821 := by
  unfold tailWord_108413
  simp only [CollatzResearch.WordTrace]
  refine ⟨3954146956245691311417893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2636097970830460874278595 3954146956245691311417893)
  ·
    refine ⟨741402554296067120890855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3954146956245691311417893 741402554296067120890855)
    ·
      refine ⟨1112103831444100681336283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 741402554296067120890855 1112103831444100681336283)
      ·
        refine ⟨1668155747166151022004425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1112103831444100681336283 1668155747166151022004425)
        ·
          refine ⟨1251116810374613266503319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1668155747166151022004425 1251116810374613266503319)
          ·
            refine ⟨1876675215561919899754979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251116810374613266503319 1876675215561919899754979)
            ·
              refine ⟨2815012823342879849632469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876675215561919899754979 2815012823342879849632469)
              ·
                refine ⟨65976863047098746475761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2815012823342879849632469 65976863047098746475761)
                ·
                  refine ⟨49482647285324059856821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65976863047098746475761 49482647285324059856821)
                  ·
                    rfl

theorem cell20_108413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_108413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108413 prefixEnd_108413 := by exact prefixLift 108413
  have htrace : WordTrace (prefixWord ++ tailWord_108413) baseStart_108413 baseEnd_108413 := by
    simpa [prefixWord, tailWord_108413, baseEnd_108413] using wordTrace_append hprefix tailTrace_108413
  have hstable : (prefixWord ++ tailWord_108413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108413).length < 2 ^ (prefixWord ++ tailWord_108413).sum := by decide
  have hdescent : baseEnd_108413 < baseStart_108413 := by decide
  rcases family_descends (prefixWord ++ tailWord_108413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108426 : List Nat := [3, 1, 2, 4, 2, 2, 2, 2, 2]
def baseStart_108426 : Nat := 118140960795 + 108426 * 2 ^ 59
def prefixEnd_108426 : Nat := 4983230072969 + 3 ^ 40 * 108426 * 2
def baseEnd_108426 : Nat := 49488580839553792423435

theorem tailTrace_108426 : CollatzResearch.WordTrace tailWord_108426 prefixEnd_108426 49488580839553792423435 := by
  unfold tailWord_108426
  simp only [CollatzResearch.WordTrace]
  refine ⟨988655276299648632910283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2636414070132396354427421 988655276299648632910283)
  ·
    refine ⟨1482982914449472949365425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 988655276299648632910283 1482982914449472949365425)
    ·
      refine ⟨1112237185837104712024069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1482982914449472949365425 1112237185837104712024069)
      ·
        refine ⟨208544472344457133504513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1112237185837104712024069 208544472344457133504513)
        ·
          refine ⟨156408354258342850128385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208544472344457133504513 156408354258342850128385)
          ·
            refine ⟨117306265693757137596289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156408354258342850128385 117306265693757137596289)
            ·
              refine ⟨87979699270317853197217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117306265693757137596289 87979699270317853197217)
              ·
                refine ⟨65984774452738389897913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87979699270317853197217 65984774452738389897913)
                ·
                  refine ⟨49488580839553792423435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65984774452738389897913 49488580839553792423435)
                  ·
                    rfl

theorem cell20_108426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_108426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108426 prefixEnd_108426 := by exact prefixLift 108426
  have htrace : WordTrace (prefixWord ++ tailWord_108426) baseStart_108426 baseEnd_108426 := by
    simpa [prefixWord, tailWord_108426, baseEnd_108426] using wordTrace_append hprefix tailTrace_108426
  have hstable : (prefixWord ++ tailWord_108426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108426).length < 2 ^ (prefixWord ++ tailWord_108426).sum := by decide
  have hdescent : baseEnd_108426 < baseStart_108426 := by decide
  rcases family_descends (prefixWord ++ tailWord_108426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108441 : List Nat := [1, 2, 1, 2, 1, 3, 5, 5]
def baseStart_108441 : Nat := 118140960795 + 108441 * 2 ^ 59
def prefixEnd_108441 : Nat := 4983230072969 + 3 ^ 40 * 108441 * 2
def baseEnd_108441 : Nat := 16498475749426802307791

theorem tailTrace_108441 : CollatzResearch.WordTrace tailWord_108441 prefixEnd_108441 16498475749426802307791 := by
  unfold tailWord_108441
  simp only [CollatzResearch.WordTrace]
  refine ⟨3955168200144252093437177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2636778800096168062291451 3955168200144252093437177)
  ·
    refine ⟨2966376150108189070077883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3955168200144252093437177 2966376150108189070077883)
    ·
      refine ⟨4449564225162283605116825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2966376150108189070077883 4449564225162283605116825)
      ·
        refine ⟨3337173168871712703837619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4449564225162283605116825 3337173168871712703837619)
        ·
          refine ⟨5005759753307569055756429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3337173168871712703837619 5005759753307569055756429)
          ·
            refine ⟨1877159907490338395908661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5005759753307569055756429 1877159907490338395908661)
            ·
              refine ⟨175983741327219224616437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1877159907490338395908661 175983741327219224616437)
              ·
                refine ⟨16498475749426802307791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175983741327219224616437 16498475749426802307791)
                ·
                  rfl

theorem cell20_108441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 5].length) (baseStart_108441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108441 prefixEnd_108441 := by exact prefixLift 108441
  have htrace : WordTrace (prefixWord ++ tailWord_108441) baseStart_108441 baseEnd_108441 := by
    simpa [prefixWord, tailWord_108441, baseEnd_108441] using wordTrace_append hprefix tailTrace_108441
  have hstable : (prefixWord ++ tailWord_108441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108441).length < 2 ^ (prefixWord ++ tailWord_108441).sum := by decide
  have hdescent : baseEnd_108441 < baseStart_108441 := by decide
  rcases family_descends (prefixWord ++ tailWord_108441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108444 : List Nat := [2, 2, 3, 3, 1, 1, 2, 3, 3]
def baseStart_108444 : Nat := 118140960795 + 108444 * 2 ^ 59
def prefixEnd_108444 : Nat := 4983230072969 + 3 ^ 40 * 108444 * 2
def baseEnd_108444 : Nat := 49496796530025729823361

theorem tailTrace_108444 : CollatzResearch.WordTrace tailWord_108444 prefixEnd_108444 49496796530025729823361 := by
  unfold tailWord_108444
  simp only [CollatzResearch.WordTrace]
  refine ⟨1977638809566691802898193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2636851746088922403864257 1977638809566691802898193)
  ·
    refine ⟨1483229107175018852173645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1977638809566691802898193 1483229107175018852173645)
    ·
      refine ⟨556210915190632069565117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1483229107175018852173645 556210915190632069565117)
      ·
        refine ⟨208579093196487026086919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 556210915190632069565117 208579093196487026086919)
        ·
          refine ⟨312868639794730539130379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208579093196487026086919 312868639794730539130379)
          ·
            refine ⟨469302959692095808695569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312868639794730539130379 469302959692095808695569)
            ·
              refine ⟨351977219769071856521677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469302959692095808695569 351977219769071856521677)
              ·
                refine ⟨131991457413401946195629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351977219769071856521677 131991457413401946195629)
                ·
                  refine ⟨49496796530025729823361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131991457413401946195629 49496796530025729823361)
                  ·
                    rfl

theorem cell20_108444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_108444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108444 prefixEnd_108444 := by exact prefixLift 108444
  have htrace : WordTrace (prefixWord ++ tailWord_108444) baseStart_108444 baseEnd_108444 := by
    simpa [prefixWord, tailWord_108444, baseEnd_108444] using wordTrace_append hprefix tailTrace_108444
  have hstable : (prefixWord ++ tailWord_108444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108444).length < 2 ^ (prefixWord ++ tailWord_108444).sum := by decide
  have hdescent : baseEnd_108444 < baseStart_108444 := by decide
  rcases family_descends (prefixWord ++ tailWord_108444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108448 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 7]
def baseStart_108448 : Nat := 118140960795 + 108448 * 2 ^ 59
def prefixEnd_108448 : Nat := 4983230072969 + 3 ^ 40 * 108448 * 2
def baseEnd_108448 : Nat := 49498622239019493690011

theorem tailTrace_108448 : CollatzResearch.WordTrace tailWord_108448 prefixEnd_108448 49498622239019493690011 := by
  unfold tailWord_108448
  simp only [CollatzResearch.WordTrace]
  refine ⟨1977711755559446144470999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2636949007412594859294665 1977711755559446144470999)
  ·
    refine ⟨2966567633339169216706499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1977711755559446144470999 2966567633339169216706499)
    ·
      refine ⟨4449851450008753825059749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2966567633339169216706499 4449851450008753825059749)
      ·
        refine ⟨834347146876641342198703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4449851450008753825059749 834347146876641342198703)
        ·
          refine ⟨1251520720314962013298055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834347146876641342198703 1251520720314962013298055)
          ·
            refine ⟨1877281080472443019947083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251520720314962013298055 1877281080472443019947083)
            ·
              refine ⟨2815921620708664529920625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1877281080472443019947083 2815921620708664529920625)
              ·
                refine ⟨2111941215531498397440469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2815921620708664529920625 2111941215531498397440469)
                ·
                  refine ⟨49498622239019493690011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2111941215531498397440469 49498622239019493690011)
                  ·
                    rfl

theorem cell20_108448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_108448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108448 prefixEnd_108448 := by exact prefixLift 108448
  have htrace : WordTrace (prefixWord ++ tailWord_108448) baseStart_108448 baseEnd_108448 := by
    simpa [prefixWord, tailWord_108448, baseEnd_108448] using wordTrace_append hprefix tailTrace_108448
  have hstable : (prefixWord ++ tailWord_108448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108448).length < 2 ^ (prefixWord ++ tailWord_108448).sum := by decide
  have hdescent : baseEnd_108448 < baseStart_108448 := by decide
  rcases family_descends (prefixWord ++ tailWord_108448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108531 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 6]
def baseStart_108531 : Nat := 118140960795 + 108531 * 2 ^ 59
def prefixEnd_108531 : Nat := 4983230072969 + 3 ^ 40 * 108531 * 2
def baseEnd_108531 : Nat := 49536505700640093923005

theorem tailTrace_108531 : CollatzResearch.WordTrace tailWord_108531 prefixEnd_108531 49536505700640093923005 := by
  unfold tailWord_108531
  simp only [CollatzResearch.WordTrace]
  refine ⟨3958450769818197464213447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2638967179878798309475631 3958450769818197464213447)
  ·
    refine ⟨5937676154727296196320171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3958450769818197464213447 5937676154727296196320171)
    ·
      refine ⟨8906514232090944294480257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5937676154727296196320171 8906514232090944294480257)
      ·
        refine ⟨6679885674068208220860193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8906514232090944294480257 6679885674068208220860193)
        ·
          refine ⟨5009914255551156165645145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6679885674068208220860193 5009914255551156165645145)
          ·
            refine ⟨3757435691663367124233859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5009914255551156165645145 3757435691663367124233859)
            ·
              refine ⟨5636153537495050686350789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3757435691663367124233859 5636153537495050686350789)
              ·
                refine ⟨1056778788280322003690773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5636153537495050686350789 1056778788280322003690773)
                ·
                  refine ⟨49536505700640093923005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1056778788280322003690773 49536505700640093923005)
                  ·
                    rfl

theorem cell20_108531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_108531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108531 prefixEnd_108531 := by exact prefixLift 108531
  have htrace : WordTrace (prefixWord ++ tailWord_108531) baseStart_108531 baseEnd_108531 := by
    simpa [prefixWord, tailWord_108531, baseEnd_108531] using wordTrace_append hprefix tailTrace_108531
  have hstable : (prefixWord ++ tailWord_108531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108531).length < 2 ^ (prefixWord ++ tailWord_108531).sum := by decide
  have hdescent : baseEnd_108531 < baseStart_108531 := by decide
  rcases family_descends (prefixWord ++ tailWord_108531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108554 : List Nat := [3, 1, 2, 2, 5, 1, 2, 1, 3]
def baseStart_108554 : Nat := 118140960795 + 108554 * 2 ^ 59
def prefixEnd_108554 : Nat := 4983230072969 + 3 ^ 40 * 108554 * 2
def baseEnd_108554 : Nat := 49547003527354236156245

theorem tailTrace_108554 : CollatzResearch.WordTrace tailWord_108554 prefixEnd_108554 49547003527354236156245 := by
  unfold tailWord_108554
  simp only [CollatzResearch.WordTrace]
  refine ⟨989822412183718098075179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2639526432489914928200477 989822412183718098075179)
  ·
    refine ⟨1484733618275577147112769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 989822412183718098075179 1484733618275577147112769)
    ·
      refine ⟨1113550213706682860334577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1484733618275577147112769 1113550213706682860334577)
      ·
        refine ⟨835162660280012145250933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1113550213706682860334577 835162660280012145250933)
        ·
          refine ⟨78296499401251138617275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 835162660280012145250933 78296499401251138617275)
          ·
            refine ⟨117444749101876707925913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78296499401251138617275 117444749101876707925913)
            ·
              refine ⟨88083561826407530944435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117444749101876707925913 88083561826407530944435)
              ·
                refine ⟨132125342739611296416653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88083561826407530944435 132125342739611296416653)
                ·
                  refine ⟨49547003527354236156245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132125342739611296416653 49547003527354236156245)
                  ·
                    rfl

theorem cell20_108554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_108554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108554 prefixEnd_108554 := by exact prefixLift 108554
  have htrace : WordTrace (prefixWord ++ tailWord_108554) baseStart_108554 baseEnd_108554 := by
    simpa [prefixWord, tailWord_108554, baseEnd_108554] using wordTrace_append hprefix tailTrace_108554
  have hstable : (prefixWord ++ tailWord_108554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108554).length < 2 ^ (prefixWord ++ tailWord_108554).sum := by decide
  have hdescent : baseEnd_108554 < baseStart_108554 := by decide
  rcases family_descends (prefixWord ++ tailWord_108554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108555 : List Nat := [1, 1, 1, 1, 6, 1, 4, 5]
def baseStart_108555 : Nat := 118140960795 + 108555 * 2 ^ 59
def prefixEnd_108555 : Nat := 4983230072969 + 3 ^ 40 * 108555 * 2
def baseEnd_108555 : Nat := 16515819984867559040969

theorem tailTrace_108555 : CollatzResearch.WordTrace tailWord_108555 prefixEnd_108555 16515819984867559040969 := by
  unfold tailWord_108555
  simp only [CollatzResearch.WordTrace]
  refine ⟨3959326121731249563087119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2639550747820833042058079 3959326121731249563087119)
  ·
    refine ⟨5938989182596874344630679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3959326121731249563087119 5938989182596874344630679)
    ·
      refine ⟨8908483773895311516946019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5938989182596874344630679 8908483773895311516946019)
      ·
        refine ⟨13362725660842967275419029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8908483773895311516946019 13362725660842967275419029)
        ·
          refine ⟨626377765352014091035267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13362725660842967275419029 626377765352014091035267)
          ·
            refine ⟨939566648028021136552901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626377765352014091035267 939566648028021136552901)
            ·
              refine ⟨176168746505253963103669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 939566648028021136552901 176168746505253963103669)
              ·
                refine ⟨16515819984867559040969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176168746505253963103669 16515819984867559040969)
                ·
                  rfl

theorem cell20_108555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 5].length) (baseStart_108555 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108555 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108555 prefixEnd_108555 := by exact prefixLift 108555
  have htrace : WordTrace (prefixWord ++ tailWord_108555) baseStart_108555 baseEnd_108555 := by
    simpa [prefixWord, tailWord_108555, baseEnd_108555] using wordTrace_append hprefix tailTrace_108555
  have hstable : (prefixWord ++ tailWord_108555).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108555).length < 2 ^ (prefixWord ++ tailWord_108555).sum := by decide
  have hdescent : baseEnd_108555 < baseStart_108555 := by decide
  rcases family_descends (prefixWord ++ tailWord_108555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108569 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 6]
def baseStart_108569 : Nat := 118140960795 + 108569 * 2 ^ 59
def prefixEnd_108569 : Nat := 4983230072969 + 3 ^ 40 * 108569 * 2
def baseEnd_108569 : Nat := 49553849936080850656183

theorem tailTrace_108569 : CollatzResearch.WordTrace tailWord_108569 prefixEnd_108569 49553849936080850656183 := by
  unfold tailWord_108569
  simp only [CollatzResearch.WordTrace]
  refine ⟨3959836743680529954096761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2639891162453686636064507 3959836743680529954096761)
  ·
    refine ⟨2969877557760397465572571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3959836743680529954096761 2969877557760397465572571)
    ·
      refine ⟨4454816336640596198358857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2969877557760397465572571 4454816336640596198358857)
      ·
        refine ⟨3341112252480447148769143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4454816336640596198358857 3341112252480447148769143)
        ·
          refine ⟨5011668378720670723153715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3341112252480447148769143 5011668378720670723153715)
          ·
            refine ⟨7517502568081006084730573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5011668378720670723153715 7517502568081006084730573)
            ·
              refine ⟨2819063463030377281773965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7517502568081006084730573 2819063463030377281773965)
              ·
                refine ⟨1057148798636391480665237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2819063463030377281773965 1057148798636391480665237)
                ·
                  refine ⟨49553849936080850656183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1057148798636391480665237 49553849936080850656183)
                  ·
                    rfl

theorem cell20_108569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_108569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108569 prefixEnd_108569 := by exact prefixLift 108569
  have htrace : WordTrace (prefixWord ++ tailWord_108569) baseStart_108569 baseEnd_108569 := by
    simpa [prefixWord, tailWord_108569, baseEnd_108569] using wordTrace_append hprefix tailTrace_108569
  have hstable : (prefixWord ++ tailWord_108569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108569).length < 2 ^ (prefixWord ++ tailWord_108569).sum := by decide
  have hdescent : baseEnd_108569 < baseStart_108569 := by decide
  rcases family_descends (prefixWord ++ tailWord_108569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108606 : List Nat := [4, 2, 1, 3, 3, 1, 1, 5]
def baseStart_108606 : Nat := 118140960795 + 108606 * 2 ^ 59
def prefixEnd_108606 : Nat := 4983230072969 + 3 ^ 40 * 108606 * 2
def baseEnd_108606 : Nat := 16523579248091055474233

theorem tailTrace_108606 : CollatzResearch.WordTrace tailWord_108606 prefixEnd_108606 16523579248091055474233 := by
  unfold tailWord_108606
  simp only [CollatzResearch.WordTrace]
  refine ⟨495148280568310659149209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2640790829697656848795781 495148280568310659149209)
  ·
    refine ⟨371361210426232994361907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 495148280568310659149209 371361210426232994361907)
    ·
      refine ⟨557041815639349491542861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371361210426232994361907 557041815639349491542861)
      ·
        refine ⟨208890680864756059328573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 557041815639349491542861 208890680864756059328573)
        ·
          refine ⟨78334005324283522248215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208890680864756059328573 78334005324283522248215)
          ·
            refine ⟨117501007986425283372323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78334005324283522248215 117501007986425283372323)
            ·
              refine ⟨176251511979637925058485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117501007986425283372323 176251511979637925058485)
              ·
                refine ⟨16523579248091055474233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176251511979637925058485 16523579248091055474233)
                ·
                  rfl

theorem cell20_108606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_108606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108606 prefixEnd_108606 := by exact prefixLift 108606
  have htrace : WordTrace (prefixWord ++ tailWord_108606) baseStart_108606 baseEnd_108606 := by
    simpa [prefixWord, tailWord_108606, baseEnd_108606] using wordTrace_append hprefix tailTrace_108606
  have hstable : (prefixWord ++ tailWord_108606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108606).length < 2 ^ (prefixWord ++ tailWord_108606).sum := by decide
  have hdescent : baseEnd_108606 < baseStart_108606 := by decide
  rcases family_descends (prefixWord ++ tailWord_108606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108637 : List Nat := [1, 4, 4, 1, 1, 2, 2, 3, 2]
def baseStart_108637 : Nat := 118140960795 + 108637 * 2 ^ 59
def prefixEnd_108637 : Nat := 4983230072969 + 3 ^ 40 * 108637 * 2
def baseEnd_108637 : Nat := 49584886988974836389239

theorem tailTrace_108637 : CollatzResearch.WordTrace tailWord_108637 prefixEnd_108637 49584886988974836389239 := by
  unfold tailWord_108637
  simp only [CollatzResearch.WordTrace]
  refine ⟨3962316907434177567572165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2641544604956118378381443 3962316907434177567572165)
  ·
    refine ⟨742934420143908293919781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3962316907434177567572165 742934420143908293919781)
    ·
      refine ⟨139300203776982805109959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 742934420143908293919781 139300203776982805109959)
      ·
        refine ⟨208950305665474207664939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139300203776982805109959 208950305665474207664939)
        ·
          refine ⟨313425458498211311497409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208950305665474207664939 313425458498211311497409)
          ·
            refine ⟨235069093873658483623057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313425458498211311497409 235069093873658483623057)
            ·
              refine ⟨176301820405243862717293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235069093873658483623057 176301820405243862717293)
              ·
                refine ⟨66113182651966448518985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176301820405243862717293 66113182651966448518985)
                ·
                  refine ⟨49584886988974836389239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66113182651966448518985 49584886988974836389239)
                  ·
                    rfl

theorem cell20_108637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_108637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108637 prefixEnd_108637 := by exact prefixLift 108637
  have htrace : WordTrace (prefixWord ++ tailWord_108637) baseStart_108637 baseEnd_108637 := by
    simpa [prefixWord, tailWord_108637, baseEnd_108637] using wordTrace_append hprefix tailTrace_108637
  have hstable : (prefixWord ++ tailWord_108637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108637).length < 2 ^ (prefixWord ++ tailWord_108637).sum := by decide
  have hdescent : baseEnd_108637 < baseStart_108637 := by decide
  rcases family_descends (prefixWord ++ tailWord_108637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108655 : List Nat := [1, 1, 2, 1, 3, 4, 3, 2, 3]
def baseStart_108655 : Nat := 118140960795 + 108655 * 2 ^ 59
def prefixEnd_108655 : Nat := 4983230072969 + 3 ^ 40 * 108655 * 2
def baseEnd_108655 : Nat := 49593102679446773789165

theorem tailTrace_108655 : CollatzResearch.WordTrace tailWord_108655 prefixEnd_108655 49593102679446773789165 := by
  unfold tailWord_108655
  simp only [CollatzResearch.WordTrace]
  refine ⟨3962973421368966641727419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2641982280912644427818279 3962973421368966641727419)
  ·
    refine ⟨5944460132053449962591129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3962973421368966641727419 5944460132053449962591129)
    ·
      refine ⟨4458345099040087471943347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5944460132053449962591129 4458345099040087471943347)
      ·
        refine ⟨6687517648560131207915021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4458345099040087471943347 6687517648560131207915021)
        ·
          refine ⟨2507819118210049202968133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6687517648560131207915021 2507819118210049202968133)
          ·
            refine ⟨470216084664384225556525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2507819118210049202968133 470216084664384225556525)
            ·
              refine ⟨176331031749144084583697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 470216084664384225556525 176331031749144084583697)
              ·
                refine ⟨132248273811858063437773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176331031749144084583697 132248273811858063437773)
                ·
                  refine ⟨49593102679446773789165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132248273811858063437773 49593102679446773789165)
                  ·
                    rfl

theorem cell20_108655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 3].length) (baseStart_108655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108655 prefixEnd_108655 := by exact prefixLift 108655
  have htrace : WordTrace (prefixWord ++ tailWord_108655) baseStart_108655 baseEnd_108655 := by
    simpa [prefixWord, tailWord_108655, baseEnd_108655] using wordTrace_append hprefix tailTrace_108655
  have hstable : (prefixWord ++ tailWord_108655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108655).length < 2 ^ (prefixWord ++ tailWord_108655).sum := by decide
  have hdescent : baseEnd_108655 < baseStart_108655 := by decide
  rcases family_descends (prefixWord ++ tailWord_108655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108686 : List Nat := [4, 1, 1, 3, 3, 1, 1, 6]
def baseStart_108686 : Nat := 118140960795 + 108686 * 2 ^ 59
def prefixEnd_108686 : Nat := 4983230072969 + 3 ^ 40 * 108686 * 2
def baseEnd_108686 : Nat := 16535750641382814585235

theorem tailTrace_108686 : CollatzResearch.WordTrace tailWord_108686 prefixEnd_108686 16535750641382814585235 := by
  unfold tailWord_108686
  simp only [CollatzResearch.WordTrace]
  refine ⟨495513010532082367013239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2642736056171105957403941 495513010532082367013239)
  ·
    refine ⟨743269515798123550519859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 495513010532082367013239 743269515798123550519859)
    ·
      refine ⟨1114904273697185325779789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 743269515798123550519859 1114904273697185325779789)
      ·
        refine ⟨418089102636444497167421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1114904273697185325779789 418089102636444497167421)
        ·
          refine ⟨156783413488666686437783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418089102636444497167421 156783413488666686437783)
          ·
            refine ⟨235175120233000029656675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156783413488666686437783 235175120233000029656675)
            ·
              refine ⟨352762680349500044485013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235175120233000029656675 352762680349500044485013)
              ·
                refine ⟨16535750641382814585235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 352762680349500044485013 16535750641382814585235)
                ·
                  rfl

theorem cell20_108686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_108686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108686 prefixEnd_108686 := by exact prefixLift 108686
  have htrace : WordTrace (prefixWord ++ tailWord_108686) baseStart_108686 baseEnd_108686 := by
    simpa [prefixWord, tailWord_108686, baseEnd_108686] using wordTrace_append hprefix tailTrace_108686
  have hstable : (prefixWord ++ tailWord_108686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108686).length < 2 ^ (prefixWord ++ tailWord_108686).sum := by decide
  have hdescent : baseEnd_108686 < baseStart_108686 := by decide
  rcases family_descends (prefixWord ++ tailWord_108686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108692 : List Nat := [2, 4, 2, 3, 1, 2, 1, 3, 2]
def baseStart_108692 : Nat := 118140960795 + 108692 * 2 ^ 59
def prefixEnd_108692 : Nat := 4983230072969 + 3 ^ 40 * 108692 * 2
def baseEnd_108692 : Nat := 49609990487639089555681

theorem tailTrace_108692 : CollatzResearch.WordTrace tailWord_108692 prefixEnd_108692 49609990487639089555681 := by
  unfold tailWord_108692
  simp only [CollatzResearch.WordTrace]
  refine ⟨1982161461117460980412165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2642881948156614640549553 1982161461117460980412165)
  ·
    refine ⟨371655273959523933827281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1982161461117460980412165 371655273959523933827281)
    ·
      refine ⟨278741455469642950370461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371655273959523933827281 278741455469642950370461)
      ·
        refine ⟨104528045801116106388923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278741455469642950370461 104528045801116106388923)
        ·
          refine ⟨156792068701674159583385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104528045801116106388923 156792068701674159583385)
          ·
            refine ⟨117594051526255619687539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156792068701674159583385 117594051526255619687539)
            ·
              refine ⟨176391077289383429531309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117594051526255619687539 176391077289383429531309)
              ·
                refine ⟨66146653983518786074241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176391077289383429531309 66146653983518786074241)
                ·
                  refine ⟨49609990487639089555681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66146653983518786074241 49609990487639089555681)
                  ·
                    rfl

theorem cell20_108692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_108692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108692 prefixEnd_108692 := by exact prefixLift 108692
  have htrace : WordTrace (prefixWord ++ tailWord_108692) baseStart_108692 baseEnd_108692 := by
    simpa [prefixWord, tailWord_108692, baseEnd_108692] using wordTrace_append hprefix tailTrace_108692
  have hstable : (prefixWord ++ tailWord_108692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108692).length < 2 ^ (prefixWord ++ tailWord_108692).sum := by decide
  have hdescent : baseEnd_108692 < baseStart_108692 := by decide
  rcases family_descends (prefixWord ++ tailWord_108692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108717 : List Nat := [1, 5, 2, 1, 2, 1, 3, 1, 4]
def baseStart_108717 : Nat := 118140960795 + 108717 * 2 ^ 59
def prefixEnd_108717 : Nat := 4983230072969 + 3 ^ 40 * 108717 * 2
def baseEnd_108717 : Nat := 49621401168850113722245

theorem tailTrace_108717 : CollatzResearch.WordTrace tailWord_108717 prefixEnd_108717 49621401168850113722245 := by
  unfold tailWord_108717
  simp only [CollatzResearch.WordTrace]
  refine ⟨3965234747144351230484405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2643489831429567486989603 3965234747144351230484405)
  ·
    refine ⟨371740757544782927857913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3965234747144351230484405 371740757544782927857913)
    ·
      refine ⟨278805568158587195893435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371740757544782927857913 278805568158587195893435)
      ·
        refine ⟨418208352237880793840153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278805568158587195893435 418208352237880793840153)
        ·
          refine ⟨313656264178410595380115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418208352237880793840153 313656264178410595380115)
          ·
            refine ⟨470484396267615893070173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313656264178410595380115 470484396267615893070173)
            ·
              refine ⟨176431648600355959901315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 470484396267615893070173 176431648600355959901315)
              ·
                refine ⟨264647472900533939851973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176431648600355959901315 264647472900533939851973)
                ·
                  refine ⟨49621401168850113722245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264647472900533939851973 49621401168850113722245)
                  ·
                    rfl

theorem cell20_108717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_108717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108717 prefixEnd_108717 := by exact prefixLift 108717
  have htrace : WordTrace (prefixWord ++ tailWord_108717) baseStart_108717 baseEnd_108717 := by
    simpa [prefixWord, tailWord_108717, baseEnd_108717] using wordTrace_append hprefix tailTrace_108717
  have hstable : (prefixWord ++ tailWord_108717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108717).length < 2 ^ (prefixWord ++ tailWord_108717).sum := by decide
  have hdescent : baseEnd_108717 < baseStart_108717 := by decide
  rcases family_descends (prefixWord ++ tailWord_108717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108766 : List Nat := [4, 16]
def baseStart_108766 : Nat := 118140960795 + 108766 * 2 ^ 59
def prefixEnd_108766 : Nat := 4983230072969 + 3 ^ 40 * 108766 * 2
def baseEnd_108766 : Nat := 22699481529046054453

theorem tailTrace_108766 : CollatzResearch.WordTrace tailWord_108766 prefixEnd_108766 22699481529046054453 := by
  unfold tailWord_108766
  simp only [CollatzResearch.WordTrace]
  refine ⟨495877740495854074877269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2644681282644555066012101 495877740495854074877269)
  ·
    refine ⟨22699481529046054453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 16 495877740495854074877269 22699481529046054453)
    ·
      rfl

theorem cell20_108766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 16].length) (baseStart_108766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108766 prefixEnd_108766 := by exact prefixLift 108766
  have htrace : WordTrace (prefixWord ++ tailWord_108766) baseStart_108766 baseEnd_108766 := by
    simpa [prefixWord, tailWord_108766, baseEnd_108766] using wordTrace_append hprefix tailTrace_108766
  have hstable : (prefixWord ++ tailWord_108766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108766).length < 2 ^ (prefixWord ++ tailWord_108766).sum := by decide
  have hdescent : baseEnd_108766 < baseStart_108766 := by decide
  rcases family_descends (prefixWord ++ tailWord_108766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108769 : List Nat := [1, 2, 3, 1, 3, 1, 4, 2, 3]
def baseStart_108769 : Nat := 118140960795 + 108769 * 2 ^ 59
def prefixEnd_108769 : Nat := 4983230072969 + 3 ^ 40 * 108769 * 2
def baseEnd_108769 : Nat := 49645135385769043988699

theorem tailTrace_108769 : CollatzResearch.WordTrace tailWord_108769 prefixEnd_108769 49645135385769043988699 := by
  unfold tailWord_108769
  simp only [CollatzResearch.WordTrace]
  refine ⟨3967131342955964111377361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2644754228637309407584907 3967131342955964111377361)
  ·
    refine ⟨2975348507216973083533021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3967131342955964111377361 2975348507216973083533021)
    ·
      refine ⟨1115755690206364906324883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2975348507216973083533021 1115755690206364906324883)
      ·
        refine ⟨1673633535309547359487325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1115755690206364906324883 1673633535309547359487325)
        ·
          refine ⟨627612575741080259807747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1673633535309547359487325 627612575741080259807747)
          ·
            refine ⟨941418863611620389711621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627612575741080259807747 941418863611620389711621)
            ·
              refine ⟨176516036927178823070929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 941418863611620389711621 176516036927178823070929)
              ·
                refine ⟨132387027695384117303197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176516036927178823070929 132387027695384117303197)
                ·
                  refine ⟨49645135385769043988699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132387027695384117303197 49645135385769043988699)
                  ·
                    rfl

theorem cell20_108769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_108769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_108769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_108769 prefixEnd_108769 := by exact prefixLift 108769
  have htrace : WordTrace (prefixWord ++ tailWord_108769) baseStart_108769 baseEnd_108769 := by
    simpa [prefixWord, tailWord_108769, baseEnd_108769] using wordTrace_append hprefix tailTrace_108769
  have hstable : (prefixWord ++ tailWord_108769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108769).length < 2 ^ (prefixWord ++ tailWord_108769).sum := by decide
  have hdescent : baseEnd_108769 < baseStart_108769 := by decide
  rcases family_descends (prefixWord ++ tailWord_108769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
