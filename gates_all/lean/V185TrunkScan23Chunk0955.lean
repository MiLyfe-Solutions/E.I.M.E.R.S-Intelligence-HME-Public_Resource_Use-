import V185TrunkScan23Chunk0954

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5654785 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_5654785 : Nat := 118140960795 + 5654785 * 2 ^ 59
def prefixEnd_5654785 : Nat := 4983230072969 + 3 ^ 40 * 5654785 * 2
def baseEnd_5654785 : Nat := 2903622702834763361381623

theorem tailTrace_5654785 : CollatzResearch.WordTrace tailWord_5654785 prefixEnd_5654785 2903622702834763361381623 := by
  unfold tailWord_5654785
  simp only [CollatzResearch.WordTrace]
  refine ⟨206246952818687180234997809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137497968545791453489998539 206246952818687180234997809)
  ·
    refine ⟨154685214614015385176248357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206246952818687180234997809 154685214614015385176248357)
    ·
      refine ⟨29003477740127884720546567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154685214614015385176248357 29003477740127884720546567)
      ·
        refine ⟨43505216610191827080819851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29003477740127884720546567 43505216610191827080819851)
        ·
          refine ⟨65257824915287740621229777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43505216610191827080819851 65257824915287740621229777)
          ·
            refine ⟨48943368686465805465922333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65257824915287740621229777 48943368686465805465922333)
            ·
              refine ⟨18353763257424677049720875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48943368686465805465922333 18353763257424677049720875)
              ·
                refine ⟨27530644886137015574581313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18353763257424677049720875 27530644886137015574581313)
                ·
                  refine ⟨20647983664602761680935985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27530644886137015574581313 20647983664602761680935985)
                  ·
                    refine ⟨15485987748452071260701989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20647983664602761680935985 15485987748452071260701989)
                    ·
                      refine ⟨2903622702834763361381623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15485987748452071260701989 2903622702834763361381623)
                      ·
                        rfl

theorem cell23_5654785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_5654785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654785 prefixEnd_5654785 := by exact prefixLift 5654785
  have htrace : WordTrace (prefixWord ++ tailWord_5654785) baseStart_5654785 baseEnd_5654785 := by
    simpa [prefixWord, tailWord_5654785, baseEnd_5654785] using wordTrace_append hprefix tailTrace_5654785
  have hstable : (prefixWord ++ tailWord_5654785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654785).length < 2 ^ (prefixWord ++ tailWord_5654785).sum := by decide
  have hdescent : baseEnd_5654785 < baseStart_5654785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654829 : List Nat := [1, 5, 3, 1, 2, 1, 2, 1, 7]
def baseStart_5654829 : Nat := 118140960795 + 5654829 * 2 ^ 59
def prefixEnd_5654829 : Nat := 4983230072969 + 3 ^ 40 * 5654829 * 2
def baseEnd_5654829 : Nat := 322627255109284576581269

theorem tailTrace_5654829 : CollatzResearch.WordTrace tailWord_5654829 prefixEnd_5654829 322627255109284576581269 := by
  unfold tailWord_5654829
  simp only [CollatzResearch.WordTrace]
  refine ⟨206248557630527775749599541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137499038420351850499733027 206248557630527775749599541)
  ·
    refine ⟨19335802277861978976524957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206248557630527775749599541 19335802277861978976524957)
    ·
      refine ⟨7250925854198242116196859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19335802277861978976524957 7250925854198242116196859)
      ·
        refine ⟨10876388781297363174295289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7250925854198242116196859 10876388781297363174295289)
        ·
          refine ⟨8157291585973022380721467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10876388781297363174295289 8157291585973022380721467)
          ·
            refine ⟨12235937378959533571082201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8157291585973022380721467 12235937378959533571082201)
            ·
              refine ⟨9176953034219650178311651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12235937378959533571082201 9176953034219650178311651)
              ·
                refine ⟨13765429551329475267467477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9176953034219650178311651 13765429551329475267467477)
                ·
                  refine ⟨322627255109284576581269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13765429551329475267467477 322627255109284576581269)
                  ·
                    rfl

theorem cell23_5654829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_5654829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654829 prefixEnd_5654829 := by exact prefixLift 5654829
  have htrace : WordTrace (prefixWord ++ tailWord_5654829) baseStart_5654829 baseEnd_5654829 := by
    simpa [prefixWord, tailWord_5654829, baseEnd_5654829] using wordTrace_append hprefix tailTrace_5654829
  have hstable : (prefixWord ++ tailWord_5654829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654829).length < 2 ^ (prefixWord ++ tailWord_5654829).sum := by decide
  have hdescent : baseEnd_5654829 < baseStart_5654829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654862 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2]
def baseStart_5654862 : Nat := 118140960795 + 5654862 * 2 ^ 59
def prefixEnd_5654862 : Nat := 4983230072969 + 3 ^ 40 * 5654862 * 2
def baseEnd_5654862 : Nat := 2903662240845159560118769

theorem tailTrace_5654862 : CollatzResearch.WordTrace tailWord_5654862 prefixEnd_5654862 2903662240845159560118769 := by
  unfold tailWord_5654862
  simp only [CollatzResearch.WordTrace]
  refine ⟨25781220154926027798193855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137499840826272148257033893 25781220154926027798193855)
  ·
    refine ⟨38671830232389041697290783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25781220154926027798193855 38671830232389041697290783)
    ·
      refine ⟨58007745348583562545936175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38671830232389041697290783 58007745348583562545936175)
      ·
        refine ⟨87011618022875343818904263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58007745348583562545936175 87011618022875343818904263)
        ·
          refine ⟨130517427034313015728356395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87011618022875343818904263 130517427034313015728356395)
          ·
            refine ⟨195776140551469523592534593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130517427034313015728356395 195776140551469523592534593)
            ·
              refine ⟨146832105413602142694400945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195776140551469523592534593 146832105413602142694400945)
              ·
                refine ⟨110124079060201607020800709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146832105413602142694400945 110124079060201607020800709)
                ·
                  refine ⟨20648264823787801316400133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110124079060201607020800709 20648264823787801316400133)
                  ·
                    refine ⟨3871549654460212746825025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20648264823787801316400133 3871549654460212746825025)
                    ·
                      refine ⟨2903662240845159560118769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3871549654460212746825025 2903662240845159560118769)
                      ·
                        rfl

theorem cell23_5654862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_5654862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654862 prefixEnd_5654862 := by exact prefixLift 5654862
  have htrace : WordTrace (prefixWord ++ tailWord_5654862) baseStart_5654862 baseEnd_5654862 := by
    simpa [prefixWord, tailWord_5654862, baseEnd_5654862] using wordTrace_append hprefix tailTrace_5654862
  have hstable : (prefixWord ++ tailWord_5654862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654862).length < 2 ^ (prefixWord ++ tailWord_5654862).sum := by decide
  have hdescent : baseEnd_5654862 < baseStart_5654862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654885 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 8]
def baseStart_5654885 : Nat := 118140960795 + 5654885 * 2 ^ 59
def prefixEnd_5654885 : Nat := 4983230072969 + 3 ^ 40 * 5654885 * 2
def baseEnd_5654885 : Nat := 322630450100023663347907

theorem tailTrace_5654885 : CollatzResearch.WordTrace tailWord_5654885 prefixEnd_5654885 322630450100023663347907 := by
  unfold tailWord_5654885
  simp only [CollatzResearch.WordTrace]
  refine ⟨206250600118324897313638109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137500400078883264875758739 206250600118324897313638109)
  ·
    refine ⟨77343975044371836492614291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206250600118324897313638109 77343975044371836492614291)
    ·
      refine ⟨116015962566557754738921437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77343975044371836492614291 116015962566557754738921437)
      ·
        refine ⟨43505985962459158027095539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116015962566557754738921437 43505985962459158027095539)
        ·
          refine ⟨65258978943688737040643309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43505985962459158027095539 65258978943688737040643309)
          ·
            refine ⟨24472117103883276390241241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65258978943688737040643309 24472117103883276390241241)
            ·
              refine ⟨18354087827912457292680931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24472117103883276390241241 18354087827912457292680931)
              ·
                refine ⟨27531131741868685939021397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18354087827912457292680931 27531131741868685939021397)
                ·
                  refine ⟨322630450100023663347907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27531131741868685939021397 322630450100023663347907)
                  ·
                    rfl

theorem cell23_5654885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 8].length) (baseStart_5654885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654885 prefixEnd_5654885 := by exact prefixLift 5654885
  have htrace : WordTrace (prefixWord ++ tailWord_5654885) baseStart_5654885 baseEnd_5654885 := by
    simpa [prefixWord, tailWord_5654885, baseEnd_5654885] using wordTrace_append hprefix tailTrace_5654885
  have hstable : (prefixWord ++ tailWord_5654885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654885).length < 2 ^ (prefixWord ++ tailWord_5654885).sum := by decide
  have hdescent : baseEnd_5654885 < baseStart_5654885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654895 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 3]
def baseStart_5654895 : Nat := 118140960795 + 5654895 * 2 ^ 59
def prefixEnd_5654895 : Nat := 4983230072969 + 3 ^ 40 * 5654895 * 2
def baseEnd_5654895 : Nat := 2903679185706757931006117

theorem tailTrace_5654895 : CollatzResearch.WordTrace tailWord_5654895 prefixEnd_5654895 2903679185706757931006117 := by
  unfold tailWord_5654895
  simp only [CollatzResearch.WordTrace]
  refine ⟨206250964848288669021502139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137500643232192446014334759 206250964848288669021502139)
  ·
    refine ⟨309376447272433003532253209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206250964848288669021502139 309376447272433003532253209)
    ·
      refine ⟨232032335454324752649189907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309376447272433003532253209 232032335454324752649189907)
      ·
        refine ⟨348048503181487128973784861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232032335454324752649189907 348048503181487128973784861)
        ·
          refine ⟨130518188693057673365169323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348048503181487128973784861 130518188693057673365169323)
          ·
            refine ⟨195777283039586510047753985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130518188693057673365169323 195777283039586510047753985)
            ·
              refine ⟨146832962279689882535815489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195777283039586510047753985 146832962279689882535815489)
              ·
                refine ⟨110124721709767411901861617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146832962279689882535815489 110124721709767411901861617)
                ·
                  refine ⟨82593541282325558926396213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110124721709767411901861617 82593541282325558926396213)
                  ·
                    refine ⟨7743144495218021149349645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82593541282325558926396213 7743144495218021149349645)
                    ·
                      refine ⟨2903679185706757931006117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7743144495218021149349645 2903679185706757931006117)
                      ·
                        rfl

theorem cell23_5654895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 3].length) (baseStart_5654895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654895 prefixEnd_5654895 := by exact prefixLift 5654895
  have htrace : WordTrace (prefixWord ++ tailWord_5654895) baseStart_5654895 baseEnd_5654895 := by
    simpa [prefixWord, tailWord_5654895, baseEnd_5654895] using wordTrace_append hprefix tailTrace_5654895
  have hstable : (prefixWord ++ tailWord_5654895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654895).length < 2 ^ (prefixWord ++ tailWord_5654895).sum := by decide
  have hdescent : baseEnd_5654895 < baseStart_5654895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654962 : List Nat := [3, 2, 1, 1, 1, 1, 6, 1, 1, 6]
def baseStart_5654962 : Nat := 118140960795 + 5654962 * 2 ^ 59
def prefixEnd_5654962 : Nat := 4983230072969 + 3 ^ 40 * 5654962 * 2
def baseEnd_5654962 : Nat := 967904529636869722956103

theorem tailTrace_5654962 : CollatzResearch.WordTrace tailWord_5654962 prefixEnd_5654962 967904529636869722956103 := by
  unfold tailWord_5654962
  simp only [CollatzResearch.WordTrace]
  refine ⟨51563352134761484866047785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137502272359363959642794093 51563352134761484866047785)
  ·
    refine ⟨38672514101071113649535839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51563352134761484866047785 38672514101071113649535839)
    ·
      refine ⟨58008771151606670474303759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38672514101071113649535839 58008771151606670474303759)
      ·
        refine ⟨87013156727410005711455639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58008771151606670474303759 87013156727410005711455639)
        ·
          refine ⟨130519735091115008567183459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87013156727410005711455639 130519735091115008567183459)
          ·
            refine ⟨195779602636672512850775189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130519735091115008567183459 195779602636672512850775189)
            ·
              refine ⟨9177168873594024039880087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 195779602636672512850775189 9177168873594024039880087)
              ·
                refine ⟨13765753310391036059820131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9177168873594024039880087 13765753310391036059820131)
                ·
                  refine ⟨20648629965586554089730197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13765753310391036059820131 20648629965586554089730197)
                  ·
                    refine ⟨967904529636869722956103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20648629965586554089730197 967904529636869722956103)
                    ·
                      rfl

theorem cell23_5654962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_5654962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654962 prefixEnd_5654962 := by exact prefixLift 5654962
  have htrace : WordTrace (prefixWord ++ tailWord_5654962) baseStart_5654962 baseEnd_5654962 := by
    simpa [prefixWord, tailWord_5654962, baseEnd_5654962] using wordTrace_append hprefix tailTrace_5654962
  have hstable : (prefixWord ++ tailWord_5654962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654962).length < 2 ^ (prefixWord ++ tailWord_5654962).sum := by decide
  have hdescent : baseEnd_5654962 < baseStart_5654962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654980 : List Nat := [2, 3, 3, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_5654980 : Nat := 118140960795 + 5654980 * 2 ^ 59
def prefixEnd_5654980 : Nat := 4983230072969 + 3 ^ 40 * 5654980 * 2
def baseEnd_5654980 : Nat := 2903722831562390098443227

theorem tailTrace_5654980 : CollatzResearch.WordTrace tailWord_5654980 prefixEnd_5654980 2903722831562390098443227 := by
  unfold tailWord_5654980
  simp only [CollatzResearch.WordTrace]
  refine ⟨103127032526490364269173197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137502710035320485692230929 103127032526490364269173197)
  ·
    refine ⟨38672637197433886600939949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103127032526490364269173197 38672637197433886600939949)
    ·
      refine ⟨14502238949037707475352481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38672637197433886600939949 14502238949037707475352481)
      ·
        refine ⟨10876679211778280606514361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14502238949037707475352481 10876679211778280606514361)
        ·
          refine ⟨8157509408833710454885771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10876679211778280606514361 8157509408833710454885771)
          ·
            refine ⟨12236264113250565682328657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8157509408833710454885771 12236264113250565682328657)
            ·
              refine ⟨9177198084937924261746493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12236264113250565682328657 9177198084937924261746493)
              ·
                refine ⟨3441449281851721598154935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9177198084937924261746493 3441449281851721598154935)
                ·
                  refine ⟨5162173922777582397232403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3441449281851721598154935 5162173922777582397232403)
                  ·
                    refine ⟨7743260884166373595848605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5162173922777582397232403 7743260884166373595848605)
                    ·
                      refine ⟨2903722831562390098443227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7743260884166373595848605 2903722831562390098443227)
                      ·
                        rfl

theorem cell23_5654980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_5654980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654980 prefixEnd_5654980 := by exact prefixLift 5654980
  have htrace : WordTrace (prefixWord ++ tailWord_5654980) baseStart_5654980 baseEnd_5654980 := by
    simpa [prefixWord, tailWord_5654980, baseEnd_5654980] using wordTrace_append hprefix tailTrace_5654980
  have hstable : (prefixWord ++ tailWord_5654980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654980).length < 2 ^ (prefixWord ++ tailWord_5654980).sum := by decide
  have hdescent : baseEnd_5654980 < baseStart_5654980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654996 : List Nat := [2, 4, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_5654996 : Nat := 118140960795 + 5654996 * 2 ^ 59
def prefixEnd_5654996 : Nat := 4983230072969 + 3 ^ 40 * 5654996 * 2
def baseEnd_5654996 : Nat := 967910349084287345281051

theorem tailTrace_5654996 : CollatzResearch.WordTrace tailWord_5654996 prefixEnd_5654996 967910349084287345281051 := by
  unfold tailWord_5654996
  simp only [CollatzResearch.WordTrace]
  refine ⟨103127324310461381635464421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137503099080615175513952561 103127324310461381635464421)
  ·
    refine ⟨19336373308211509056649579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103127324310461381635464421 19336373308211509056649579)
    ·
      refine ⟨29004559962317263584974369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19336373308211509056649579 29004559962317263584974369)
      ·
        refine ⟨21753419971737947688730777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29004559962317263584974369 21753419971737947688730777)
        ·
          refine ⟨16315064978803460766548083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21753419971737947688730777 16315064978803460766548083)
          ·
            refine ⟨24472597468205191149822125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16315064978803460766548083 24472597468205191149822125)
            ·
              refine ⟨9177224050576946681183297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24472597468205191149822125 9177224050576946681183297)
              ·
                refine ⟨6882918037932710010887473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9177224050576946681183297 6882918037932710010887473)
                ·
                  refine ⟨5162188528449532508165605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6882918037932710010887473 5162188528449532508165605)
                  ·
                    refine ⟨967910349084287345281051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5162188528449532508165605 967910349084287345281051)
                    ·
                      rfl

theorem cell23_5654996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_5654996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654996 prefixEnd_5654996 := by exact prefixLift 5654996
  have htrace : WordTrace (prefixWord ++ tailWord_5654996) baseStart_5654996 baseEnd_5654996 := by
    simpa [prefixWord, tailWord_5654996, baseEnd_5654996] using wordTrace_append hprefix tailTrace_5654996
  have hstable : (prefixWord ++ tailWord_5654996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654996).length < 2 ^ (prefixWord ++ tailWord_5654996).sum := by decide
  have hdescent : baseEnd_5654996 < baseStart_5654996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655013 : List Nat := [1, 3, 1, 5, 2, 1, 3, 1, 2, 4]
def baseStart_5655013 : Nat := 118140960795 + 5655013 * 2 ^ 59
def prefixEnd_5655013 : Nat := 4983230072969 + 3 ^ 40 * 5655013 * 2
def baseEnd_5655013 : Nat := 967913258807996156443525

theorem tailTrace_5655013 : CollatzResearch.WordTrace tailWord_5655013 prefixEnd_5655013 967913258807996156443525 := by
  unfold tailWord_5655013
  simp only [CollatzResearch.WordTrace]
  refine ⟨206255268661861175174297693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137503512441240783449531795 206255268661861175174297693)
  ·
    refine ⟨77345725748197940690361635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206255268661861175174297693 77345725748197940690361635)
    ·
      refine ⟨116018588622296911035542453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77345725748197940690361635 116018588622296911035542453)
      ·
        refine ⟨10876742683340335409582105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116018588622296911035542453 10876742683340335409582105)
        ·
          refine ⟨8157557012505251557186579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10876742683340335409582105 8157557012505251557186579)
          ·
            refine ⟨12236335518757877335779869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8157557012505251557186579 12236335518757877335779869)
            ·
              refine ⟨4588625819534204000917451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12236335518757877335779869 4588625819534204000917451)
              ·
                refine ⟨6882938729301306001376177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4588625819534204000917451 6882938729301306001376177)
                ·
                  refine ⟨5162204046975979501032133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6882938729301306001376177 5162204046975979501032133)
                  ·
                    refine ⟨967913258807996156443525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5162204046975979501032133 967913258807996156443525)
                    ·
                      rfl

theorem cell23_5655013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 2, 4].length) (baseStart_5655013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655013 prefixEnd_5655013 := by exact prefixLift 5655013
  have htrace : WordTrace (prefixWord ++ tailWord_5655013) baseStart_5655013 baseEnd_5655013 := by
    simpa [prefixWord, tailWord_5655013, baseEnd_5655013] using wordTrace_append hprefix tailTrace_5655013
  have hstable : (prefixWord ++ tailWord_5655013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655013).length < 2 ^ (prefixWord ++ tailWord_5655013).sum := by decide
  have hdescent : baseEnd_5655013 < baseStart_5655013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655026 : List Nat := [3, 2, 1, 4, 2, 2, 2, 7]
def baseStart_5655026 : Nat := 118140960795 + 5655026 * 2 ^ 59
def prefixEnd_5655026 : Nat := 4983230072969 + 3 ^ 40 * 5655026 * 2
def baseEnd_5655026 : Nat := 107546164876759145128445

theorem tailTrace_5655026 : CollatzResearch.WordTrace tailWord_5655026 prefixEnd_5655026 107546164876759145128445 := by
  unfold tailWord_5655026
  simp only [CollatzResearch.WordTrace]
  refine ⟨51563935702703519598630233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137503828540542718929680621 51563935702703519598630233)
  ·
    refine ⟨38672951777027639698972675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51563935702703519598630233 38672951777027639698972675)
    ·
      refine ⟨58009427665541459548459013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38672951777027639698972675 58009427665541459548459013)
      ·
        refine ⟨10876767687289023665336065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58009427665541459548459013 10876767687289023665336065)
        ·
          refine ⟨8157575765466767749002049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10876767687289023665336065 8157575765466767749002049)
          ·
            refine ⟨6118181824100075811751537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8157575765466767749002049 6118181824100075811751537)
            ·
              refine ⟨4588636368075056858813653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6118181824100075811751537 4588636368075056858813653)
              ·
                refine ⟨107546164876759145128445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4588636368075056858813653 107546164876759145128445)
                ·
                  rfl

theorem cell23_5655026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 7].length) (baseStart_5655026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655026 prefixEnd_5655026 := by exact prefixLift 5655026
  have htrace : WordTrace (prefixWord ++ tailWord_5655026) baseStart_5655026 baseEnd_5655026 := by
    simpa [prefixWord, tailWord_5655026, baseEnd_5655026] using wordTrace_append hprefix tailTrace_5655026
  have hstable : (prefixWord ++ tailWord_5655026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655026).length < 2 ^ (prefixWord ++ tailWord_5655026).sum := by decide
  have hdescent : baseEnd_5655026 < baseStart_5655026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655080 : List Nat := [2, 1, 5, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_5655080 : Nat := 118140960795 + 5655080 * 2 ^ 59
def prefixEnd_5655080 : Nat := 4983230072969 + 3 ^ 40 * 5655080 * 2
def baseEnd_5655080 : Nat := 2903774179627839707192767

theorem tailTrace_5655080 : CollatzResearch.WordTrace tailWord_5655080 prefixEnd_5655080 2903774179627839707192767 := by
  unfold tailWord_5655080
  simp only [CollatzResearch.WordTrace]
  refine ⟨103128856176309222808493347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137505141568412297077991129 103128856176309222808493347)
  ·
    refine ⟨154693284264463834212740021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103128856176309222808493347 154693284264463834212740021)
    ·
      refine ⟨14502495399793484457444377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154693284264463834212740021 14502495399793484457444377)
      ·
        refine ⟨10876871549845113343083283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14502495399793484457444377 10876871549845113343083283)
        ·
          refine ⟨16315307324767670014624925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10876871549845113343083283 16315307324767670014624925)
          ·
            refine ⟨6118240246787876255484347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16315307324767670014624925 6118240246787876255484347)
            ·
              refine ⟨9177360370181814383226521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6118240246787876255484347 9177360370181814383226521)
              ·
                refine ⟨6883020277636360787419891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9177360370181814383226521 6883020277636360787419891)
                ·
                  refine ⟨10324530416454541181129837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6883020277636360787419891 10324530416454541181129837)
                  ·
                    refine ⟨3871698906170452942923689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10324530416454541181129837 3871698906170452942923689)
                    ·
                      refine ⟨2903774179627839707192767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3871698906170452942923689 2903774179627839707192767)
                      ·
                        rfl

theorem cell23_5655080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_5655080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655080 prefixEnd_5655080 := by exact prefixLift 5655080
  have htrace : WordTrace (prefixWord ++ tailWord_5655080) baseStart_5655080 baseEnd_5655080 := by
    simpa [prefixWord, tailWord_5655080, baseEnd_5655080] using wordTrace_append hprefix tailTrace_5655080
  have hstable : (prefixWord ++ tailWord_5655080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655080).length < 2 ^ (prefixWord ++ tailWord_5655080).sum := by decide
  have hdescent : baseEnd_5655080 < baseStart_5655080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655119 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 2, 5, 2]
def baseStart_5655119 : Nat := 118140960795 + 5655119 * 2 ^ 59
def prefixEnd_5655119 : Nat := 4983230072969 + 3 ^ 40 * 5655119 * 2
def baseEnd_5655119 : Nat := 2903794205373365054605087

theorem tailTrace_5655119 : CollatzResearch.WordTrace tailWord_5655119 prefixEnd_5655119 2903794205373365054605087 := by
  unfold tailWord_5655119
  simp only [CollatzResearch.WordTrace]
  refine ⟨206259134799477155277656411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137506089866318103518437607 206259134799477155277656411)
  ·
    refine ⟨309388702199215732916484617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206259134799477155277656411 309388702199215732916484617)
    ·
      refine ⟨232041526649411799687363463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309388702199215732916484617 232041526649411799687363463)
      ·
        refine ⟨348062289974117699531045195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232041526649411799687363463 348062289974117699531045195)
        ·
          refine ⟨522093434961176549296567793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348062289974117699531045195 522093434961176549296567793)
          ·
            refine ⟨391570076220882411972425845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522093434961176549296567793 391570076220882411972425845)
            ·
              refine ⟨36709694645707726122414923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 391570076220882411972425845 36709694645707726122414923)
              ·
                refine ⟨55064541968561589183622385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36709694645707726122414923 55064541968561589183622385)
                ·
                  refine ⟨41298406476421191887716789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55064541968561589183622385 41298406476421191887716789)
                  ·
                    refine ⟨3871725607164486739473449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41298406476421191887716789 3871725607164486739473449)
                    ·
                      refine ⟨2903794205373365054605087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3871725607164486739473449 2903794205373365054605087)
                      ·
                        rfl

theorem cell23_5655119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 5, 2].length) (baseStart_5655119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655119 prefixEnd_5655119 := by exact prefixLift 5655119
  have htrace : WordTrace (prefixWord ++ tailWord_5655119) baseStart_5655119 baseEnd_5655119 := by
    simpa [prefixWord, tailWord_5655119, baseEnd_5655119] using wordTrace_append hprefix tailTrace_5655119
  have hstable : (prefixWord ++ tailWord_5655119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655119).length < 2 ^ (prefixWord ++ tailWord_5655119).sum := by decide
  have hdescent : baseEnd_5655119 < baseStart_5655119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655186 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_5655186 : Nat := 118140960795 + 5655186 * 2 ^ 59
def prefixEnd_5655186 : Nat := 4983230072969 + 3 ^ 40 * 5655186 * 2
def baseEnd_5655186 : Nat := 2903828608577216292467279

theorem tailTrace_5655186 : CollatzResearch.WordTrace tailWord_5655186 prefixEnd_5655186 2903828608577216292467279 := by
  unfold tailWord_5655186
  simp only [CollatzResearch.WordTrace]
  refine ⟨51565394622558606430086353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137507718993489617146896941 51565394622558606430086353)
  ·
    refine ⟨38674045966918954822564765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51565394622558606430086353 38674045966918954822564765)
    ·
      refine ⟨14502767237594608058461787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38674045966918954822564765 14502767237594608058461787)
      ·
        refine ⟨21754150856391912087692681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14502767237594608058461787 21754150856391912087692681)
        ·
          refine ⟨16315613142293934065769511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21754150856391912087692681 16315613142293934065769511)
          ·
            refine ⟨24473419713440901098654267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16315613142293934065769511 24473419713440901098654267)
            ·
              refine ⟨36710129570161351647981401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24473419713440901098654267 36710129570161351647981401)
              ·
                refine ⟨27532597177621013735986051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36710129570161351647981401 27532597177621013735986051)
                ·
                  refine ⟨41298895766431520603979077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27532597177621013735986051 41298895766431520603979077)
                  ·
                    refine ⟨7743542956205910113246077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41298895766431520603979077 7743542956205910113246077)
                    ·
                      refine ⟨2903828608577216292467279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7743542956205910113246077 2903828608577216292467279)
                      ·
                        rfl

theorem cell23_5655186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_5655186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655186 prefixEnd_5655186 := by exact prefixLift 5655186
  have htrace : WordTrace (prefixWord ++ tailWord_5655186) baseStart_5655186 baseEnd_5655186 := by
    simpa [prefixWord, tailWord_5655186, baseEnd_5655186] using wordTrace_append hprefix tailTrace_5655186
  have hstable : (prefixWord ++ tailWord_5655186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655186).length < 2 ^ (prefixWord ++ tailWord_5655186).sum := by decide
  have hdescent : baseEnd_5655186 < baseStart_5655186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655249 : List Nat := [1, 2, 2, 1, 2, 3, 2, 3, 1, 6]
def baseStart_5655249 : Nat := 118140960795 + 5655249 * 2 ^ 59
def prefixEnd_5655249 : Nat := 4983230072969 + 3 ^ 40 * 5655249 * 2
def baseEnd_5655249 : Nat := 967953652619483181993163

theorem tailTrace_5655249 : CollatzResearch.WordTrace tailWord_5655249 prefixEnd_5655249 967953652619483181993163 := by
  unfold tailWord_5655249
  simp only [CollatzResearch.WordTrace]
  refine ⟨206263876289006187479888801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137509250859337458319925867 206263876289006187479888801)
  ·
    refine ⟨154697907216754640609916601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206263876289006187479888801 154697907216754640609916601)
    ·
      refine ⟨116023430412565980457437451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154697907216754640609916601 116023430412565980457437451)
      ·
        refine ⟨174035145618848970686156177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116023430412565980457437451 174035145618848970686156177)
        ·
          refine ⟨130526359214136728014617133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174035145618848970686156177 130526359214136728014617133)
          ·
            refine ⟨48947384705301273005481425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130526359214136728014617133 48947384705301273005481425)
            ·
              refine ⟨36710538528975954754111069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48947384705301273005481425 36710538528975954754111069)
              ·
                refine ⟨13766451948365983032791651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36710538528975954754111069 13766451948365983032791651)
                ·
                  refine ⟨20649677922548974549187477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13766451948365983032791651 20649677922548974549187477)
                  ·
                    refine ⟨967953652619483181993163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20649677922548974549187477 967953652619483181993163)
                    ·
                      rfl

theorem cell23_5655249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_5655249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655249 prefixEnd_5655249 := by exact prefixLift 5655249
  have htrace : WordTrace (prefixWord ++ tailWord_5655249) baseStart_5655249 baseEnd_5655249 := by
    simpa [prefixWord, tailWord_5655249, baseEnd_5655249] using wordTrace_append hprefix tailTrace_5655249
  have hstable : (prefixWord ++ tailWord_5655249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655249).length < 2 ^ (prefixWord ++ tailWord_5655249).sum := by decide
  have hdescent : baseEnd_5655249 < baseStart_5655249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655253 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 3, 5]
def baseStart_5655253 : Nat := 118140960795 + 5655253 * 2 ^ 59
def prefixEnd_5655253 : Nat := 4983230072969 + 3 ^ 40 * 5655253 * 2
def baseEnd_5655253 : Nat := 967954337260355843443157

theorem tailTrace_5655253 : CollatzResearch.WordTrace tailWord_5655253 prefixEnd_5655253 967954337260355843443157 := by
  unfold tailWord_5655253
  simp only [CollatzResearch.WordTrace]
  refine ⟨206264022180991696163034413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137509348120661130775356275 206264022180991696163034413)
  ·
    refine ⟨77349008317871886061137905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206264022180991696163034413 77349008317871886061137905)
    ·
      refine ⟨58011756238403914545853429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77349008317871886061137905 58011756238403914545853429)
      ·
        refine ⟨5438602147350366988673759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58011756238403914545853429 5438602147350366988673759)
        ·
          refine ⟨8157903221025550483010639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5438602147350366988673759 8157903221025550483010639)
          ·
            refine ⟨12236854831538325724515959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8157903221025550483010639 12236854831538325724515959)
            ·
              refine ⟨18355282247307488586773939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12236854831538325724515959 18355282247307488586773939)
              ·
                refine ⟨27532923370961232880160909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18355282247307488586773939 27532923370961232880160909)
                ·
                  refine ⟨10324846264110462330060341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27532923370961232880160909 10324846264110462330060341)
                  ·
                    refine ⟨967954337260355843443157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10324846264110462330060341 967954337260355843443157)
                    ·
                      rfl

theorem cell23_5655253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_5655253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655253 prefixEnd_5655253 := by exact prefixLift 5655253
  have htrace : WordTrace (prefixWord ++ tailWord_5655253) baseStart_5655253 baseEnd_5655253 := by
    simpa [prefixWord, tailWord_5655253, baseEnd_5655253] using wordTrace_append hprefix tailTrace_5655253
  have hstable : (prefixWord ++ tailWord_5655253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655253).length < 2 ^ (prefixWord ++ tailWord_5655253).sum := by decide
  have hdescent : baseEnd_5655253 < baseStart_5655253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655256 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 3, 1, 4]
def baseStart_5655256 : Nat := 118140960795 + 5655256 * 2 ^ 59
def prefixEnd_5655256 : Nat := 4983230072969 + 3 ^ 40 * 5655256 * 2
def baseEnd_5655256 : Nat := 2903864552223031018591957

theorem tailTrace_5655256 : CollatzResearch.WordTrace tailWord_5655256 prefixEnd_5655256 2903864552223031018591957 := by
  unfold tailWord_5655256
  simp only [CollatzResearch.WordTrace]
  refine ⟨103132065799990413837696811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137509421066653885116929081 103132065799990413837696811)
  ·
    refine ⟨154698098699985620756545217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103132065799990413837696811 154698098699985620756545217)
    ·
      refine ⟨116023574024989215567408913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154698098699985620756545217 116023574024989215567408913)
      ·
        refine ⟨87017680518741911675556685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116023574024989215567408913 87017680518741911675556685)
        ·
          refine ⟨32631630194528216878333757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87017680518741911675556685 32631630194528216878333757)
          ·
            refine ⟨12236861322948081329375159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32631630194528216878333757 12236861322948081329375159)
            ·
              refine ⟨18355291984422121994062739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12236861322948081329375159 18355291984422121994062739)
              ·
                refine ⟨27532937976633182991094109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18355291984422121994062739 27532937976633182991094109)
                ·
                  refine ⟨10324851741237443621660291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27532937976633182991094109 10324851741237443621660291)
                  ·
                    refine ⟨15487277611856165432490437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10324851741237443621660291 15487277611856165432490437)
                    ·
                      refine ⟨2903864552223031018591957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15487277611856165432490437 2903864552223031018591957)
                      ·
                        rfl

theorem cell23_5655256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_5655256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655256 prefixEnd_5655256 := by exact prefixLift 5655256
  have htrace : WordTrace (prefixWord ++ tailWord_5655256) baseStart_5655256 baseEnd_5655256 := by
    simpa [prefixWord, tailWord_5655256, baseEnd_5655256] using wordTrace_append hprefix tailTrace_5655256
  have hstable : (prefixWord ++ tailWord_5655256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655256).length < 2 ^ (prefixWord ++ tailWord_5655256).sum := by decide
  have hdescent : baseEnd_5655256 < baseStart_5655256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655260 : List Nat := [2, 2, 5, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_5655260 : Nat := 118140960795 + 5655260 * 2 ^ 59
def prefixEnd_5655260 : Nat := 4983230072969 + 3 ^ 40 * 5655260 * 2
def baseEnd_5655260 : Nat := 2903866606145649002941939

theorem tailTrace_5655260 : CollatzResearch.WordTrace tailWord_5655260 prefixEnd_5655260 2903866606145649002941939 := by
  unfold tailWord_5655260
  simp only [CollatzResearch.WordTrace]
  refine ⟨103132138745983168179269617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137509518327977557572359489 103132138745983168179269617)
  ·
    refine ⟨77349104059487376134452213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103132138745983168179269617 77349104059487376134452213)
    ·
      refine ⟨7251478505576941512604895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77349104059487376134452213 7251478505576941512604895)
      ·
        refine ⟨10877217758365412268907343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7251478505576941512604895 10877217758365412268907343)
        ·
          refine ⟨16315826637548118403361015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10877217758365412268907343 16315826637548118403361015)
          ·
            refine ⟨24473739956322177605041523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16315826637548118403361015 24473739956322177605041523)
            ·
              refine ⟨36710609934483266407562285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24473739956322177605041523 36710609934483266407562285)
              ·
                refine ⟨13766478725431224902835857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36710609934483266407562285 13766478725431224902835857)
                ·
                  refine ⟨10324859044073418677126893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13766478725431224902835857 10324859044073418677126893)
                  ·
                    refine ⟨3871822141527532003922585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10324859044073418677126893 3871822141527532003922585)
                    ·
                      refine ⟨2903866606145649002941939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3871822141527532003922585 2903866606145649002941939)
                      ·
                        rfl

theorem cell23_5655260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_5655260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655260 prefixEnd_5655260 := by exact prefixLift 5655260
  have htrace : WordTrace (prefixWord ++ tailWord_5655260) baseStart_5655260 baseEnd_5655260 := by
    simpa [prefixWord, tailWord_5655260, baseEnd_5655260] using wordTrace_append hprefix tailTrace_5655260
  have hstable : (prefixWord ++ tailWord_5655260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655260).length < 2 ^ (prefixWord ++ tailWord_5655260).sum := by decide
  have hdescent : baseEnd_5655260 < baseStart_5655260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655286 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_5655286 : Nat := 118140960795 + 5655286 * 2 ^ 59
def prefixEnd_5655286 : Nat := 4983230072969 + 3 ^ 40 * 5655286 * 2
def baseEnd_5655286 : Nat := 2903879956642665901216819

theorem tailTrace_5655286 : CollatzResearch.WordTrace tailWord_5655286 prefixEnd_5655286 2903879956642665901216819 := by
  unfold tailWord_5655286
  simp only [CollatzResearch.WordTrace]
  refine ⟨12891576611867008924936607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137510150526581428532657141 12891576611867008924936607)
  ·
    refine ⟨19337364917800513387404911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12891576611867008924936607 19337364917800513387404911)
    ·
      refine ⟨29006047376700770081107367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19337364917800513387404911 29006047376700770081107367)
      ·
        refine ⟨43509071065051155121661051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29006047376700770081107367 43509071065051155121661051)
        ·
          refine ⟨65263606597576732682491577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43509071065051155121661051 65263606597576732682491577)
          ·
            refine ⟨48947704948182549511868683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65263606597576732682491577 48947704948182549511868683)
            ·
              refine ⟨73421557422273824267803025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48947704948182549511868683 73421557422273824267803025)
              ·
                refine ⟨55066168066705368200852269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73421557422273824267803025 55066168066705368200852269)
                ·
                  refine ⟨20649813025014513075319601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55066168066705368200852269 20649813025014513075319601)
                  ·
                    refine ⟨15487359768760884806489701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20649813025014513075319601 15487359768760884806489701)
                    ·
                      refine ⟨2903879956642665901216819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15487359768760884806489701 2903879956642665901216819)
                      ·
                        rfl

theorem cell23_5655286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_5655286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655286 prefixEnd_5655286 := by exact prefixLift 5655286
  have htrace : WordTrace (prefixWord ++ tailWord_5655286) baseStart_5655286 baseEnd_5655286 := by
    simpa [prefixWord, tailWord_5655286, baseEnd_5655286] using wordTrace_append hprefix tailTrace_5655286
  have hstable : (prefixWord ++ tailWord_5655286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655286).length < 2 ^ (prefixWord ++ tailWord_5655286).sum := by decide
  have hdescent : baseEnd_5655286 < baseStart_5655286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655303 : List Nat := [1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 4]
def baseStart_5655303 : Nat := 118140960795 + 5655303 * 2 ^ 59
def prefixEnd_5655303 : Nat := 4983230072969 + 3 ^ 40 * 5655303 * 2
def baseEnd_5655303 : Nat := 2903888685813792334704241

theorem tailTrace_5655303 : CollatzResearch.WordTrace tailWord_5655303 prefixEnd_5655303 2903888685813792334704241 := by
  unfold tailWord_5655303
  simp only [CollatzResearch.WordTrace]
  refine ⟨206265845830810554702354563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137510563887207036468236375 206265845830810554702354563)
  ·
    refine ⟨309398768746215832053531845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206265845830810554702354563 309398768746215832053531845)
    ·
      refine ⟨58012269139915468510037221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 309398768746215832053531845 58012269139915468510037221)
      ·
        refine ⟨10877300463734150345631979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58012269139915468510037221 10877300463734150345631979)
        ·
          refine ⟨16315950695601225518447969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10877300463734150345631979 16315950695601225518447969)
          ·
            refine ⟨12236963021700919138835977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16315950695601225518447969 12236963021700919138835977)
            ·
              refine ⟨9177722266275689354126983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12236963021700919138835977 9177722266275689354126983)
              ·
                refine ⟨13766583399413534031190475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9177722266275689354126983 13766583399413534031190475)
                ·
                  refine ⟨20649875099120301046785713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13766583399413534031190475 20649875099120301046785713)
                  ·
                    refine ⟨15487406324340225785089285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20649875099120301046785713 15487406324340225785089285)
                    ·
                      refine ⟨2903888685813792334704241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15487406324340225785089285 2903888685813792334704241)
                      ·
                        rfl

theorem cell23_5655303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_5655303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655303 prefixEnd_5655303 := by exact prefixLift 5655303
  have htrace : WordTrace (prefixWord ++ tailWord_5655303) baseStart_5655303 baseEnd_5655303 := by
    simpa [prefixWord, tailWord_5655303, baseEnd_5655303] using wordTrace_append hprefix tailTrace_5655303
  have hstable : (prefixWord ++ tailWord_5655303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655303).length < 2 ^ (prefixWord ++ tailWord_5655303).sum := by decide
  have hdescent : baseEnd_5655303 < baseStart_5655303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655339 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 2, 6]
def baseStart_5655339 : Nat := 118140960795 + 5655339 * 2 ^ 59
def prefixEnd_5655339 : Nat := 4983230072969 + 3 ^ 40 * 5655339 * 2
def baseEnd_5655339 : Nat := 967969057039118064618025

theorem tailTrace_5655339 : CollatzResearch.WordTrace tailWord_5655339 prefixEnd_5655339 967969057039118064618025 := by
  unfold tailWord_5655339
  simp only [CollatzResearch.WordTrace]
  refine ⟨206267158858680132850665071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137511439239120088567110047 206267158858680132850665071)
  ·
    refine ⟨309400738288020199275997607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206267158858680132850665071 309400738288020199275997607)
    ·
      refine ⟨464101107432030298913996411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309400738288020199275997607 464101107432030298913996411)
      ·
        refine ⟨696151661148045448370994617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464101107432030298913996411 696151661148045448370994617)
        ·
          refine ⟨522113745861034086278245963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 696151661148045448370994617 522113745861034086278245963)
          ·
            refine ⟨783170618791551129417368945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522113745861034086278245963 783170618791551129417368945)
            ·
              refine ⟨587377964093663347063026709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 783170618791551129417368945 587377964093663347063026709)
              ·
                refine ⟨27533342066890469393579377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 587377964093663347063026709 27533342066890469393579377)
                ·
                  refine ⟨20650006550167852045184533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27533342066890469393579377 20650006550167852045184533)
                  ·
                    refine ⟨967969057039118064618025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20650006550167852045184533 967969057039118064618025)
                    ·
                      rfl

theorem cell23_5655339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 6].length) (baseStart_5655339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655339 prefixEnd_5655339 := by exact prefixLift 5655339
  have htrace : WordTrace (prefixWord ++ tailWord_5655339) baseStart_5655339 baseEnd_5655339 := by
    simpa [prefixWord, tailWord_5655339, baseEnd_5655339] using wordTrace_append hprefix tailTrace_5655339
  have hstable : (prefixWord ++ tailWord_5655339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655339).length < 2 ^ (prefixWord ++ tailWord_5655339).sum := by decide
  have hdescent : baseEnd_5655339 < baseStart_5655339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655357 : List Nat := [1, 4, 1, 4, 3, 1, 1, 1, 1, 3, 3]
def baseStart_5655357 : Nat := 118140960795 + 5655357 * 2 ^ 59
def prefixEnd_5655357 : Nat := 4983230072969 + 3 ^ 40 * 5655357 * 2
def baseEnd_5655357 : Nat := 2903916413769135123428993

theorem tailTrace_5655357 : CollatzResearch.WordTrace tailWord_5655357 prefixEnd_5655357 2903916413769135123428993 := by
  unfold tailWord_5655357
  simp only [CollatzResearch.WordTrace]
  refine ⟨206267815372614921924820325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137511876915076614616546883 206267815372614921924820325)
  ·
    refine ⟨38675215382365297860903811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206267815372614921924820325 38675215382365297860903811)
    ·
      refine ⟨58012823073547946791355717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38675215382365297860903811 58012823073547946791355717)
      ·
        refine ⟨10877404326290240023379197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58012823073547946791355717 10877404326290240023379197)
        ·
          refine ⟨4079026622358840008767199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10877404326290240023379197 4079026622358840008767199)
          ·
            refine ⟨6118539933538260013150799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4079026622358840008767199 6118539933538260013150799)
            ·
              refine ⟨9177809900307390019726199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6118539933538260013150799 9177809900307390019726199)
              ·
                refine ⟨13766714850461085029589299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9177809900307390019726199 13766714850461085029589299)
                ·
                  refine ⟨20650072275691627544383949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13766714850461085029589299 20650072275691627544383949)
                  ·
                    refine ⟨7743777103384360329143981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20650072275691627544383949 7743777103384360329143981)
                    ·
                      refine ⟨2903916413769135123428993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7743777103384360329143981 2903916413769135123428993)
                      ·
                        rfl

theorem cell23_5655357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_5655357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655357 prefixEnd_5655357 := by exact prefixLift 5655357
  have htrace : WordTrace (prefixWord ++ tailWord_5655357) baseStart_5655357 baseEnd_5655357 := by
    simpa [prefixWord, tailWord_5655357, baseEnd_5655357] using wordTrace_append hprefix tailTrace_5655357
  have hstable : (prefixWord ++ tailWord_5655357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655357).length < 2 ^ (prefixWord ++ tailWord_5655357).sum := by decide
  have hdescent : baseEnd_5655357 < baseStart_5655357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655414 : List Nat := [5, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2]
def baseStart_5655414 : Nat := 118140960795 + 5655414 * 2 ^ 59
def prefixEnd_5655414 : Nat := 4983230072969 + 3 ^ 40 * 5655414 * 2
def baseEnd_5655414 : Nat := 2903945682166441400416231

theorem tailTrace_5655414 : CollatzResearch.WordTrace tailWord_5655414 prefixEnd_5655414 2903945682166441400416231 := by
  unfold tailWord_5655414
  simp only [CollatzResearch.WordTrace]
  refine ⟨12891868395838026291227831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137513262888938947106430197 12891868395838026291227831)
  ·
    refine ⟨19337802593757039436841747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12891868395838026291227831 19337802593757039436841747)
    ·
      refine ⟨29006703890635559155262621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19337802593757039436841747 29006703890635559155262621)
      ·
        refine ⟨10877513958988334683223483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29006703890635559155262621 10877513958988334683223483)
        ·
          refine ⟨16316270938482502024835225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10877513958988334683223483 16316270938482502024835225)
          ·
            refine ⟨12237203203861876518626419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16316270938482502024835225 12237203203861876518626419)
            ·
              refine ⟨18355804805792814777939629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12237203203861876518626419 18355804805792814777939629)
              ·
                refine ⟨6883426802172305541727361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18355804805792814777939629 6883426802172305541727361)
                ·
                  refine ⟨5162570101629229156295521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6883426802172305541727361 5162570101629229156295521)
                  ·
                    refine ⟨3871927576221921867221641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5162570101629229156295521 3871927576221921867221641)
                    ·
                      refine ⟨2903945682166441400416231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3871927576221921867221641 2903945682166441400416231)
                      ·
                        rfl

theorem cell23_5655414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_5655414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655414 prefixEnd_5655414 := by exact prefixLift 5655414
  have htrace : WordTrace (prefixWord ++ tailWord_5655414) baseStart_5655414 baseEnd_5655414 := by
    simpa [prefixWord, tailWord_5655414, baseEnd_5655414] using wordTrace_append hprefix tailTrace_5655414
  have hstable : (prefixWord ++ tailWord_5655414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655414).length < 2 ^ (prefixWord ++ tailWord_5655414).sum := by decide
  have hdescent : baseEnd_5655414 < baseStart_5655414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655433 : List Nat := [1, 2, 1, 1, 5, 3, 2, 1, 2, 5]
def baseStart_5655433 : Nat := 118140960795 + 5655433 * 2 ^ 59
def prefixEnd_5655433 : Nat := 4983230072969 + 3 ^ 40 * 5655433 * 2
def baseEnd_5655433 : Nat := 967985146099625608692881

theorem tailTrace_5655433 : CollatzResearch.WordTrace tailWord_5655433 prefixEnd_5655433 967985146099625608692881 := by
  unfold tailWord_5655433
  simp only [CollatzResearch.WordTrace]
  refine ⟨206270587320339586904586953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137513724880226391269724635 206270587320339586904586953)
  ·
    refine ⟨154702940490254690178440215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206270587320339586904586953 154702940490254690178440215)
    ·
      refine ⟨232054410735382035267660323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154702940490254690178440215 232054410735382035267660323)
      ·
        refine ⟨348081616103073052901490485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232054410735382035267660323 348081616103073052901490485)
        ·
          refine ⟨32632651509663098709514733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 348081616103073052901490485 32632651509663098709514733)
          ·
            refine ⟨12237244316123662016068025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32632651509663098709514733 12237244316123662016068025)
            ·
              refine ⟨9177933237092746512051019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12237244316123662016068025 9177933237092746512051019)
              ·
                refine ⟨13766899855639119768076529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9177933237092746512051019 13766899855639119768076529)
                ·
                  refine ⟨10325174891729339826057397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13766899855639119768076529 10325174891729339826057397)
                  ·
                    refine ⟨967985146099625608692881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10325174891729339826057397 967985146099625608692881)
                    ·
                      rfl

theorem cell23_5655433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 5].length) (baseStart_5655433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655433 prefixEnd_5655433 := by exact prefixLift 5655433
  have htrace : WordTrace (prefixWord ++ tailWord_5655433) baseStart_5655433 baseEnd_5655433 := by
    simpa [prefixWord, tailWord_5655433, baseEnd_5655433] using wordTrace_append hprefix tailTrace_5655433
  have hstable : (prefixWord ++ tailWord_5655433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655433).length < 2 ^ (prefixWord ++ tailWord_5655433).sum := by decide
  have hdescent : baseEnd_5655433 < baseStart_5655433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655436 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 1, 3, 4]
def baseStart_5655436 : Nat := 118140960795 + 5655436 * 2 ^ 59
def prefixEnd_5655436 : Nat := 4983230072969 + 3 ^ 40 * 5655436 * 2
def baseEnd_5655436 : Nat := 2903956978740840314341129

theorem tailTrace_5655436 : CollatzResearch.WordTrace tailWord_5655436 prefixEnd_5655436 2903956978740840314341129 := by
  unfold tailWord_5655436
  simp only [CollatzResearch.WordTrace]
  refine ⟨103135348369664359208473081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137513797826219145611297441 103135348369664359208473081)
  ·
    refine ⟨77351511277248269406354811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103135348369664359208473081 77351511277248269406354811)
    ·
      refine ⟨116027266915872404109532217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77351511277248269406354811 116027266915872404109532217)
      ·
        refine ⟨87020450186904303082149163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116027266915872404109532217 87020450186904303082149163)
        ·
          refine ⟨130530675280356454623223745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87020450186904303082149163 130530675280356454623223745)
          ·
            refine ⟨97898006460267340967417809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130530675280356454623223745 97898006460267340967417809)
            ·
              refine ⟨73423504845200505725563357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97898006460267340967417809 73423504845200505725563357)
              ·
                refine ⟨27533814316950189647086259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73423504845200505725563357 27533814316950189647086259)
                ·
                  refine ⟨41300721475425284470629389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27533814316950189647086259 41300721475425284470629389)
                  ·
                    refine ⟨15487770553284481676486021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41300721475425284470629389 15487770553284481676486021)
                    ·
                      refine ⟨2903956978740840314341129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15487770553284481676486021 2903956978740840314341129)
                      ·
                        rfl

theorem cell23_5655436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_5655436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655436 prefixEnd_5655436 := by exact prefixLift 5655436
  have htrace : WordTrace (prefixWord ++ tailWord_5655436) baseStart_5655436 baseEnd_5655436 := by
    simpa [prefixWord, tailWord_5655436, baseEnd_5655436] using wordTrace_append hprefix tailTrace_5655436
  have hstable : (prefixWord ++ tailWord_5655436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655436).length < 2 ^ (prefixWord ++ tailWord_5655436).sum := by decide
  have hdescent : baseEnd_5655436 < baseStart_5655436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655453 : List Nat := [1, 4, 2, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_5655453 : Nat := 118140960795 + 5655453 * 2 ^ 59
def prefixEnd_5655453 : Nat := 4983230072969 + 3 ^ 40 * 5655453 * 2
def baseEnd_5655453 : Nat := 2903965707911966747828551

theorem tailTrace_5655453 : CollatzResearch.WordTrace tailWord_5655453 prefixEnd_5655453 2903965707911966747828551 := by
  unfold tailWord_5655453
  simp only [CollatzResearch.WordTrace]
  refine ⟨206271316780267130320315013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137514211186844753546876675 206271316780267130320315013)
  ·
    refine ⟨38675871896300086935059065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206271316780267130320315013 38675871896300086935059065)
    ·
      refine ⟨29006903922225065201294299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38675871896300086935059065 29006903922225065201294299)
      ·
        refine ⟨43510355883337597801941449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29006903922225065201294299 43510355883337597801941449)
        ·
          refine ⟨32632766912503198351456087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43510355883337597801941449 32632766912503198351456087)
          ·
            refine ⟨48949150368754797527184131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32632766912503198351456087 48949150368754797527184131)
            ·
              refine ⟨73423725553132196290776197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48949150368754797527184131 73423725553132196290776197)
              ·
                refine ⟨13766948541212286804520537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73423725553132196290776197 13766948541212286804520537)
                ·
                  refine ⟨10325211405909215103390403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13766948541212286804520537 10325211405909215103390403)
                  ·
                    refine ⟨15487817108863822655085605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10325211405909215103390403 15487817108863822655085605)
                    ·
                      refine ⟨2903965707911966747828551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15487817108863822655085605 2903965707911966747828551)
                      ·
                        rfl

theorem cell23_5655453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_5655453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655453 prefixEnd_5655453 := by exact prefixLift 5655453
  have htrace : WordTrace (prefixWord ++ tailWord_5655453) baseStart_5655453 baseEnd_5655453 := by
    simpa [prefixWord, tailWord_5655453, baseEnd_5655453] using wordTrace_append hprefix tailTrace_5655453
  have hstable : (prefixWord ++ tailWord_5655453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655453).length < 2 ^ (prefixWord ++ tailWord_5655453).sum := by decide
  have hdescent : baseEnd_5655453 < baseStart_5655453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655510 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 8]
def baseStart_5655510 : Nat := 118140960795 + 5655510 * 2 ^ 59
def prefixEnd_5655510 : Nat := 4983230072969 + 3 ^ 40 * 5655510 * 2
def baseEnd_5655510 : Nat := 322666108478808113868421

theorem tailTrace_5655510 : CollatzResearch.WordTrace tailWord_5655510 prefixEnd_5655510 322666108478808113868421 := by
  unfold tailWord_5655510
  simp only [CollatzResearch.WordTrace]
  refine ⟨12892087233816289315946249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137515597160707086036759989 12892087233816289315946249)
  ·
    refine ⟨9669065425362216986959687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12892087233816289315946249 9669065425362216986959687)
    ·
      refine ⟨14503598138043325480439531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9669065425362216986959687 14503598138043325480439531)
      ·
        refine ⟨21755397207064988220659297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14503598138043325480439531 21755397207064988220659297)
        ·
          refine ⟨16316547905298741165494473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21755397207064988220659297 16316547905298741165494473)
          ·
            refine ⟨12237410928974055874120855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16316547905298741165494473 12237410928974055874120855)
            ·
              refine ⟨18356116393461083811181283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12237410928974055874120855 18356116393461083811181283)
              ·
                refine ⟨27534174590191625716771925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18356116393461083811181283 27534174590191625716771925)
                ·
                  refine ⟨322666108478808113868421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27534174590191625716771925 322666108478808113868421)
                  ·
                    rfl

theorem cell23_5655510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_5655510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655510 prefixEnd_5655510 := by exact prefixLift 5655510
  have htrace : WordTrace (prefixWord ++ tailWord_5655510) baseStart_5655510 baseEnd_5655510 := by
    simpa [prefixWord, tailWord_5655510, baseEnd_5655510] using wordTrace_append hprefix tailTrace_5655510
  have hstable : (prefixWord ++ tailWord_5655510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655510).length < 2 ^ (prefixWord ++ tailWord_5655510).sum := by decide
  have hdescent : baseEnd_5655510 < baseStart_5655510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655530 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 1, 5, 2]
def baseStart_5655530 : Nat := 118140960795 + 5655530 * 2 ^ 59
def prefixEnd_5655530 : Nat := 4983230072969 + 3 ^ 40 * 5655530 * 2
def baseEnd_5655530 : Nat := 2904005245922362946565697

theorem tailTrace_5655530 : CollatzResearch.WordTrace tailWord_5655530 prefixEnd_5655530 2904005245922362946565697 := by
  unfold tailWord_5655530
  simp only [CollatzResearch.WordTrace]
  refine ⟨51568531300247043117717011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137516083467325448313912029 51568531300247043117717011)
  ·
    refine ⟨77352796950370564676575517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51568531300247043117717011 77352796950370564676575517)
    ·
      refine ⟨29007298856388961753715819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77352796950370564676575517 29007298856388961753715819)
      ·
        refine ⟨43510948284583442630573729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29007298856388961753715819 43510948284583442630573729)
        ·
          refine ⟨32633211213437581972930297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43510948284583442630573729 32633211213437581972930297)
          ·
            refine ⟨24474908410078186479697723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32633211213437581972930297 24474908410078186479697723)
            ·
              refine ⟨36712362615117279719546585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24474908410078186479697723 36712362615117279719546585)
              ·
                refine ⟨27534271961337959789659939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36712362615117279719546585 27534271961337959789659939)
                ·
                  refine ⟨41301407942006939684489909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27534271961337959789659939 41301407942006939684489909)
                  ·
                    refine ⟨3872006994563150595420929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41301407942006939684489909 3872006994563150595420929)
                    ·
                      refine ⟨2904005245922362946565697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3872006994563150595420929 2904005245922362946565697)
                      ·
                        rfl

theorem cell23_5655530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_5655530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655530 prefixEnd_5655530 := by exact prefixLift 5655530
  have htrace : WordTrace (prefixWord ++ tailWord_5655530) baseStart_5655530 baseEnd_5655530 := by
    simpa [prefixWord, tailWord_5655530, baseEnd_5655530] using wordTrace_append hprefix tailTrace_5655530
  have hstable : (prefixWord ++ tailWord_5655530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655530).length < 2 ^ (prefixWord ++ tailWord_5655530).sum := by decide
  have hdescent : baseEnd_5655530 < baseStart_5655530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655560 : List Nat := [2, 1, 3, 2, 1, 3, 2, 3, 1, 1, 4]
def baseStart_5655560 : Nat := 118140960795 + 5655560 * 2 ^ 59
def prefixEnd_5655560 : Nat := 4983230072969 + 3 ^ 40 * 5655560 * 2
def baseEnd_5655560 : Nat := 2904020650341997829190559

theorem tailTrace_5655560 : CollatzResearch.WordTrace tailWord_5655560 prefixEnd_5655560 2904020650341997829190559 := by
  unfold tailWord_5655560
  simp only [CollatzResearch.WordTrace]
  refine ⟨103137609695439743797230067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137516812927252991729640089 103137609695439743797230067)
  ·
    refine ⟨154706414543159615695845101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103137609695439743797230067 154706414543159615695845101)
    ·
      refine ⟨58014905453684855885941913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154706414543159615695845101 58014905453684855885941913)
      ·
        refine ⟨43511179090263641914456435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58014905453684855885941913 43511179090263641914456435)
        ·
          refine ⟨65266768635395462871684653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43511179090263641914456435 65266768635395462871684653)
          ·
            refine ⟨24475038238273298576881745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65266768635395462871684653 24475038238273298576881745)
            ·
              refine ⟨18356278678704973932661309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24475038238273298576881745 18356278678704973932661309)
              ·
                refine ⟨6883604504514365224747991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18356278678704973932661309 6883604504514365224747991)
                ·
                  refine ⟨10325406756771547837121987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6883604504514365224747991 10325406756771547837121987)
                  ·
                    refine ⟨15488110135157321755682981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10325406756771547837121987 15488110135157321755682981)
                    ·
                      refine ⟨2904020650341997829190559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15488110135157321755682981 2904020650341997829190559)
                      ·
                        rfl

theorem cell23_5655560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_5655560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655560 prefixEnd_5655560 := by exact prefixLift 5655560
  have htrace : WordTrace (prefixWord ++ tailWord_5655560) baseStart_5655560 baseEnd_5655560 := by
    simpa [prefixWord, tailWord_5655560, baseEnd_5655560] using wordTrace_append hprefix tailTrace_5655560
  have hstable : (prefixWord ++ tailWord_5655560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655560).length < 2 ^ (prefixWord ++ tailWord_5655560).sum := by decide
  have hdescent : baseEnd_5655560 < baseStart_5655560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655563 : List Nat := [1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 5]
def baseStart_5655563 : Nat := 118140960795 + 5655563 * 2 ^ 59
def prefixEnd_5655563 : Nat := 4983230072969 + 3 ^ 40 * 5655563 * 2
def baseEnd_5655563 : Nat := 2904022190783961317453045

theorem tailTrace_5655563 : CollatzResearch.WordTrace tailWord_5655563 prefixEnd_5655563 2904022190783961317453045 := by
  unfold tailWord_5655563
  simp only [CollatzResearch.WordTrace]
  refine ⟨206275328809868619106819343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137516885873245746071212895 206275328809868619106819343)
  ·
    refine ⟨309412993214802928660229015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206275328809868619106819343 309412993214802928660229015)
    ·
      refine ⟨464119489822204392990343523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309412993214802928660229015 464119489822204392990343523)
      ·
        refine ⟨696179234733306589485515285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464119489822204392990343523 696179234733306589485515285)
        ·
          refine ⟨32633401628123746382133529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 696179234733306589485515285 32633401628123746382133529)
          ·
            refine ⟨24475051221092809786600147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32633401628123746382133529 24475051221092809786600147)
            ·
              refine ⟨36712576831639214679900221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24475051221092809786600147 36712576831639214679900221)
              ·
                refine ⟨13767216311864705504962583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36712576831639214679900221 13767216311864705504962583)
                ·
                  refine ⟨20650824467797058257443875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13767216311864705504962583 20650824467797058257443875)
                  ·
                    refine ⟨30976236701695587386165813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20650824467797058257443875 30976236701695587386165813)
                    ·
                      refine ⟨2904022190783961317453045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30976236701695587386165813 2904022190783961317453045)
                      ·
                        rfl

theorem cell23_5655563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 5].length) (baseStart_5655563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655563 prefixEnd_5655563 := by exact prefixLift 5655563
  have htrace : WordTrace (prefixWord ++ tailWord_5655563) baseStart_5655563 baseEnd_5655563 := by
    simpa [prefixWord, tailWord_5655563, baseEnd_5655563] using wordTrace_append hprefix tailTrace_5655563
  have hstable : (prefixWord ++ tailWord_5655563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655563).length < 2 ^ (prefixWord ++ tailWord_5655563).sum := by decide
  have hdescent : baseEnd_5655563 < baseStart_5655563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655573 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_5655573 : Nat := 118140960795 + 5655573 * 2 ^ 59
def prefixEnd_5655573 : Nat := 4983230072969 + 3 ^ 40 * 5655573 * 2
def baseEnd_5655573 : Nat := 2904027325590506278327999

theorem tailTrace_5655573 : CollatzResearch.WordTrace tailWord_5655573 prefixEnd_5655573 2904027325590506278327999 := by
  unfold tailWord_5655573
  simp only [CollatzResearch.WordTrace]
  refine ⟨206275693539832390814683373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137517129026554927209788915 206275693539832390814683373)
  ·
    refine ⟨77353385077437146555506265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206275693539832390814683373 77353385077437146555506265)
    ·
      refine ⟨58015038808077859916629699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77353385077437146555506265 58015038808077859916629699)
      ·
        refine ⟨87022558212116789874944549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58015038808077859916629699 87022558212116789874944549)
        ·
          refine ⟨16316729664771898101552103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87022558212116789874944549 16316729664771898101552103)
          ·
            refine ⟨24475094497157847152328155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16316729664771898101552103 24475094497157847152328155)
            ·
              refine ⟨36712641745736770728492233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24475094497157847152328155 36712641745736770728492233)
              ·
                refine ⟨27534481309302578046369175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36712641745736770728492233 27534481309302578046369175)
                ·
                  refine ⟨41301721963953867069553763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27534481309302578046369175 41301721963953867069553763)
                  ·
                    refine ⟨61952582945930800604330645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41301721963953867069553763 61952582945930800604330645)
                    ·
                      refine ⟨2904027325590506278327999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61952582945930800604330645 2904027325590506278327999)
                      ·
                        rfl

theorem cell23_5655573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_5655573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655573 prefixEnd_5655573 := by exact prefixLift 5655573
  have htrace : WordTrace (prefixWord ++ tailWord_5655573) baseStart_5655573 baseEnd_5655573 := by
    simpa [prefixWord, tailWord_5655573, baseEnd_5655573] using wordTrace_append hprefix tailTrace_5655573
  have hstable : (prefixWord ++ tailWord_5655573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655573).length < 2 ^ (prefixWord ++ tailWord_5655573).sum := by decide
  have hdescent : baseEnd_5655573 < baseStart_5655573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655577 : List Nat := [1, 2, 1, 2, 1, 1, 7, 1, 3, 2, 2]
def baseStart_5655577 : Nat := 118140960795 + 5655577 * 2 ^ 59
def prefixEnd_5655577 : Nat := 4983230072969 + 3 ^ 40 * 5655577 * 2
def baseEnd_5655577 : Nat := 2904029379513124262677981

theorem tailTrace_5655577 : CollatzResearch.WordTrace tailWord_5655577 prefixEnd_5655577 2904029379513124262677981 := by
  unfold tailWord_5655577
  simp only [CollatzResearch.WordTrace]
  refine ⟨206275839431817899497828985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137517226287878599665219323 206275839431817899497828985)
  ·
    refine ⟨154706879573863424623371739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206275839431817899497828985 154706879573863424623371739)
    ·
      refine ⟨232060319360795136935057609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154706879573863424623371739 232060319360795136935057609)
      ·
        refine ⟨174045239520596352701293207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232060319360795136935057609 174045239520596352701293207)
        ·
          refine ⟨261067859280894529051939811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174045239520596352701293207 261067859280894529051939811)
          ·
            refine ⟨391601788921341793577909717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261067859280894529051939811 391601788921341793577909717)
            ·
              refine ⟨9178166927843948286982259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 391601788921341793577909717 9178166927843948286982259)
              ·
                refine ⟨13767250391765922430473389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9178166927843948286982259 13767250391765922430473389)
                ·
                  refine ⟨5162718896912220911427521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13767250391765922430473389 5162718896912220911427521)
                  ·
                    refine ⟨3872039172684165683570641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5162718896912220911427521 3872039172684165683570641)
                    ·
                      refine ⟨2904029379513124262677981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3872039172684165683570641 2904029379513124262677981)
                      ·
                        rfl

theorem cell23_5655577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 2, 2].length) (baseStart_5655577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655577 prefixEnd_5655577 := by exact prefixLift 5655577
  have htrace : WordTrace (prefixWord ++ tailWord_5655577) baseStart_5655577 baseEnd_5655577 := by
    simpa [prefixWord, tailWord_5655577, baseEnd_5655577] using wordTrace_append hprefix tailTrace_5655577
  have hstable : (prefixWord ++ tailWord_5655577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655577).length < 2 ^ (prefixWord ++ tailWord_5655577).sum := by decide
  have hdescent : baseEnd_5655577 < baseStart_5655577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655583 : List Nat := [1, 1, 2, 4, 1, 4, 2, 8]
def baseStart_5655583 : Nat := 118140960795 + 5655583 * 2 ^ 59
def prefixEnd_5655583 : Nat := 4983230072969 + 3 ^ 40 * 5655583 * 2
def baseEnd_5655583 : Nat := 107556757792483379229739

theorem tailTrace_5655583 : CollatzResearch.WordTrace tailWord_5655583 prefixEnd_5655583 107556757792483379229739 := by
  unfold tailWord_5655583
  simp only [CollatzResearch.WordTrace]
  refine ⟨206276058269796162522547403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137517372179864108348364935 206276058269796162522547403)
  ·
    refine ⟨309414087404694243783821105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206276058269796162522547403 309414087404694243783821105)
    ·
      refine ⟨232060565553520682837865829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309414087404694243783821105 232060565553520682837865829)
      ·
        refine ⟨43511356041285128032099843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232060565553520682837865829 43511356041285128032099843)
        ·
          refine ⟨65267034061927692048149765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43511356041285128032099843 65267034061927692048149765)
          ·
            refine ⟨12237568886611442259028081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65267034061927692048149765 12237568886611442259028081)
            ·
              refine ⟨9178176664958581694271061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12237568886611442259028081 9178176664958581694271061)
              ·
                refine ⟨107556757792483379229739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9178176664958581694271061 107556757792483379229739)
                ·
                  rfl

theorem cell23_5655583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 8].length) (baseStart_5655583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655583 prefixEnd_5655583 := by exact prefixLift 5655583
  have htrace : WordTrace (prefixWord ++ tailWord_5655583) baseStart_5655583 baseEnd_5655583 := by
    simpa [prefixWord, tailWord_5655583, baseEnd_5655583] using wordTrace_append hprefix tailTrace_5655583
  have hstable : (prefixWord ++ tailWord_5655583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655583).length < 2 ^ (prefixWord ++ tailWord_5655583).sum := by decide
  have hdescent : baseEnd_5655583 < baseStart_5655583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655587 : List Nat := [1, 1, 1, 4, 3, 2, 4, 1, 2, 4]
def baseStart_5655587 : Nat := 118140960795 + 5655587 * 2 ^ 59
def prefixEnd_5655587 : Nat := 4983230072969 + 3 ^ 40 * 5655587 * 2
def baseEnd_5655587 : Nat := 968011504773223074517645

theorem tailTrace_5655587 : CollatzResearch.WordTrace tailWord_5655587 prefixEnd_5655587 968011504773223074517645 := by
  unfold tailWord_5655587
  simp only [CollatzResearch.WordTrace]
  refine ⟨206276204161781671205693015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137517469441187780803795343 206276204161781671205693015)
  ·
    refine ⟨309414306242672506808539523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206276204161781671205693015 309414306242672506808539523)
    ·
      refine ⟨464121459364008760212809285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309414306242672506808539523 464121459364008760212809285)
      ·
        refine ⟨87022773630751642539901741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 464121459364008760212809285 87022773630751642539901741)
        ·
          refine ⟨32633540111531865952463153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87022773630751642539901741 32633540111531865952463153)
          ·
            refine ⟨24475155083648899464347365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32633540111531865952463153 24475155083648899464347365)
            ·
              refine ⟨4589091578184168649565131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24475155083648899464347365 4589091578184168649565131)
              ·
                refine ⟨6883637367276252974347697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4589091578184168649565131 6883637367276252974347697)
                ·
                  refine ⟨5162728025457189730760773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6883637367276252974347697 5162728025457189730760773)
                  ·
                    refine ⟨968011504773223074517645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5162728025457189730760773 968011504773223074517645)
                    ·
                      rfl

theorem cell23_5655587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 2, 4].length) (baseStart_5655587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655587 prefixEnd_5655587 := by exact prefixLift 5655587
  have htrace : WordTrace (prefixWord ++ tailWord_5655587) baseStart_5655587 baseEnd_5655587 := by
    simpa [prefixWord, tailWord_5655587, baseEnd_5655587] using wordTrace_append hprefix tailTrace_5655587
  have hstable : (prefixWord ++ tailWord_5655587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655587).length < 2 ^ (prefixWord ++ tailWord_5655587).sum := by decide
  have hdescent : baseEnd_5655587 < baseStart_5655587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655594 : List Nat := [3, 1, 4, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_5655594 : Nat := 118140960795 + 5655594 * 2 ^ 59
def prefixEnd_5655594 : Nat := 4983230072969 + 3 ^ 40 * 5655594 * 2
def baseEnd_5655594 : Nat := 2904038108684250696165403

theorem tailTrace_5655594 : CollatzResearch.WordTrace tailWord_5655594 prefixEnd_5655594 2904038108684250696165403 := by
  unfold tailWord_5655594
  simp only [CollatzResearch.WordTrace]
  refine ⟨51569114868189077850299459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137517639648504207600798557 51569114868189077850299459)
  ·
    refine ⟨77353672302283616775449189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51569114868189077850299459 77353672302283616775449189)
    ·
      refine ⟨14503813556678178145396723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77353672302283616775449189 14503813556678178145396723)
      ·
        refine ⟨21755720335017267218095085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14503813556678178145396723 21755720335017267218095085)
        ·
          refine ⟨8158395125631475206785657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21755720335017267218095085 8158395125631475206785657)
          ·
            refine ⟨6118796344223606405089243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8158395125631475206785657 6118796344223606405089243)
            ·
              refine ⟨9178194516335409607633865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6118796344223606405089243 9178194516335409607633865)
              ·
                refine ⟨6883645887251557205725399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9178194516335409607633865 6883645887251557205725399)
                ·
                  refine ⟨10325468830877335808588099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6883645887251557205725399 10325468830877335808588099)
                  ·
                    refine ⟨15488203246316003712882149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10325468830877335808588099 15488203246316003712882149)
                    ·
                      refine ⟨2904038108684250696165403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15488203246316003712882149 2904038108684250696165403)
                      ·
                        rfl

theorem cell23_5655594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_5655594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655594 prefixEnd_5655594 := by exact prefixLift 5655594
  have htrace : WordTrace (prefixWord ++ tailWord_5655594) baseStart_5655594 baseEnd_5655594 := by
    simpa [prefixWord, tailWord_5655594, baseEnd_5655594] using wordTrace_append hprefix tailTrace_5655594
  have hstable : (prefixWord ++ tailWord_5655594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655594).length < 2 ^ (prefixWord ++ tailWord_5655594).sum := by decide
  have hdescent : baseEnd_5655594 < baseStart_5655594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655610 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3]
def baseStart_5655610 : Nat := 118140960795 + 5655610 * 2 ^ 59
def prefixEnd_5655610 : Nat := 4983230072969 + 3 ^ 40 * 5655610 * 2
def baseEnd_5655610 : Nat := 2904046324374722633565329

theorem tailTrace_5655610 : CollatzResearch.WordTrace tailWord_5655610 prefixEnd_5655610 2904046324374722633565329 := by
  unfold tailWord_5655610
  simp only [CollatzResearch.WordTrace]
  refine ⟨51569260760174586533445071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137518028693798897422520189 51569260760174586533445071)
  ·
    refine ⟨77353891140261879800167607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51569260760174586533445071 77353891140261879800167607)
    ·
      refine ⟨116030836710392819700251411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77353891140261879800167607 116030836710392819700251411)
      ·
        refine ⟨174046255065589229550377117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116030836710392819700251411 174046255065589229550377117)
        ·
          refine ⟨65267345649595961081391419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174046255065589229550377117 65267345649595961081391419)
          ·
            refine ⟨97901018474393941622087129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65267345649595961081391419 97901018474393941622087129)
            ·
              refine ⟨73425763855795456216565347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97901018474393941622087129 73425763855795456216565347)
              ·
                refine ⟨110138645783693184324848021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73425763855795456216565347 110138645783693184324848021)
                ·
                  refine ⟨5162749021110618015227251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110138645783693184324848021 5162749021110618015227251)
                  ·
                    refine ⟨7744123531665927022840877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5162749021110618015227251 7744123531665927022840877)
                    ·
                      refine ⟨2904046324374722633565329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7744123531665927022840877 2904046324374722633565329)
                      ·
                        rfl

theorem cell23_5655610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3].length) (baseStart_5655610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655610 prefixEnd_5655610 := by exact prefixLift 5655610
  have htrace : WordTrace (prefixWord ++ tailWord_5655610) baseStart_5655610 baseEnd_5655610 := by
    simpa [prefixWord, tailWord_5655610, baseEnd_5655610] using wordTrace_append hprefix tailTrace_5655610
  have hstable : (prefixWord ++ tailWord_5655610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655610).length < 2 ^ (prefixWord ++ tailWord_5655610).sum := by decide
  have hdescent : baseEnd_5655610 < baseStart_5655610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655633 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 2, 3, 4]
def baseStart_5655633 : Nat := 118140960795 + 5655633 * 2 ^ 59
def prefixEnd_5655633 : Nat := 4983230072969 + 3 ^ 40 * 5655633 * 2
def baseEnd_5655633 : Nat := 2904058134429776043577723

theorem tailTrace_5655633 : CollatzResearch.WordTrace tailWord_5655633 prefixEnd_5655633 2904058134429776043577723 := by
  unfold tailWord_5655633
  simp only [CollatzResearch.WordTrace]
  refine ⟨206277881919615021061867553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137518587946410014041245035 206277881919615021061867553)
  ·
    refine ⟨154708411439711265796400665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206277881919615021061867553 154708411439711265796400665)
    ·
      refine ⟨116031308579783449347300499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154708411439711265796400665 116031308579783449347300499)
      ·
        refine ⟨174046962869675174020950749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116031308579783449347300499 174046962869675174020950749)
        ·
          refine ⟨65267611076128190257856531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174046962869675174020950749 65267611076128190257856531)
          ·
            refine ⟨97901416614192285386784797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65267611076128190257856531 97901416614192285386784797)
            ·
              refine ⟨36713031230322107020044299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97901416614192285386784797 36713031230322107020044299)
              ·
                refine ⟨55069546845483160530066449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36713031230322107020044299 55069546845483160530066449)
                ·
                  refine ⟨41302160134112370397549837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55069546845483160530066449 41302160134112370397549837)
                  ·
                    refine ⟨15488310050292138899081189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41302160134112370397549837 15488310050292138899081189)
                    ·
                      refine ⟨2904058134429776043577723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15488310050292138899081189 2904058134429776043577723)
                      ·
                        rfl

theorem cell23_5655633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_5655633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655633 prefixEnd_5655633 := by exact prefixLift 5655633
  have htrace : WordTrace (prefixWord ++ tailWord_5655633) baseStart_5655633 baseEnd_5655633 := by
    simpa [prefixWord, tailWord_5655633, baseEnd_5655633] using wordTrace_append hprefix tailTrace_5655633
  have hstable : (prefixWord ++ tailWord_5655633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655633).length < 2 ^ (prefixWord ++ tailWord_5655633).sum := by decide
  have hdescent : baseEnd_5655633 < baseStart_5655633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655663 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 4]
def baseStart_5655663 : Nat := 118140960795 + 5655663 * 2 ^ 59
def prefixEnd_5655663 : Nat := 4983230072969 + 3 ^ 40 * 5655663 * 2
def baseEnd_5655663 : Nat := 2904073538849410926202585

theorem tailTrace_5655663 : CollatzResearch.WordTrace tailWord_5655663 prefixEnd_5655663 2904073538849410926202585 := by
  unfold tailWord_5655663
  simp only [CollatzResearch.WordTrace]
  refine ⟨206278976109506336185459643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137519317406337557456973095 206278976109506336185459643)
  ·
    refine ⟨309418464164259504278189465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206278976109506336185459643 309418464164259504278189465)
    ·
      refine ⟨232063848123194628208642099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309418464164259504278189465 232063848123194628208642099)
      ·
        refine ⟨348095772184791942312963149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232063848123194628208642099 348095772184791942312963149)
        ·
          refine ⟨130535914569296978367361181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348095772184791942312963149 130535914569296978367361181)
          ·
            refine ⟨48950967963486366887760443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130535914569296978367361181 48950967963486366887760443)
            ·
              refine ⟨73426451945229550331640665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48950967963486366887760443 73426451945229550331640665)
              ·
                refine ⟨55069838958922162748730499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73426451945229550331640665 55069838958922162748730499)
                ·
                  refine ⟨82604758438383244123095749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55069838958922162748730499 82604758438383244123095749)
                  ·
                    refine ⟨15488392207196858273080453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82604758438383244123095749 15488392207196858273080453)
                    ·
                      refine ⟨2904073538849410926202585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15488392207196858273080453 2904073538849410926202585)
                      ·
                        rfl

theorem cell23_5655663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_5655663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655663 prefixEnd_5655663 := by exact prefixLift 5655663
  have htrace : WordTrace (prefixWord ++ tailWord_5655663) baseStart_5655663 baseEnd_5655663 := by
    simpa [prefixWord, tailWord_5655663, baseEnd_5655663] using wordTrace_append hprefix tailTrace_5655663
  have hstable : (prefixWord ++ tailWord_5655663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655663).length < 2 ^ (prefixWord ++ tailWord_5655663).sum := by decide
  have hdescent : baseEnd_5655663 < baseStart_5655663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655670 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_5655670 : Nat := 118140960795 + 5655670 * 2 ^ 59
def prefixEnd_5655670 : Nat := 4983230072969 + 3 ^ 40 * 5655670 * 2
def baseEnd_5655670 : Nat := 2904077133213992398815053

theorem tailTrace_5655670 : CollatzResearch.WordTrace tailWord_5655670 prefixEnd_5655670 2904077133213992398815053 := by
  unfold tailWord_5655670
  simp only [CollatzResearch.WordTrace]
  refine ⟨12892451963780061023810279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137519487613653984253976309 12892451963780061023810279)
  ·
    refine ⟨19338677945670091535715419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12892451963780061023810279 19338677945670091535715419)
    ·
      refine ⟨29008016918505137303573129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19338677945670091535715419 29008016918505137303573129)
      ·
        refine ⟨21756012688878852977679847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29008016918505137303573129 21756012688878852977679847)
        ·
          refine ⟨32634019033318279466519771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21756012688878852977679847 32634019033318279466519771)
          ·
            refine ⟨48951028549977419199779657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32634019033318279466519771 48951028549977419199779657)
            ·
              refine ⟨36713271412483064399834743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48951028549977419199779657 36713271412483064399834743)
              ·
                refine ⟨55069907118724596599752115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36713271412483064399834743 55069907118724596599752115)
                ·
                  refine ⟨82604860678086894899628173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55069907118724596599752115 82604860678086894899628173)
                  ·
                    refine ⟨30976822754282585587360565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82604860678086894899628173 30976822754282585587360565)
                    ·
                      refine ⟨2904077133213992398815053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30976822754282585587360565 2904077133213992398815053)
                      ·
                        rfl

theorem cell23_5655670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_5655670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655670 prefixEnd_5655670 := by exact prefixLift 5655670
  have htrace : WordTrace (prefixWord ++ tailWord_5655670) baseStart_5655670 baseEnd_5655670 := by
    simpa [prefixWord, tailWord_5655670, baseEnd_5655670] using wordTrace_append hprefix tailTrace_5655670
  have hstable : (prefixWord ++ tailWord_5655670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655670).length < 2 ^ (prefixWord ++ tailWord_5655670).sum := by decide
  have hdescent : baseEnd_5655670 < baseStart_5655670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655678 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_5655678 : Nat := 118140960795 + 5655678 * 2 ^ 59
def prefixEnd_5655678 : Nat := 4983230072969 + 3 ^ 40 * 5655678 * 2
def baseEnd_5655678 : Nat := 2904081241059228367515017

theorem tailTrace_5655678 : CollatzResearch.WordTrace tailWord_5655678 prefixEnd_5655678 2904081241059228367515017 := by
  unfold tailWord_5655678
  simp only [CollatzResearch.WordTrace]
  refine ⟨25784940400556499218406961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137519682136301329164837125 25784940400556499218406961)
  ·
    refine ⟨19338705300417374413805221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25784940400556499218406961 19338705300417374413805221)
    ·
      refine ⟨3626007243828257702588479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19338705300417374413805221 3626007243828257702588479)
      ·
        refine ⟨5439010865742386553882719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3626007243828257702588479 5439010865742386553882719)
        ·
          refine ⟨8158516298613579830824079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5439010865742386553882719 8158516298613579830824079)
          ·
            refine ⟨12237774447920369746236119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8158516298613579830824079 12237774447920369746236119)
            ·
              refine ⟨18356661671880554619354179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12237774447920369746236119 18356661671880554619354179)
              ·
                refine ⟨27534992507820831929031269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18356661671880554619354179 27534992507820831929031269)
                ·
                  refine ⟨5162811095216405986693363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27534992507820831929031269 5162811095216405986693363)
                  ·
                    refine ⟨7744216642824608980040045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5162811095216405986693363 7744216642824608980040045)
                    ·
                      refine ⟨2904081241059228367515017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7744216642824608980040045 2904081241059228367515017)
                      ·
                        rfl

theorem cell23_5655678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_5655678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655678 prefixEnd_5655678 := by exact prefixLift 5655678
  have htrace : WordTrace (prefixWord ++ tailWord_5655678) baseStart_5655678 baseEnd_5655678 := by
    simpa [prefixWord, tailWord_5655678, baseEnd_5655678] using wordTrace_append hprefix tailTrace_5655678
  have hstable : (prefixWord ++ tailWord_5655678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655678).length < 2 ^ (prefixWord ++ tailWord_5655678).sum := by decide
  have hdescent : baseEnd_5655678 < baseStart_5655678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655684 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 4, 2, 2]
def baseStart_5655684 : Nat := 118140960795 + 5655684 * 2 ^ 59
def prefixEnd_5655684 : Nat := 4983230072969 + 3 ^ 40 * 5655684 * 2
def baseEnd_5655684 : Nat := 2904084321943155344039989

theorem tailTrace_5655684 : CollatzResearch.WordTrace tailWord_5655684 prefixEnd_5655684 2904084321943155344039989 := by
  unfold tailWord_5655684
  simp only [CollatzResearch.WordTrace]
  refine ⟨103139871021215128385987053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137519828028286837847982737 103139871021215128385987053)
  ·
    refine ⟨38677451632955673144745145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103139871021215128385987053 38677451632955673144745145)
    ·
      refine ⟨29008088724716754858558859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38677451632955673144745145 29008088724716754858558859)
      ·
        refine ⟨43512133087075132287838289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29008088724716754858558859 43512133087075132287838289)
        ·
          refine ⟨32634099815306349215878717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43512133087075132287838289 32634099815306349215878717)
          ·
            refine ⟨12237787430739880955954519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32634099815306349215878717 12237787430739880955954519)
            ·
              refine ⟨18356681146109821433931779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12237787430739880955954519 18356681146109821433931779)
              ·
                refine ⟨27535021719164732150897669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18356681146109821433931779 27535021719164732150897669)
                ·
                  refine ⟨5162816572343387278293313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27535021719164732150897669 5162816572343387278293313)
                  ·
                    refine ⟨3872112429257540458719985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5162816572343387278293313 3872112429257540458719985)
                    ·
                      refine ⟨2904084321943155344039989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3872112429257540458719985 2904084321943155344039989)
                      ·
                        rfl

theorem cell23_5655684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_5655684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655684 prefixEnd_5655684 := by exact prefixLift 5655684
  have htrace : WordTrace (prefixWord ++ tailWord_5655684) baseStart_5655684 baseEnd_5655684 := by
    simpa [prefixWord, tailWord_5655684, baseEnd_5655684] using wordTrace_append hprefix tailTrace_5655684
  have hstable : (prefixWord ++ tailWord_5655684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655684).length < 2 ^ (prefixWord ++ tailWord_5655684).sum := by decide
  have hdescent : baseEnd_5655684 < baseStart_5655684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655690 : List Nat := [3, 1, 2, 3, 1, 1, 4, 1, 7]
def baseStart_5655690 : Nat := 118140960795 + 5655690 * 2 ^ 59
def prefixEnd_5655690 : Nat := 4983230072969 + 3 ^ 40 * 5655690 * 2
def baseEnd_5655690 : Nat := 322676378091898035618329

theorem tailTrace_5655690 : CollatzResearch.WordTrace tailWord_5655690 prefixEnd_5655690 322676378091898035618329 := by
  unfold tailWord_5655690
  simp only [CollatzResearch.WordTrace]
  refine ⟨51569990220102129949173131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137519973920272346531128349 51569990220102129949173131)
  ·
    refine ⟨77354985330153194923759697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51569990220102129949173131 77354985330153194923759697)
    ·
      refine ⟨58016238997614896192819773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77354985330153194923759697 58016238997614896192819773)
      ·
        refine ⟨21756089624105586072307415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58016238997614896192819773 21756089624105586072307415)
        ·
          refine ⟨32634134436158379108461123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21756089624105586072307415 32634134436158379108461123)
          ·
            refine ⟨48951201654237568662691685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32634134436158379108461123 48951201654237568662691685)
            ·
              refine ⟨9178350310169544124254691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48951201654237568662691685 9178350310169544124254691)
              ·
                refine ⟨13767525465254316186382037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9178350310169544124254691 13767525465254316186382037)
                ·
                  refine ⟨322676378091898035618329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13767525465254316186382037 322676378091898035618329)
                  ·
                    rfl

theorem cell23_5655690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 7].length) (baseStart_5655690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655690 prefixEnd_5655690 := by exact prefixLift 5655690
  have htrace : WordTrace (prefixWord ++ tailWord_5655690) baseStart_5655690 baseEnd_5655690 := by
    simpa [prefixWord, tailWord_5655690, baseEnd_5655690] using wordTrace_append hprefix tailTrace_5655690
  have hstable : (prefixWord ++ tailWord_5655690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655690).length < 2 ^ (prefixWord ++ tailWord_5655690).sum := by decide
  have hdescent : baseEnd_5655690 < baseStart_5655690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655753 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 3, 3, 6]
def baseStart_5655753 : Nat := 118140960795 + 5655753 * 2 ^ 59
def prefixEnd_5655753 : Nat := 4983230072969 + 3 ^ 40 * 5655753 * 2
def baseEnd_5655753 : Nat := 2904119752108315574077171

theorem tailTrace_5655753 : CollatzResearch.WordTrace tailWord_5655753 prefixEnd_5655753 2904119752108315574077171 := by
  unfold tailWord_5655753
  simp only [CollatzResearch.WordTrace]
  refine ⟨206282258679180281556235913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137521505786120187704157275 206282258679180281556235913)
  ·
    refine ⟨154711694009385211167176935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206282258679180281556235913 154711694009385211167176935)
    ·
      refine ⟨232067541014077816750765403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154711694009385211167176935 232067541014077816750765403)
      ·
        refine ⟨348101311521116725126148105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232067541014077816750765403 348101311521116725126148105)
        ·
          refine ⟨261075983640837543844611079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348101311521116725126148105 261075983640837543844611079)
          ·
            refine ⟨391613975461256315766916619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261075983640837543844611079 391613975461256315766916619)
            ·
              refine ⟨587420963191884473650374929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391613975461256315766916619 587420963191884473650374929)
              ·
                refine ⟨440565722393913355237781197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 587420963191884473650374929 440565722393913355237781197)
                ·
                  refine ⟨165212145897717508214167949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 440565722393913355237781197 165212145897717508214167949)
                  ·
                    refine ⟨61954554711644065580312981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165212145897717508214167949 61954554711644065580312981)
                    ·
                      refine ⟨2904119752108315574077171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61954554711644065580312981 2904119752108315574077171)
                      ·
                        rfl

theorem cell23_5655753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_5655753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655753 prefixEnd_5655753 := by exact prefixLift 5655753
  have htrace : WordTrace (prefixWord ++ tailWord_5655753) baseStart_5655753 baseEnd_5655753 := by
    simpa [prefixWord, tailWord_5655753, baseEnd_5655753] using wordTrace_append hprefix tailTrace_5655753
  have hstable : (prefixWord ++ tailWord_5655753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655753).length < 2 ^ (prefixWord ++ tailWord_5655753).sum := by decide
  have hdescent : baseEnd_5655753 < baseStart_5655753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655777 : List Nat := [1, 2, 3, 1, 3, 2, 1, 3, 2, 2, 3]
def baseStart_5655777 : Nat := 118140960795 + 5655777 * 2 ^ 59
def prefixEnd_5655777 : Nat := 4983230072969 + 3 ^ 40 * 5655777 * 2
def baseEnd_5655777 : Nat := 2904132075644023480177061

theorem tailTrace_5655777 : CollatzResearch.WordTrace tailWord_5655777 prefixEnd_5655777 2904132075644023480177061 := by
  unfold tailWord_5655777
  simp only [CollatzResearch.WordTrace]
  refine ⟨206283134031093333655109585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137522089354062222436739723 206283134031093333655109585)
  ·
    refine ⟨154712350523320000241332189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206283134031093333655109585 154712350523320000241332189)
    ·
      refine ⟨58017131446245000090499571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154712350523320000241332189 58017131446245000090499571)
      ·
        refine ⟨87025697169367500135749357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58017131446245000090499571 87025697169367500135749357)
        ·
          refine ⟨32634636438512812550906009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87025697169367500135749357 32634636438512812550906009)
          ·
            refine ⟨24475977328884609413179507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32634636438512812550906009 24475977328884609413179507)
            ·
              refine ⟨36713965993326914119769261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24475977328884609413179507 36713965993326914119769261)
              ·
                refine ⟨13767737247497592794913473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36713965993326914119769261 13767737247497592794913473)
                ·
                  refine ⟨10325802935623194596185105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13767737247497592794913473 10325802935623194596185105)
                  ·
                    refine ⟨7744352201717395947138829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10325802935623194596185105 7744352201717395947138829)
                    ·
                      refine ⟨2904132075644023480177061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7744352201717395947138829 2904132075644023480177061)
                      ·
                        rfl

theorem cell23_5655777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_5655777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655777 prefixEnd_5655777 := by exact prefixLift 5655777
  have htrace : WordTrace (prefixWord ++ tailWord_5655777) baseStart_5655777 baseEnd_5655777 := by
    simpa [prefixWord, tailWord_5655777, baseEnd_5655777] using wordTrace_append hprefix tailTrace_5655777
  have hstable : (prefixWord ++ tailWord_5655777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655777).length < 2 ^ (prefixWord ++ tailWord_5655777).sum := by decide
  have hdescent : baseEnd_5655777 < baseStart_5655777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655784 : List Nat := [2, 1, 4, 1, 2, 1, 2, 5, 1, 4]
def baseStart_5655784 : Nat := 118140960795 + 5655784 * 2 ^ 59
def prefixEnd_5655784 : Nat := 4983230072969 + 3 ^ 40 * 5655784 * 2
def baseEnd_5655784 : Nat := 968045223336201650929843

theorem tailTrace_5655784 : CollatzResearch.WordTrace tailWord_5655784 prefixEnd_5655784 968045223336201650929843 := by
  unfold tailWord_5655784
  simp only [CollatzResearch.WordTrace]
  refine ⟨103141694671033986925307203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137522259561378649233742937 103141694671033986925307203)
  ·
    refine ⟨154712542006550980387960805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103141694671033986925307203 154712542006550980387960805)
    ·
      refine ⟨29008601626228308822742651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154712542006550980387960805 29008601626228308822742651)
      ·
        refine ⟨43512902439342463234113977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29008601626228308822742651 43512902439342463234113977)
        ·
          refine ⟨32634676829506847425585483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43512902439342463234113977 32634676829506847425585483)
          ·
            refine ⟨48952015244260271138378225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32634676829506847425585483 48952015244260271138378225)
            ·
              refine ⟨36714011433195203353783669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48952015244260271138378225 36714011433195203353783669)
              ·
                refine ⟨3441938571862050314417219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36714011433195203353783669 3441938571862050314417219)
                ·
                  refine ⟨5162907857793075471625829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3441938571862050314417219 5162907857793075471625829)
                  ·
                    refine ⟨968045223336201650929843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5162907857793075471625829 968045223336201650929843)
                    ·
                      rfl

theorem cell23_5655784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_5655784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655784 prefixEnd_5655784 := by exact prefixLift 5655784
  have htrace : WordTrace (prefixWord ++ tailWord_5655784) baseStart_5655784 baseEnd_5655784 := by
    simpa [prefixWord, tailWord_5655784, baseEnd_5655784] using wordTrace_append hprefix tailTrace_5655784
  have hstable : (prefixWord ++ tailWord_5655784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655784).length < 2 ^ (prefixWord ++ tailWord_5655784).sum := by decide
  have hdescent : baseEnd_5655784 < baseStart_5655784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655817 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 1, 5, 2]
def baseStart_5655817 : Nat := 118140960795 + 5655817 * 2 ^ 59
def prefixEnd_5655817 : Nat := 4983230072969 + 3 ^ 40 * 5655817 * 2
def baseEnd_5655817 : Nat := 2904152614870203323676877

theorem tailTrace_5655817 : CollatzResearch.WordTrace tailWord_5655817 prefixEnd_5655817 2904152614870203323676877 := by
  unfold tailWord_5655817
  simp only [CollatzResearch.WordTrace]
  refine ⟨206284592950948420486565705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137523061967298946991043803 206284592950948420486565705)
  ·
    refine ⟨154713444713211315364924279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206284592950948420486565705 154713444713211315364924279)
    ·
      refine ⟨232070167069816973047386419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154713444713211315364924279 232070167069816973047386419)
      ·
        refine ⟨348105250604725459571079629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232070167069816973047386419 348105250604725459571079629)
        ·
          refine ⟨130539468976772047339154861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348105250604725459571079629 130539468976772047339154861)
          ·
            refine ⟨48952300866289517752183073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130539468976772047339154861 48952300866289517752183073)
            ·
              refine ⟨36714225649717138314137305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48952300866289517752183073 36714225649717138314137305)
              ·
                refine ⟨27535669237287853735602979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36714225649717138314137305 27535669237287853735602979)
                ·
                  refine ⟨41303503855931780603404469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27535669237287853735602979 41303503855931780603404469)
                  ·
                    refine ⟨3872203486493604431569169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41303503855931780603404469 3872203486493604431569169)
                    ·
                      refine ⟨2904152614870203323676877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3872203486493604431569169 2904152614870203323676877)
                      ·
                        rfl

theorem cell23_5655817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 5, 2].length) (baseStart_5655817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655817 prefixEnd_5655817 := by exact prefixLift 5655817
  have htrace : WordTrace (prefixWord ++ tailWord_5655817) baseStart_5655817 baseEnd_5655817 := by
    simpa [prefixWord, tailWord_5655817, baseEnd_5655817] using wordTrace_append hprefix tailTrace_5655817
  have hstable : (prefixWord ++ tailWord_5655817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655817).length < 2 ^ (prefixWord ++ tailWord_5655817).sum := by decide
  have hdescent : baseEnd_5655817 < baseStart_5655817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655834 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2]
def baseStart_5655834 : Nat := 118140960795 + 5655834 * 2 ^ 59
def prefixEnd_5655834 : Nat := 4983230072969 + 3 ^ 40 * 5655834 * 2
def baseEnd_5655834 : Nat := 2904161344041329757164299

theorem tailTrace_5655834 : CollatzResearch.WordTrace tailWord_5655834 prefixEnd_5655834 2904161344041329757164299 := by
  unfold tailWord_5655834
  simp only [CollatzResearch.WordTrace]
  refine ⟨51571303247971708097483639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137523475327924554926623037 51571303247971708097483639)
  ·
    refine ⟨77356954871957562146225459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51571303247971708097483639 77356954871957562146225459)
    ·
      refine ⟨116035432307936343219338189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77356954871957562146225459 116035432307936343219338189)
      ·
        refine ⟨43513287115476128707251821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116035432307936343219338189 43513287115476128707251821)
        ·
          refine ⟨16317482668303548265219433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43513287115476128707251821 16317482668303548265219433)
          ·
            refine ⟨12238112001227661198914575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16317482668303548265219433 12238112001227661198914575)
            ·
              refine ⟨18357168001841491798371863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12238112001227661198914575 18357168001841491798371863)
              ·
                refine ⟨27535752002762237697557795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18357168001841491798371863 27535752002762237697557795)
                ·
                  refine ⟨41303628004143356546336693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27535752002762237697557795 41303628004143356546336693)
                  ·
                    refine ⟨3872215125388439676219065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41303628004143356546336693 3872215125388439676219065)
                    ·
                      refine ⟨2904161344041329757164299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3872215125388439676219065 2904161344041329757164299)
                      ·
                        rfl

theorem cell23_5655834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_5655834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655834 prefixEnd_5655834 := by exact prefixLift 5655834
  have htrace : WordTrace (prefixWord ++ tailWord_5655834) baseStart_5655834 baseEnd_5655834 := by
    simpa [prefixWord, tailWord_5655834, baseEnd_5655834] using wordTrace_append hprefix tailTrace_5655834
  have hstable : (prefixWord ++ tailWord_5655834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655834).length < 2 ^ (prefixWord ++ tailWord_5655834).sum := by decide
  have hdescent : baseEnd_5655834 < baseStart_5655834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655884 : List Nat := [2, 2, 1, 3, 2, 2, 1, 4, 1, 2, 3]
def baseStart_5655884 : Nat := 118140960795 + 5655884 * 2 ^ 59
def prefixEnd_5655884 : Nat := 4983230072969 + 3 ^ 40 * 5655884 * 2
def baseEnd_5655884 : Nat := 2904187018074054561539069

theorem tailTrace_5655884 : CollatzResearch.WordTrace tailWord_5655884 prefixEnd_5655884 2904187018074054561539069 := by
  unfold tailWord_5655884
  simp only [CollatzResearch.WordTrace]
  refine ⟨103143518320852845464627353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137524691094470460619503137 103143518320852845464627353)
  ·
    refine ⟨77357638740639634098470515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103143518320852845464627353 77357638740639634098470515)
    ·
      refine ⟨116036458110959451147705773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77357638740639634098470515 116036458110959451147705773)
      ·
        refine ⟨43513671791609794180389665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116036458110959451147705773 43513671791609794180389665)
        ·
          refine ⟨32635253843707345635292249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43513671791609794180389665 32635253843707345635292249)
          ·
            refine ⟨24476440382780509226469187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32635253843707345635292249 24476440382780509226469187)
            ·
              refine ⟨36714660574170763839703781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24476440382780509226469187 36714660574170763839703781)
              ·
                refine ⟨6883998857657018219944459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36714660574170763839703781 6883998857657018219944459)
                ·
                  refine ⟨10325998286485527329916689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6883998857657018219944459 10325998286485527329916689)
                  ·
                    refine ⟨7744498714864145497437517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10325998286485527329916689 7744498714864145497437517)
                    ·
                      refine ⟨2904187018074054561539069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7744498714864145497437517 2904187018074054561539069)
                      ·
                        rfl

theorem cell23_5655884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_5655884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655884 prefixEnd_5655884 := by exact prefixLift 5655884
  have htrace : WordTrace (prefixWord ++ tailWord_5655884) baseStart_5655884 baseEnd_5655884 := by
    simpa [prefixWord, tailWord_5655884, baseEnd_5655884] using wordTrace_append hprefix tailTrace_5655884
  have hstable : (prefixWord ++ tailWord_5655884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655884).length < 2 ^ (prefixWord ++ tailWord_5655884).sum := by decide
  have hdescent : baseEnd_5655884 < baseStart_5655884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655897 : List Nat := [1, 2, 1, 2, 2, 2, 2, 4, 1, 3, 3]
def baseStart_5655897 : Nat := 118140960795 + 5655897 * 2 ^ 59
def prefixEnd_5655897 : Nat := 4983230072969 + 3 ^ 40 * 5655897 * 2
def baseEnd_5655897 : Nat := 2904193693322563010676509

theorem tailTrace_5655897 : CollatzResearch.WordTrace tailWord_5655897 prefixEnd_5655897 2904193693322563010676509 := by
  unfold tailWord_5655897
  simp only [CollatzResearch.WordTrace]
  refine ⟨206287510790658594149477945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137525007193772396099651963 206287510790658594149477945)
  ·
    refine ⟨154715633092993945612108459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206287510790658594149477945 154715633092993945612108459)
    ·
      refine ⟨232073449639490918418162689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154715633092993945612108459 232073449639490918418162689)
      ·
        refine ⟨174055087229618188813622017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232073449639490918418162689 174055087229618188813622017)
        ·
          refine ⟨130541315422213641610216513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174055087229618188813622017 130541315422213641610216513)
          ·
            refine ⟨97905986566660231207662385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130541315422213641610216513 97905986566660231207662385)
            ·
              refine ⟨73429489924995173405746789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97905986566660231207662385 73429489924995173405746789)
              ·
                refine ⟨13768029360936595013577523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73429489924995173405746789 13768029360936595013577523)
                ·
                  refine ⟨20652044041404892520366285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13768029360936595013577523 20652044041404892520366285)
                  ·
                    refine ⟨7744516515526834695137357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20652044041404892520366285 7744516515526834695137357)
                    ·
                      refine ⟨2904193693322563010676509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7744516515526834695137357 2904193693322563010676509)
                      ·
                        rfl

theorem cell23_5655897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_5655897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655897 prefixEnd_5655897 := by exact prefixLift 5655897
  have htrace : WordTrace (prefixWord ++ tailWord_5655897) baseStart_5655897 baseEnd_5655897 := by
    simpa [prefixWord, tailWord_5655897, baseEnd_5655897] using wordTrace_append hprefix tailTrace_5655897
  have hstable : (prefixWord ++ tailWord_5655897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655897).length < 2 ^ (prefixWord ++ tailWord_5655897).sum := by decide
  have hdescent : baseEnd_5655897 < baseStart_5655897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655898 : List Nat := [3, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2]
def baseStart_5655898 : Nat := 118140960795 + 5655898 * 2 ^ 59
def prefixEnd_5655898 : Nat := 4983230072969 + 3 ^ 40 * 5655898 * 2
def baseEnd_5655898 : Nat := 2904194206803217506764005

theorem tailTrace_5655898 : CollatzResearch.WordTrace tailWord_5655898 prefixEnd_5655898 2904194206803217506764005 := by
  unfold tailWord_5655898
  simp only [CollatzResearch.WordTrace]
  refine ⟨51571886815913742830066087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137525031509103314213509565 51571886815913742830066087)
  ·
    refine ⟨77357830223870614245099131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51571886815913742830066087 77357830223870614245099131)
    ·
      refine ⟨116036745335805921367648697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77357830223870614245099131 116036745335805921367648697)
      ·
        refine ⟨87027559001854441025736523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116036745335805921367648697 87027559001854441025736523)
        ·
          refine ⟨130541338502781661538604785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87027559001854441025736523 130541338502781661538604785)
          ·
            refine ⟨97906003877086246153953589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130541338502781661538604785 97906003877086246153953589)
            ·
              refine ⟨9178687863476835576933149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97906003877086246153953589 9178687863476835576933149)
              ·
                refine ⟨3442007948803813341349931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9178687863476835576933149 3442007948803813341349931)
                ·
                  refine ⟨5163011923205720012024897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3442007948803813341349931 5163011923205720012024897)
                  ·
                    refine ⟨3872258942404290009018673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5163011923205720012024897 3872258942404290009018673)
                    ·
                      refine ⟨2904194206803217506764005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3872258942404290009018673 2904194206803217506764005)
                      ·
                        rfl

theorem cell23_5655898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_5655898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655898 prefixEnd_5655898 := by exact prefixLift 5655898
  have htrace : WordTrace (prefixWord ++ tailWord_5655898) baseStart_5655898 baseEnd_5655898 := by
    simpa [prefixWord, tailWord_5655898, baseEnd_5655898] using wordTrace_append hprefix tailTrace_5655898
  have hstable : (prefixWord ++ tailWord_5655898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655898).length < 2 ^ (prefixWord ++ tailWord_5655898).sum := by decide
  have hdescent : baseEnd_5655898 < baseStart_5655898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655925 : List Nat := [1, 3, 4, 1, 4, 1, 2, 1, 2, 4]
def baseStart_5655925 : Nat := 118140960795 + 5655925 * 2 ^ 59
def prefixEnd_5655925 : Nat := 4983230072969 + 3 ^ 40 * 5655925 * 2
def baseEnd_5655925 : Nat := 968069356926962967042127

theorem tailTrace_5655925 : CollatzResearch.WordTrace tailWord_5655925 prefixEnd_5655925 968069356926962967042127 := by
  unfold tailWord_5655925
  simp only [CollatzResearch.WordTrace]
  refine ⟨206288532034557154931497229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137525688023038103287664819 206288532034557154931497229)
  ·
    refine ⟨77358199512958933099311461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206288532034557154931497229 77358199512958933099311461)
    ·
      refine ⟨14504662408679799956120899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77358199512958933099311461 14504662408679799956120899)
      ·
        refine ⟨21756993613019699934181349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14504662408679799956120899 21756993613019699934181349)
        ·
          refine ⟨4079436302441193737659003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21756993613019699934181349 4079436302441193737659003)
          ·
            refine ⟨6119154453661790606488505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4079436302441193737659003 6119154453661790606488505)
            ·
              refine ⟨4589365840246342954866379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6119154453661790606488505 4589365840246342954866379)
              ·
                refine ⟨6884048760369514432299569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4589365840246342954866379 6884048760369514432299569)
                ·
                  refine ⟨5163036570277135824224677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6884048760369514432299569 5163036570277135824224677)
                  ·
                    refine ⟨968069356926962967042127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5163036570277135824224677 968069356926962967042127)
                    ·
                      rfl

theorem cell23_5655925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_5655925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655925 prefixEnd_5655925 := by exact prefixLift 5655925
  have htrace : WordTrace (prefixWord ++ tailWord_5655925) baseStart_5655925 baseEnd_5655925 := by
    simpa [prefixWord, tailWord_5655925, baseEnd_5655925] using wordTrace_append hprefix tailTrace_5655925
  have hstable : (prefixWord ++ tailWord_5655925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655925).length < 2 ^ (prefixWord ++ tailWord_5655925).sum := by decide
  have hdescent : baseEnd_5655925 < baseStart_5655925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655941 : List Nat := [1, 3, 1, 1, 3, 1, 5, 2, 1, 3, 2]
def baseStart_5655941 : Nat := 118140960795 + 5655941 * 2 ^ 59
def prefixEnd_5655941 : Nat := 4983230072969 + 3 ^ 40 * 5655941 * 2
def baseEnd_5655941 : Nat := 2904216286471360838526307

theorem tailTrace_5655941 : CollatzResearch.WordTrace tailWord_5655941 prefixEnd_5655941 2904216286471360838526307 := by
  unfold tailWord_5655941
  simp only [CollatzResearch.WordTrace]
  refine ⟨206289115602499189664079677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137526077068332793109386451 206289115602499189664079677)
  ·
    refine ⟨77358418350937196124029879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206289115602499189664079677 77358418350937196124029879)
    ·
      refine ⟨116037627526405794186044819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77358418350937196124029879 116037627526405794186044819)
      ·
        refine ⟨174056441289608691279067229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116037627526405794186044819 174056441289608691279067229)
        ·
          refine ⟨65271165483603259229650211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174056441289608691279067229 65271165483603259229650211)
          ·
            refine ⟨97906748225404888844475317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65271165483603259229650211 97906748225404888844475317)
            ·
              refine ⟨9178757646131708329169561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97906748225404888844475317 9178757646131708329169561)
              ·
                refine ⟨6884068234598781246877171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9178757646131708329169561 6884068234598781246877171)
                ·
                  refine ⟨10326102351898171870315757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6884068234598781246877171 10326102351898171870315757)
                  ·
                    refine ⟨3872288381961814451368409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10326102351898171870315757 3872288381961814451368409)
                    ·
                      refine ⟨2904216286471360838526307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3872288381961814451368409 2904216286471360838526307)
                      ·
                        rfl

theorem cell23_5655941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 3, 2].length) (baseStart_5655941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655941 prefixEnd_5655941 := by exact prefixLift 5655941
  have htrace : WordTrace (prefixWord ++ tailWord_5655941) baseStart_5655941 baseEnd_5655941 := by
    simpa [prefixWord, tailWord_5655941, baseEnd_5655941] using wordTrace_append hprefix tailTrace_5655941
  have hstable : (prefixWord ++ tailWord_5655941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655941).length < 2 ^ (prefixWord ++ tailWord_5655941).sum := by decide
  have hdescent : baseEnd_5655941 < baseStart_5655941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655957 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_5655957 : Nat := 118140960795 + 5655957 * 2 ^ 59
def prefixEnd_5655957 : Nat := 4983230072969 + 3 ^ 40 * 5655957 * 2
def baseEnd_5655957 : Nat := 2904224502161832775926233

theorem tailTrace_5655957 : CollatzResearch.WordTrace tailWord_5655957 prefixEnd_5655957 2904224502161832775926233 := by
  unfold tailWord_5655957
  simp only [CollatzResearch.WordTrace]
  refine ⟨206289699170441224396662125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137526466113627482931108083 206289699170441224396662125)
  ·
    refine ⟨77358637188915459148748297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206289699170441224396662125 77358637188915459148748297)
    ·
      refine ⟨58018977891686594361561223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77358637188915459148748297 58018977891686594361561223)
      ·
        refine ⟨87028466837529891542341835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58018977891686594361561223 87028466837529891542341835)
        ·
          refine ⟨130542700256294837313512753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87028466837529891542341835 130542700256294837313512753)
          ·
            refine ⟨97907025192221127985134565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130542700256294837313512753 97907025192221127985134565)
            ·
              refine ⟨18357567223541461497212731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97907025192221127985134565 18357567223541461497212731)
              ·
                refine ⟨27536350835312192245819097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18357567223541461497212731 27536350835312192245819097)
                ·
                  refine ⟨20652263126484144184364323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27536350835312192245819097 20652263126484144184364323)
                  ·
                    refine ⟨30978394689726216276546485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20652263126484144184364323 30978394689726216276546485)
                    ·
                      refine ⟨2904224502161832775926233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30978394689726216276546485 2904224502161832775926233)
                      ·
                        rfl

theorem cell23_5655957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_5655957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655957 prefixEnd_5655957 := by exact prefixLift 5655957
  have htrace : WordTrace (prefixWord ++ tailWord_5655957) baseStart_5655957 baseEnd_5655957 := by
    simpa [prefixWord, tailWord_5655957, baseEnd_5655957] using wordTrace_append hprefix tailTrace_5655957
  have hstable : (prefixWord ++ tailWord_5655957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655957).length < 2 ^ (prefixWord ++ tailWord_5655957).sum := by decide
  have hdescent : baseEnd_5655957 < baseStart_5655957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5655966 : List Nat := [4, 3, 1, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_5655966 : Nat := 118140960795 + 5655966 * 2 ^ 59
def prefixEnd_5655966 : Nat := 4983230072969 + 3 ^ 40 * 5655966 * 2
def baseEnd_5655966 : Nat := 2904229123487723240713693

theorem tailTrace_5655966 : CollatzResearch.WordTrace tailWord_5655966 prefixEnd_5655966 2904229123487723240713693 := by
  unfold tailWord_5655966
  simp only [CollatzResearch.WordTrace]
  refine ⟨25786253428426077366717469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137526684951605745955826501 25786253428426077366717469)
  ·
    refine ⟨9669845035659779012519051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25786253428426077366717469 9669845035659779012519051)
    ·
      refine ⟨14504767553489668518778577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9669845035659779012519051 14504767553489668518778577)
      ·
        refine ⟨10878575665117251389083933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14504767553489668518778577 10878575665117251389083933)
        ·
          refine ⟨4079465874418969270906475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10878575665117251389083933 4079465874418969270906475)
          ·
            refine ⟨6119198811628453906359713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4079465874418969270906475 6119198811628453906359713)
            ·
              refine ⟨4589399108721340429769785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6119198811628453906359713 4589399108721340429769785)
              ·
                refine ⟨3442049331541005322327339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4589399108721340429769785 3442049331541005322327339)
                ·
                  refine ⟨5163073997311507983491009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3442049331541005322327339 5163073997311507983491009)
                  ·
                    refine ⟨3872305497983630987618257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5163073997311507983491009 3872305497983630987618257)
                    ·
                      refine ⟨2904229123487723240713693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3872305497983630987618257 2904229123487723240713693)
                      ·
                        rfl

theorem cell23_5655966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_5655966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5655966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5655966 prefixEnd_5655966 := by exact prefixLift 5655966
  have htrace : WordTrace (prefixWord ++ tailWord_5655966) baseStart_5655966 baseEnd_5655966 := by
    simpa [prefixWord, tailWord_5655966, baseEnd_5655966] using wordTrace_append hprefix tailTrace_5655966
  have hstable : (prefixWord ++ tailWord_5655966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5655966).length < 2 ^ (prefixWord ++ tailWord_5655966).sum := by decide
  have hdescent : baseEnd_5655966 < baseStart_5655966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5655966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656007 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 1, 7]
def baseStart_5656007 : Nat := 118140960795 + 5656007 * 2 ^ 59
def prefixEnd_5656007 : Nat := 4983230072969 + 3 ^ 40 * 5656007 * 2
def baseEnd_5656007 : Nat := 968083392064852526767001

theorem tailTrace_5656007 : CollatzResearch.WordTrace tailWord_5656007 prefixEnd_5656007 968083392064852526767001 := by
  unfold tailWord_5656007
  simp only [CollatzResearch.WordTrace]
  refine ⟨206291522820260082935982275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137527681880173388623988183 206291522820260082935982275)
  ·
    refine ⟨309437284230390124403973413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206291522820260082935982275 309437284230390124403973413)
    ·
      refine ⟨58019490793198148325745015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 309437284230390124403973413 58019490793198148325745015)
      ·
        refine ⟨87029236189797222488617523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58019490793198148325745015 87029236189797222488617523)
        ·
          refine ⟨130543854284695833732926285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87029236189797222488617523 130543854284695833732926285)
          ·
            refine ⟨48953945356760937649847357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130543854284695833732926285 48953945356760937649847357)
            ·
              refine ⟨18357729508785351618692759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48953945356760937649847357 18357729508785351618692759)
              ·
                refine ⟨27536594263178027428039139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18357729508785351618692759 27536594263178027428039139)
                ·
                  refine ⟨41304891394767041142058709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27536594263178027428039139 41304891394767041142058709)
                  ·
                    refine ⟨968083392064852526767001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41304891394767041142058709 968083392064852526767001)
                    ·
                      rfl

theorem cell23_5656007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_5656007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656007 prefixEnd_5656007 := by exact prefixLift 5656007
  have htrace : WordTrace (prefixWord ++ tailWord_5656007) baseStart_5656007 baseEnd_5656007 := by
    simpa [prefixWord, tailWord_5656007, baseEnd_5656007] using wordTrace_append hprefix tailTrace_5656007
  have hstable : (prefixWord ++ tailWord_5656007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656007).length < 2 ^ (prefixWord ++ tailWord_5656007).sum := by decide
  have hdescent : baseEnd_5656007 < baseStart_5656007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656022 : List Nat := [5, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_5656022 : Nat := 118140960795 + 5656022 * 2 ^ 59
def prefixEnd_5656022 : Nat := 4983230072969 + 3 ^ 40 * 5656022 * 2
def baseEnd_5656022 : Nat := 2904257878404375021613435

theorem tailTrace_5656022 : CollatzResearch.WordTrace tailWord_5656022 prefixEnd_5656022 2904257878404375021613435 := by
  unfold tailWord_5656022
  simp only [CollatzResearch.WordTrace]
  refine ⟨12893254369700358781111145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137528046610137160331852213 12893254369700358781111145)
  ·
    refine ⟨9669940777275269085833359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12893254369700358781111145 9669940777275269085833359)
    ·
      refine ⟨14504911165912903628750039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9669940777275269085833359 14504911165912903628750039)
      ·
        refine ⟨21757366748869355443125059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14504911165912903628750039 21757366748869355443125059)
        ·
          refine ⟨32636050123304033164687589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21757366748869355443125059 32636050123304033164687589)
          ·
            refine ⟨6119259398119506218378923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32636050123304033164687589 6119259398119506218378923)
            ·
              refine ⟨9178889097179259327568385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6119259398119506218378923 9178889097179259327568385)
              ·
                refine ⟨6884166822884444495676289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9178889097179259327568385 6884166822884444495676289)
                ·
                  refine ⟨5163125117163333371757217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6884166822884444495676289 5163125117163333371757217)
                  ·
                    refine ⟨3872343837872500028817913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5163125117163333371757217 3872343837872500028817913)
                    ·
                      refine ⟨2904257878404375021613435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3872343837872500028817913 2904257878404375021613435)
                      ·
                        rfl

theorem cell23_5656022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_5656022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656022 prefixEnd_5656022 := by exact prefixLift 5656022
  have htrace : WordTrace (prefixWord ++ tailWord_5656022) baseStart_5656022 baseEnd_5656022 := by
    simpa [prefixWord, tailWord_5656022, baseEnd_5656022] using wordTrace_append hprefix tailTrace_5656022
  have hstable : (prefixWord ++ tailWord_5656022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656022).length < 2 ^ (prefixWord ++ tailWord_5656022).sum := by decide
  have hdescent : baseEnd_5656022 < baseStart_5656022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656044 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 1, 6, 2]
def baseStart_5656044 : Nat := 118140960795 + 5656044 * 2 ^ 59
def prefixEnd_5656044 : Nat := 4983230072969 + 3 ^ 40 * 5656044 * 2
def baseEnd_5656044 : Nat := 2904269174978773935538333

theorem tailTrace_5656044 : CollatzResearch.WordTrace tailWord_5656044 prefixEnd_5656044 2904269174978773935538333 := by
  unfold tailWord_5656044
  simp only [CollatzResearch.WordTrace]
  refine ⟨103146436160563019127539593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137528581547417358836719457 103146436160563019127539593)
  ·
    refine ⟨77359827120422264345654695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103146436160563019127539593 77359827120422264345654695)
    ·
      refine ⟨116039740680633396518482043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77359827120422264345654695 116039740680633396518482043)
      ·
        refine ⟨174059611020950094777723065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116039740680633396518482043 174059611020950094777723065)
        ·
          refine ⟨130544708265712571083292299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174059611020950094777723065 130544708265712571083292299)
          ·
            refine ⟨195817062398568856624938449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130544708265712571083292299 195817062398568856624938449)
            ·
              refine ⟨146862796798926642468703837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195817062398568856624938449 146862796798926642468703837)
              ·
                refine ⟨55073548799597490925763939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146862796798926642468703837 55073548799597490925763939)
                ·
                  refine ⟨82610323199396236388645909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55073548799597490925763939 82610323199396236388645909)
                  ·
                    refine ⟨3872358899971698580717777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82610323199396236388645909 3872358899971698580717777)
                    ·
                      refine ⟨2904269174978773935538333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3872358899971698580717777 2904269174978773935538333)
                      ·
                        rfl

theorem cell23_5656044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 6, 2].length) (baseStart_5656044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656044 prefixEnd_5656044 := by exact prefixLift 5656044
  have htrace : WordTrace (prefixWord ++ tailWord_5656044) baseStart_5656044 baseEnd_5656044 := by
    simpa [prefixWord, tailWord_5656044, baseEnd_5656044] using wordTrace_append hprefix tailTrace_5656044
  have hstable : (prefixWord ++ tailWord_5656044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656044).length < 2 ^ (prefixWord ++ tailWord_5656044).sum := by decide
  have hdescent : baseEnd_5656044 < baseStart_5656044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656057 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 1, 6, 4]
def baseStart_5656057 : Nat := 118140960795 + 5656057 * 2 ^ 59
def prefixEnd_5656057 : Nat := 4983230072969 + 3 ^ 40 * 5656057 * 2
def baseEnd_5656057 : Nat := 2904275850227282384675773

theorem tailTrace_5656057 : CollatzResearch.WordTrace tailWord_5656057 prefixEnd_5656057 2904275850227282384675773 := by
  unfold tailWord_5656057
  simp only [CollatzResearch.WordTrace]
  refine ⟨206293346470078941475302425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137528897646719294316868283 206293346470078941475302425)
  ·
    refine ⟨154720009852559206106476819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206293346470078941475302425 154720009852559206106476819)
    ·
      refine ⟨232080014778838809159715229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154720009852559206106476819 232080014778838809159715229)
      ·
        refine ⟨87030005542064553434893211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232080014778838809159715229 87030005542064553434893211)
        ·
          refine ⟨130545008313096830152339817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87030005542064553434893211 130545008313096830152339817)
          ·
            refine ⟨97908756234822622614254863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130545008313096830152339817 97908756234822622614254863)
            ·
              refine ⟨146863134352233933921382295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97908756234822622614254863 146863134352233933921382295)
              ·
                refine ⟨220294701528350900882073443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146863134352233933921382295 220294701528350900882073443)
                ·
                  refine ⟨330442052292526351323110165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220294701528350900882073443 330442052292526351323110165)
                  ·
                    refine ⟨15489471201212172718270789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 330442052292526351323110165 15489471201212172718270789)
                    ·
                      refine ⟨2904275850227282384675773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15489471201212172718270789 2904275850227282384675773)
                      ·
                        rfl

theorem cell23_5656057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_5656057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656057 prefixEnd_5656057 := by exact prefixLift 5656057
  have htrace : WordTrace (prefixWord ++ tailWord_5656057) baseStart_5656057 baseEnd_5656057 := by
    simpa [prefixWord, tailWord_5656057, baseEnd_5656057] using wordTrace_append hprefix tailTrace_5656057
  have hstable : (prefixWord ++ tailWord_5656057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656057).length < 2 ^ (prefixWord ++ tailWord_5656057).sum := by decide
  have hdescent : baseEnd_5656057 < baseStart_5656057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656062 : List Nat := [4, 2, 2, 3, 2, 1, 1, 3, 5]
def baseStart_5656062 : Nat := 118140960795 + 5656062 * 2 ^ 59
def prefixEnd_5656062 : Nat := 4983230072969 + 3 ^ 40 * 5656062 * 2
def baseEnd_5656062 : Nat := 322697601958950540568139

theorem tailTrace_5656062 : CollatzResearch.WordTrace tailWord_5656062 prefixEnd_5656062 322697601958950540568139 := by
  unfold tailWord_5656062
  simp only [CollatzResearch.WordTrace]
  refine ⟨25786691104382603416154305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137529019223373884886156293 25786691104382603416154305)
  ·
    refine ⟨19340018328286952562115729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25786691104382603416154305 19340018328286952562115729)
    ·
      refine ⟨14505013746215214421586797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19340018328286952562115729 14505013746215214421586797)
      ·
        refine ⟨5439380154830705408095049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14505013746215214421586797 5439380154830705408095049)
        ·
          refine ⟨4079535116123029056071287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5439380154830705408095049 4079535116123029056071287)
          ·
            refine ⟨6119302674184543584106931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4079535116123029056071287 6119302674184543584106931)
            ·
              refine ⟨9178954011276815376160397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6119302674184543584106931 9178954011276815376160397)
              ·
                refine ⟨3442107754228805766060149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9178954011276815376160397 3442107754228805766060149)
                ·
                  refine ⟨322697601958950540568139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3442107754228805766060149 322697601958950540568139)
                  ·
                    rfl

theorem cell23_5656062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_5656062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656062 prefixEnd_5656062 := by exact prefixLift 5656062
  have htrace : WordTrace (prefixWord ++ tailWord_5656062) baseStart_5656062 baseEnd_5656062 := by
    simpa [prefixWord, tailWord_5656062, baseEnd_5656062] using wordTrace_append hprefix tailTrace_5656062
  have hstable : (prefixWord ++ tailWord_5656062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656062).length < 2 ^ (prefixWord ++ tailWord_5656062).sum := by decide
  have hdescent : baseEnd_5656062 < baseStart_5656062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656088 : List Nat := [2, 1, 2, 3, 4, 2, 1, 1, 3, 4]
def baseStart_5656088 : Nat := 118140960795 + 5656088 * 2 ^ 59
def prefixEnd_5656088 : Nat := 4983230072969 + 3 ^ 40 * 5656088 * 2
def baseEnd_5656088 : Nat := 968097256042523921129377

theorem tailTrace_5656088 : CollatzResearch.WordTrace tailWord_5656088 prefixEnd_5656088 968097256042523921129377 := by
  unfold tailWord_5656088
  simp only [CollatzResearch.WordTrace]
  refine ⟨103147238566483316884840459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137529651421977755846453945 103147238566483316884840459)
  ·
    refine ⟨154720857849724975327260689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103147238566483316884840459 154720857849724975327260689)
    ·
      refine ⟨116040643387293731495445517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154720857849724975327260689 116040643387293731495445517)
      ·
        refine ⟨43515241270235149310792069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116040643387293731495445517 43515241270235149310792069)
        ·
          refine ⟨8159107738169090495773513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43515241270235149310792069 8159107738169090495773513)
          ·
            refine ⟨6119330803626817871830135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8159107738169090495773513 6119330803626817871830135)
            ·
              refine ⟨9178996205440226807745203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6119330803626817871830135 9178996205440226807745203)
              ·
                refine ⟨13768494308160340211617805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9178996205440226807745203 13768494308160340211617805)
                ·
                  refine ⟨5163185365560127579356677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13768494308160340211617805 5163185365560127579356677)
                  ·
                    refine ⟨968097256042523921129377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5163185365560127579356677 968097256042523921129377)
                    ·
                      rfl

theorem cell23_5656088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_5656088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656088 prefixEnd_5656088 := by exact prefixLift 5656088
  have htrace : WordTrace (prefixWord ++ tailWord_5656088) baseStart_5656088 baseEnd_5656088 := by
    simpa [prefixWord, tailWord_5656088, baseEnd_5656088] using wordTrace_append hprefix tailTrace_5656088
  have hstable : (prefixWord ++ tailWord_5656088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656088).length < 2 ^ (prefixWord ++ tailWord_5656088).sum := by decide
  have hdescent : baseEnd_5656088 < baseStart_5656088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656128 : List Nat := [2, 1, 1, 2, 2, 2, 1, 7, 1, 1, 3]
def baseStart_5656128 : Nat := 118140960795 + 5656128 * 2 ^ 59
def prefixEnd_5656128 : Nat := 4983230072969 + 3 ^ 40 * 5656128 * 2
def baseEnd_5656128 : Nat := 2904312307353751606887947

theorem tailTrace_5656128 : CollatzResearch.WordTrace tailWord_5656128 prefixEnd_5656128 2904312307353751606887947 := by
  unfold tailWord_5656128
  simp only [CollatzResearch.WordTrace]
  refine ⟨103147968026410860300568519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137530624035214480400758025 103147968026410860300568519)
  ·
    refine ⟨154721952039616290450852779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103147968026410860300568519 154721952039616290450852779)
    ·
      refine ⟨232082928059424435676279169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154721952039616290450852779 232082928059424435676279169)
      ·
        refine ⟨174062196044568326757209377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232082928059424435676279169 174062196044568326757209377)
        ·
          refine ⟨130546647033426245067907033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174062196044568326757209377 130546647033426245067907033)
          ·
            refine ⟨97909985275069683800930275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130546647033426245067907033 97909985275069683800930275)
            ·
              refine ⟨146864977912604525701395413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97909985275069683800930275 146864977912604525701395413)
              ·
                refine ⟨3442147919826668571126455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 146864977912604525701395413 3442147919826668571126455)
                ·
                  refine ⟨5163221879740002856689683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3442147919826668571126455 5163221879740002856689683)
                  ·
                    refine ⟨7744832819610004285034525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5163221879740002856689683 7744832819610004285034525)
                    ·
                      refine ⟨2904312307353751606887947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7744832819610004285034525 2904312307353751606887947)
                      ·
                        rfl

theorem cell23_5656128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 1, 1, 3].length) (baseStart_5656128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656128 prefixEnd_5656128 := by exact prefixLift 5656128
  have htrace : WordTrace (prefixWord ++ tailWord_5656128) baseStart_5656128 baseEnd_5656128 := by
    simpa [prefixWord, tailWord_5656128, baseEnd_5656128] using wordTrace_append hprefix tailTrace_5656128
  have hstable : (prefixWord ++ tailWord_5656128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656128).length < 2 ^ (prefixWord ++ tailWord_5656128).sum := by decide
  have hdescent : baseEnd_5656128 < baseStart_5656128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656154 : List Nat := [3, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5]
def baseStart_5656154 : Nat := 118140960795 + 5656154 * 2 ^ 59
def prefixEnd_5656154 : Nat := 4983230072969 + 3 ^ 40 * 5656154 * 2
def baseEnd_5656154 : Nat := 2904325657850768505162827

theorem tailTrace_5656154 : CollatzResearch.WordTrace tailWord_5656154 prefixEnd_5656154 2904325657850768505162827 := by
  unfold tailWord_5656154
  simp only [CollatzResearch.WordTrace]
  refine ⟨51574221087681881760395879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137531256233818351361055677 51574221087681881760395879)
  ·
    refine ⟨77361331631522822640593819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51574221087681881760395879 77361331631522822640593819)
    ·
      refine ⟨116041997447284233960890729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77361331631522822640593819 116041997447284233960890729)
      ·
        refine ⟨87031498085463175470668047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116041997447284233960890729 87031498085463175470668047)
        ·
          refine ⟨130547247128194763206002071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87031498085463175470668047 130547247128194763206002071)
          ·
            refine ⟨195820870692292144809003107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130547247128194763206002071 195820870692292144809003107)
            ·
              refine ⟨293731306038438217213504661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195820870692292144809003107 293731306038438217213504661)
              ·
                refine ⟨13768654970551791431883031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 293731306038438217213504661 13768654970551791431883031)
                ·
                  refine ⟨20652982455827687147824547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13768654970551791431883031 20652982455827687147824547)
                  ·
                    refine ⟨30979473683741530721736821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20652982455827687147824547 30979473683741530721736821)
                    ·
                      refine ⟨2904325657850768505162827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30979473683741530721736821 2904325657850768505162827)
                      ·
                        rfl

theorem cell23_5656154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_5656154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656154 prefixEnd_5656154 := by exact prefixLift 5656154
  have htrace : WordTrace (prefixWord ++ tailWord_5656154) baseStart_5656154 baseEnd_5656154 := by
    simpa [prefixWord, tailWord_5656154, baseEnd_5656154] using wordTrace_append hprefix tailTrace_5656154
  have hstable : (prefixWord ++ tailWord_5656154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656154).length < 2 ^ (prefixWord ++ tailWord_5656154).sum := by decide
  have hdescent : baseEnd_5656154 < baseStart_5656154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656161 : List Nat := [1, 2, 3, 1, 1, 3, 1, 5, 2, 4]
def baseStart_5656161 : Nat := 118140960795 + 5656161 * 2 ^ 59
def prefixEnd_5656161 : Nat := 4983230072969 + 3 ^ 40 * 5656161 * 2
def baseEnd_5656161 : Nat := 968109750738449992591765

theorem tailTrace_5656161 : CollatzResearch.WordTrace tailWord_5656161 prefixEnd_5656161 968109750738449992591765 := by
  unfold tailWord_5656161
  simp only [CollatzResearch.WordTrace]
  refine ⟨206297139661702167237088337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137531426441134778158058891 206297139661702167237088337)
  ·
    refine ⟨154722854746276625427816253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206297139661702167237088337 154722854746276625427816253)
    ·
      refine ⟨58021070529853734535431095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154722854746276625427816253 58021070529853734535431095)
      ·
        refine ⟨87031605794780601803146643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58021070529853734535431095 87031605794780601803146643)
        ·
          refine ⟨130547408692170902704719965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87031605794780601803146643 130547408692170902704719965)
          ·
            refine ⟨48955278259564088514269987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130547408692170902704719965 48955278259564088514269987)
            ·
              refine ⟨73432917389346132771404981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48955278259564088514269987 73432917389346132771404981)
              ·
                refine ⟨6884336005251199947319217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73432917389346132771404981 6884336005251199947319217)
                ·
                  refine ⟨5163252003938399960489413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6884336005251199947319217 5163252003938399960489413)
                  ·
                    refine ⟨968109750738449992591765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5163252003938399960489413 968109750738449992591765)
                    ·
                      rfl

theorem cell23_5656161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_5656161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656161 prefixEnd_5656161 := by exact prefixLift 5656161
  have htrace : WordTrace (prefixWord ++ tailWord_5656161) baseStart_5656161 baseEnd_5656161 := by
    simpa [prefixWord, tailWord_5656161, baseEnd_5656161] using wordTrace_append hprefix tailTrace_5656161
  have hstable : (prefixWord ++ tailWord_5656161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656161).length < 2 ^ (prefixWord ++ tailWord_5656161).sum := by decide
  have hdescent : baseEnd_5656161 < baseStart_5656161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656202 : List Nat := [3, 1, 2, 3, 2, 1, 2, 4, 1, 2, 2]
def baseStart_5656202 : Nat := 118140960795 + 5656202 * 2 ^ 59
def prefixEnd_5656202 : Nat := 4983230072969 + 3 ^ 40 * 5656202 * 2
def baseEnd_5656202 : Nat := 2904350304922184317362607

theorem tailTrace_5656202 : CollatzResearch.WordTrace tailWord_5656202 prefixEnd_5656202 2904350304922184317362607 := by
  unfold tailWord_5656202
  simp only [CollatzResearch.WordTrace]
  refine ⟨51574658763638407809832715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137532423369702420826220573 51574658763638407809832715)
  ·
    refine ⟨77361988145457611714749073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51574658763638407809832715 77361988145457611714749073)
    ·
      refine ⟨58021491109093208786061805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77361988145457611714749073 58021491109093208786061805)
      ·
        refine ⟨21758059165909953294773177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58021491109093208786061805 21758059165909953294773177)
        ·
          refine ⟨16318544374432464971079883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21758059165909953294773177 16318544374432464971079883)
          ·
            refine ⟨24477816561648697456619825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16318544374432464971079883 24477816561648697456619825)
            ·
              refine ⟨18358362421236523092464869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24477816561648697456619825 18358362421236523092464869)
              ·
                refine ⟨3442192953981848079837163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18358362421236523092464869 3442192953981848079837163)
                ·
                  refine ⟨5163289430972772119755745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3442192953981848079837163 5163289430972772119755745)
                  ·
                    refine ⟨3872467073229579089816809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5163289430972772119755745 3872467073229579089816809)
                    ·
                      refine ⟨2904350304922184317362607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3872467073229579089816809 2904350304922184317362607)
                      ·
                        rfl

theorem cell23_5656202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_5656202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656202 prefixEnd_5656202 := by exact prefixLift 5656202
  have htrace : WordTrace (prefixWord ++ tailWord_5656202) baseStart_5656202 baseEnd_5656202 := by
    simpa [prefixWord, tailWord_5656202, baseEnd_5656202] using wordTrace_append hprefix tailTrace_5656202
  have hstable : (prefixWord ++ tailWord_5656202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656202).length < 2 ^ (prefixWord ++ tailWord_5656202).sum := by decide
  have hdescent : baseEnd_5656202 < baseStart_5656202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656212 : List Nat := [2, 4, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_5656212 : Nat := 118140960795 + 5656212 * 2 ^ 59
def prefixEnd_5656212 : Nat := 4983230072969 + 3 ^ 40 * 5656212 * 2
def baseEnd_5656212 : Nat := 968118479909576426079187

theorem tailTrace_5656212 : CollatzResearch.WordTrace tailWord_5656212 prefixEnd_5656212 968118479909576426079187 := by
  unfold tailWord_5656212
  simp only [CollatzResearch.WordTrace]
  refine ⟨103149499892258701473597445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137532666523011601964796593 103149499892258701473597445)
  ·
    refine ⟨19340531229798506526299521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103149499892258701473597445 19340531229798506526299521)
    ·
      refine ⟨14505398422348879894724641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19340531229798506526299521 14505398422348879894724641)
      ·
        refine ⟨10879048816761659921043481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14505398422348879894724641 10879048816761659921043481)
        ·
          refine ⟨8159286612571244940782611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10879048816761659921043481 8159286612571244940782611)
          ·
            refine ⟨12238929918856867411173917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8159286612571244940782611 12238929918856867411173917)
            ·
              refine ⟨4589598719571325279190219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12238929918856867411173917 4589598719571325279190219)
              ·
                refine ⟨6884398079356987918785329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4589598719571325279190219 6884398079356987918785329)
                ·
                  refine ⟨5163298559517740939088997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6884398079356987918785329 5163298559517740939088997)
                  ·
                    refine ⟨968118479909576426079187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5163298559517740939088997 968118479909576426079187)
                    ·
                      rfl

theorem cell23_5656212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_5656212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656212 prefixEnd_5656212 := by exact prefixLift 5656212
  have htrace : WordTrace (prefixWord ++ tailWord_5656212) baseStart_5656212 baseEnd_5656212 := by
    simpa [prefixWord, tailWord_5656212, baseEnd_5656212] using wordTrace_append hprefix tailTrace_5656212
  have hstable : (prefixWord ++ tailWord_5656212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656212).length < 2 ^ (prefixWord ++ tailWord_5656212).sum := by decide
  have hdescent : baseEnd_5656212 < baseStart_5656212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656269 : List Nat := [1, 6, 2, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_5656269 : Nat := 118140960795 + 5656269 * 2 ^ 59
def prefixEnd_5656269 : Nat := 4983230072969 + 3 ^ 40 * 5656269 * 2
def baseEnd_5656269 : Nat := 2904384708126035555224799

theorem tailTrace_5656269 : CollatzResearch.WordTrace tailWord_5656269 prefixEnd_5656269 2904384708126035555224799 := by
  unfold tailWord_5656269
  simp only [CollatzResearch.WordTrace]
  refine ⟨206301078745310901682019861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137534052496873934454679907 206301078745310901682019861)
  ·
    refine ⟨9670363066186448516344681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 206301078745310901682019861 9670363066186448516344681)
    ·
      refine ⟨7252772299639836387258511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9670363066186448516344681 7252772299639836387258511)
      ·
        refine ⟨10879158449459754580887767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7252772299639836387258511 10879158449459754580887767)
        ·
          refine ⟨16318737674189631871331651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10879158449459754580887767 16318737674189631871331651)
          ·
            refine ⟨24478106511284447806997477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16318737674189631871331651 24478106511284447806997477)
            ·
              refine ⟨4589644970865833963812027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24478106511284447806997477 4589644970865833963812027)
              ·
                refine ⟨6884467456298750945718041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4589644970865833963812027 6884467456298750945718041)
                ·
                  refine ⟨5163350592224063209288531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6884467456298750945718041 5163350592224063209288531)
                  ·
                    refine ⟨7745025888336094813932797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5163350592224063209288531 7745025888336094813932797)
                    ·
                      refine ⟨2904384708126035555224799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7745025888336094813932797 2904384708126035555224799)
                      ·
                        rfl

theorem cell23_5656269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_5656269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656269 prefixEnd_5656269 := by exact prefixLift 5656269
  have htrace : WordTrace (prefixWord ++ tailWord_5656269) baseStart_5656269 baseEnd_5656269 := by
    simpa [prefixWord, tailWord_5656269, baseEnd_5656269] using wordTrace_append hprefix tailTrace_5656269
  have hstable : (prefixWord ++ tailWord_5656269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656269).length < 2 ^ (prefixWord ++ tailWord_5656269).sum := by decide
  have hdescent : baseEnd_5656269 < baseStart_5656269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656311 : List Nat := [1, 1, 3, 1, 1, 1, 6, 2, 2, 5]
def baseStart_5656311 : Nat := 118140960795 + 5656311 * 2 ^ 59
def prefixEnd_5656311 : Nat := 4983230072969 + 3 ^ 40 * 5656311 * 2
def baseEnd_5656311 : Nat := 968135424771174796966535

theorem tailTrace_5656311 : CollatzResearch.WordTrace tailWord_5656311 prefixEnd_5656311 968135424771174796966535 := by
  unfold tailWord_5656311
  simp only [CollatzResearch.WordTrace]
  refine ⟨206302610611158742855048787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137535073740772495236699191 206302610611158742855048787)
  ·
    refine ⟨309453915916738114282573181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206302610611158742855048787 309453915916738114282573181)
    ·
      refine ⟨116045218468776792855964943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309453915916738114282573181 116045218468776792855964943)
      ·
        refine ⟨174067827703165189283947415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116045218468776792855964943 174067827703165189283947415)
        ·
          refine ⟨261101741554747783925921123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174067827703165189283947415 261101741554747783925921123)
          ·
            refine ⟨391652612332121675888881685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261101741554747783925921123 391652612332121675888881685)
            ·
              refine ⟨18358716203068203557291329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 391652612332121675888881685 18358716203068203557291329)
              ·
                refine ⟨13769037152301152667968497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18358716203068203557291329 13769037152301152667968497)
                ·
                  refine ⟨10326777864225864500976373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13769037152301152667968497 10326777864225864500976373)
                  ·
                    refine ⟨968135424771174796966535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10326777864225864500976373 968135424771174796966535)
                    ·
                      rfl

theorem cell23_5656311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_5656311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656311 prefixEnd_5656311 := by exact prefixLift 5656311
  have htrace : WordTrace (prefixWord ++ tailWord_5656311) baseStart_5656311 baseEnd_5656311 := by
    simpa [prefixWord, tailWord_5656311, baseEnd_5656311] using wordTrace_append hprefix tailTrace_5656311
  have hstable : (prefixWord ++ tailWord_5656311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656311).length < 2 ^ (prefixWord ++ tailWord_5656311).sum := by decide
  have hdescent : baseEnd_5656311 < baseStart_5656311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656321 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_5656321 : Nat := 118140960795 + 5656321 * 2 ^ 59
def prefixEnd_5656321 : Nat := 4983230072969 + 3 ^ 40 * 5656321 * 2
def baseEnd_5656321 : Nat := 2904411409120069351774559

theorem tailTrace_5656321 : CollatzResearch.WordTrace tailWord_5656321 prefixEnd_5656321 2904411409120069351774559 := by
  unfold tailWord_5656321
  simp only [CollatzResearch.WordTrace]
  refine ⟨206302975341122514562912817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137535316894081676375275211 206302975341122514562912817)
  ·
    refine ⟨154727231505841885922184613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206302975341122514562912817 154727231505841885922184613)
    ·
      refine ⟨29011355907345353610409615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154727231505841885922184613 29011355907345353610409615)
      ·
        refine ⟨43517033861018030415614423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29011355907345353610409615 43517033861018030415614423)
        ·
          refine ⟨65275550791527045623421635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43517033861018030415614423 65275550791527045623421635)
          ·
            refine ⟨97913326187290568435132453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65275550791527045623421635 97913326187290568435132453)
            ·
              refine ⟨18358748660116981581587335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97913326187290568435132453 18358748660116981581587335)
              ·
                refine ⟨27538122990175472372381003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18358748660116981581587335 27538122990175472372381003)
                ·
                  refine ⟨41307184485263208558571505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27538122990175472372381003 41307184485263208558571505)
                  ·
                    refine ⟨30980388363947406418928629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41307184485263208558571505 30980388363947406418928629)
                    ·
                      refine ⟨2904411409120069351774559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30980388363947406418928629 2904411409120069351774559)
                      ·
                        rfl

theorem cell23_5656321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_5656321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656321 prefixEnd_5656321 := by exact prefixLift 5656321
  have htrace : WordTrace (prefixWord ++ tailWord_5656321) baseStart_5656321 baseEnd_5656321 := by
    simpa [prefixWord, tailWord_5656321, baseEnd_5656321] using wordTrace_append hprefix tailTrace_5656321
  have hstable : (prefixWord ++ tailWord_5656321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656321).length < 2 ^ (prefixWord ++ tailWord_5656321).sum := by decide
  have hdescent : baseEnd_5656321 < baseStart_5656321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656331 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 4]
def baseStart_5656331 : Nat := 118140960795 + 5656331 * 2 ^ 59
def prefixEnd_5656331 : Nat := 4983230072969 + 3 ^ 40 * 5656331 * 2
def baseEnd_5656331 : Nat := 2904416543926614312649513

theorem tailTrace_5656331 : CollatzResearch.WordTrace tailWord_5656331 prefixEnd_5656331 2904416543926614312649513 := by
  unfold tailWord_5656331
  simp only [CollatzResearch.WordTrace]
  refine ⟨206303340071086286270776847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137535560047390857513851231 206303340071086286270776847)
  ·
    refine ⟨309455010106629429406165271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206303340071086286270776847 309455010106629429406165271)
    ·
      refine ⟨464182515159944144109247907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309455010106629429406165271 464182515159944144109247907)
      ·
        refine ⟨696273772739916216163871861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464182515159944144109247907 696273772739916216163871861)
        ·
          refine ⟨65275666194367145265362987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 696273772739916216163871861 65275666194367145265362987)
          ·
            refine ⟨97913499291550717898044481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65275666194367145265362987 97913499291550717898044481)
            ·
              refine ⟨73435124468663038423533361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97913499291550717898044481 73435124468663038423533361)
              ·
                refine ⟨55076343351497278817650021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73435124468663038423533361 55076343351497278817650021)
                ·
                  refine ⟨10326814378405739778309379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55076343351497278817650021 10326814378405739778309379)
                  ·
                    refine ⟨15490221567608609667464069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10326814378405739778309379 15490221567608609667464069)
                    ·
                      refine ⟨2904416543926614312649513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15490221567608609667464069 2904416543926614312649513)
                      ·
                        rfl

theorem cell23_5656331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 4].length) (baseStart_5656331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656331 prefixEnd_5656331 := by exact prefixLift 5656331
  have htrace : WordTrace (prefixWord ++ tailWord_5656331) baseStart_5656331 baseEnd_5656331 := by
    simpa [prefixWord, tailWord_5656331, baseEnd_5656331] using wordTrace_append hprefix tailTrace_5656331
  have hstable : (prefixWord ++ tailWord_5656331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656331).length < 2 ^ (prefixWord ++ tailWord_5656331).sum := by decide
  have hdescent : baseEnd_5656331 < baseStart_5656331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656348 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 1, 6, 2]
def baseStart_5656348 : Nat := 118140960795 + 5656348 * 2 ^ 59
def prefixEnd_5656348 : Nat := 4983230072969 + 3 ^ 40 * 5656348 * 2
def baseEnd_5656348 : Nat := 2904425273097740746136935

theorem tailTrace_5656348 : CollatzResearch.WordTrace tailWord_5656348 prefixEnd_5656348 2904425273097740746136935 := by
  unfold tailWord_5656348
  simp only [CollatzResearch.WordTrace]
  refine ⟨103151980056012349087072849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137535973408016465449430465 103151980056012349087072849)
  ·
    refine ⟨77363985042009261815304637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103151980056012349087072849 77363985042009261815304637)
    ·
      refine ⟨29011494390753473180739239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77363985042009261815304637 29011494390753473180739239)
      ·
        refine ⟨43517241586130209771108859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29011494390753473180739239 43517241586130209771108859)
        ·
          refine ⟨65275862379195314656663289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43517241586130209771108859 65275862379195314656663289)
          ·
            refine ⟨48956896784396485992497467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65275862379195314656663289 48956896784396485992497467)
            ·
              refine ⟨73435345176594728988746201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48956896784396485992497467 73435345176594728988746201)
              ·
                refine ⟨55076508882446046741559651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73435345176594728988746201 55076508882446046741559651)
                ·
                  refine ⟨82614763323669070112339477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55076508882446046741559651 82614763323669070112339477)
                  ·
                    refine ⟨3872567030796987661515913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82614763323669070112339477 3872567030796987661515913)
                    ·
                      refine ⟨2904425273097740746136935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3872567030796987661515913 2904425273097740746136935)
                      ·
                        rfl

theorem cell23_5656348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_5656348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656348 prefixEnd_5656348 := by exact prefixLift 5656348
  have htrace : WordTrace (prefixWord ++ tailWord_5656348) baseStart_5656348 baseEnd_5656348 := by
    simpa [prefixWord, tailWord_5656348, baseEnd_5656348] using wordTrace_append hprefix tailTrace_5656348
  have hstable : (prefixWord ++ tailWord_5656348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656348).length < 2 ^ (prefixWord ++ tailWord_5656348).sum := by decide
  have hdescent : baseEnd_5656348 < baseStart_5656348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656426 : List Nat := [3, 1, 3, 4, 1, 1, 3, 2, 1, 4]
def baseStart_5656426 : Nat := 118140960795 + 5656426 * 2 ^ 59
def prefixEnd_5656426 : Nat := 4983230072969 + 3 ^ 40 * 5656426 * 2
def baseEnd_5656426 : Nat := 968155108196263813653859

theorem tailTrace_5656426 : CollatzResearch.WordTrace tailWord_5656426 prefixEnd_5656426 968155108196263813653859 := by
  unfold tailWord_5656426
  simp only [CollatzResearch.WordTrace]
  refine ⟨51576701251435529373871283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137537870003828078330323421 51576701251435529373871283)
  ·
    refine ⟨77365051877153294060806925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51576701251435529373871283 77365051877153294060806925)
    ·
      refine ⟨29011894453932485272802597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77365051877153294060806925 29011894453932485272802597)
      ·
        refine ⟨5439730210112340988650487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29011894453932485272802597 5439730210112340988650487)
        ·
          refine ⟨8159595315168511482975731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5439730210112340988650487 8159595315168511482975731)
          ·
            refine ⟨12239392972752767224463597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8159595315168511482975731 12239392972752767224463597)
            ·
              refine ⟨4589772364782287709173849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12239392972752767224463597 4589772364782287709173849)
              ·
                refine ⟨3442329273586715781880387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4589772364782287709173849 3442329273586715781880387)
                ·
                  refine ⟨5163493910380073672820581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3442329273586715781880387 5163493910380073672820581)
                  ·
                    refine ⟨968155108196263813653859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5163493910380073672820581 968155108196263813653859)
                    ·
                      rfl

theorem cell23_5656426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_5656426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656426 prefixEnd_5656426 := by exact prefixLift 5656426
  have htrace : WordTrace (prefixWord ++ tailWord_5656426) baseStart_5656426 baseEnd_5656426 := by
    simpa [prefixWord, tailWord_5656426, baseEnd_5656426] using wordTrace_append hprefix tailTrace_5656426
  have hstable : (prefixWord ++ tailWord_5656426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656426).length < 2 ^ (prefixWord ++ tailWord_5656426).sum := by decide
  have hdescent : baseEnd_5656426 < baseStart_5656426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656455 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 4]
def baseStart_5656455 : Nat := 118140960795 + 5656455 * 2 ^ 59
def prefixEnd_5656455 : Nat := 4983230072969 + 3 ^ 40 * 5656455 * 2
def baseEnd_5656455 : Nat := 2904480215527771827498943

theorem tailTrace_5656455 : CollatzResearch.WordTrace tailWord_5656455 prefixEnd_5656455 2904480215527771827498943 := by
  unfold tailWord_5656455
  simp only [CollatzResearch.WordTrace]
  refine ⟨206307862722637055448290819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137538575148424703632193879 206307862722637055448290819)
  ·
    refine ⟨309461794083955583172436229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206307862722637055448290819 309461794083955583172436229)
    ·
      refine ⟨58024086390741671844831793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 309461794083955583172436229 58024086390741671844831793)
      ·
        refine ⟨43518064793056253883623845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58024086390741671844831793 43518064793056253883623845)
        ·
          refine ⟨8159637148698047603179471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43518064793056253883623845 8159637148698047603179471)
          ·
            refine ⟨12239455723047071404769207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8159637148698047603179471 12239455723047071404769207)
            ·
              refine ⟨18359183584570607107153811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12239455723047071404769207 18359183584570607107153811)
              ·
                refine ⟨27538775376855910660730717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18359183584570607107153811 27538775376855910660730717)
                ·
                  refine ⟨10327040766320966497774019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27538775376855910660730717 10327040766320966497774019)
                  ·
                    refine ⟨15490561149481449746661029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10327040766320966497774019 15490561149481449746661029)
                    ·
                      refine ⟨2904480215527771827498943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15490561149481449746661029 2904480215527771827498943)
                      ·
                        rfl

theorem cell23_5656455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_5656455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656455 prefixEnd_5656455 := by exact prefixLift 5656455
  have htrace : WordTrace (prefixWord ++ tailWord_5656455) baseStart_5656455 baseEnd_5656455 := by
    simpa [prefixWord, tailWord_5656455, baseEnd_5656455] using wordTrace_append hprefix tailTrace_5656455
  have hstable : (prefixWord ++ tailWord_5656455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656455).length < 2 ^ (prefixWord ++ tailWord_5656455).sum := by decide
  have hdescent : baseEnd_5656455 < baseStart_5656455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656505 : List Nat := [1, 2, 1, 4, 2, 1, 4, 1, 1, 3, 3]
def baseStart_5656505 : Nat := 118140960795 + 5656505 * 2 ^ 59
def prefixEnd_5656505 : Nat := 4983230072969 + 3 ^ 40 * 5656505 * 2
def baseEnd_5656505 : Nat := 2904505889560496631873713

theorem tailTrace_5656505 : CollatzResearch.WordTrace tailWord_5656505 prefixEnd_5656505 2904505889560496631873713 := by
  unfold tailWord_5656505
  simp only [CollatzResearch.WordTrace]
  refine ⟨206309686372455913987610969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137539790914970609325073979 206309686372455913987610969)
  ·
    refine ⟨154732264779341935490708227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206309686372455913987610969 154732264779341935490708227)
    ·
      refine ⟨232098397169012903236062341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154732264779341935490708227 232098397169012903236062341)
      ·
        refine ⟨43518449469189919356761689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232098397169012903236062341 43518449469189919356761689)
        ·
          refine ⟨32638837101892439517571267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43518449469189919356761689 32638837101892439517571267)
          ·
            refine ⟨48958255652838659276356901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32638837101892439517571267 48958255652838659276356901)
            ·
              refine ⟨9179672934907248614316919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48958255652838659276356901 9179672934907248614316919)
              ·
                refine ⟨13769509402360872921475379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9179672934907248614316919 13769509402360872921475379)
                ·
                  refine ⟨20654264103541309382213069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13769509402360872921475379 20654264103541309382213069)
                  ·
                    refine ⟨7745349038827991018329901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20654264103541309382213069 7745349038827991018329901)
                    ·
                      refine ⟨2904505889560496631873713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7745349038827991018329901 2904505889560496631873713)
                      ·
                        rfl

theorem cell23_5656505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_5656505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656505 prefixEnd_5656505 := by exact prefixLift 5656505
  have htrace : WordTrace (prefixWord ++ tailWord_5656505) baseStart_5656505 baseEnd_5656505 := by
    simpa [prefixWord, tailWord_5656505, baseEnd_5656505] using wordTrace_append hprefix tailTrace_5656505
  have hstable : (prefixWord ++ tailWord_5656505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656505).length < 2 ^ (prefixWord ++ tailWord_5656505).sum := by decide
  have hdescent : baseEnd_5656505 < baseStart_5656505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656545 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 3, 4, 2]
def baseStart_5656545 : Nat := 118140960795 + 5656545 * 2 ^ 59
def prefixEnd_5656545 : Nat := 4983230072969 + 3 ^ 40 * 5656545 * 2
def baseEnd_5656545 : Nat := 2904526428786676475373529

theorem tailTrace_5656545 : CollatzResearch.WordTrace tailWord_5656545 prefixEnd_5656545 2904526428786676475373529 := by
  unfold tailWord_5656545
  simp only [CollatzResearch.WordTrace]
  refine ⟨206311145292311000819067089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137540763528207333879378059 206311145292311000819067089)
  ·
    refine ⟨154733358969233250614300317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206311145292311000819067089 154733358969233250614300317)
    ·
      refine ⟨58025009613462468980362619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154733358969233250614300317 58025009613462468980362619)
      ·
        refine ⟨87037514420193703470543929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58025009613462468980362619 87037514420193703470543929)
        ·
          refine ⟨65278135815145277602907947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87037514420193703470543929 65278135815145277602907947)
          ·
            refine ⟨97917203722717916404361921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65278135815145277602907947 97917203722717916404361921)
            ·
              refine ⟨73437902792038437303271441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97917203722717916404361921 73437902792038437303271441)
              ·
                refine ⟨55078427094028827977453581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73437902792038437303271441 55078427094028827977453581)
                ·
                  refine ⟨20654410160260810491545093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55078427094028827977453581 20654410160260810491545093)
                  ·
                    refine ⟨3872701905048901967164705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20654410160260810491545093 3872701905048901967164705)
                    ·
                      refine ⟨2904526428786676475373529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3872701905048901967164705 2904526428786676475373529)
                      ·
                        rfl

theorem cell23_5656545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_5656545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656545 prefixEnd_5656545 := by exact prefixLift 5656545
  have htrace : WordTrace (prefixWord ++ tailWord_5656545) baseStart_5656545 baseEnd_5656545 := by
    simpa [prefixWord, tailWord_5656545, baseEnd_5656545] using wordTrace_append hprefix tailTrace_5656545
  have hstable : (prefixWord ++ tailWord_5656545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656545).length < 2 ^ (prefixWord ++ tailWord_5656545).sum := by decide
  have hdescent : baseEnd_5656545 < baseStart_5656545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656566 : List Nat := [5, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2]
def baseStart_5656566 : Nat := 118140960795 + 5656566 * 2 ^ 59
def prefixEnd_5656566 : Nat := 4983230072969 + 3 ^ 40 * 5656566 * 2
def baseEnd_5656566 : Nat := 2904537211880420893210933

theorem tailTrace_5656566 : CollatzResearch.WordTrace tailWord_5656566 prefixEnd_5656566 2904537211880420893210933 := by
  unfold tailWord_5656566
  simp only [CollatzResearch.WordTrace]
  refine ⟨12894494451577182587848847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137541274150156614270387701 12894494451577182587848847)
  ·
    refine ⟨19341741677365773881773271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12894494451577182587848847 19341741677365773881773271)
    ·
      refine ⟨29012612516048660822659907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19341741677365773881773271 29012612516048660822659907)
      ·
        refine ⟨43518918774072991233989861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29012612516048660822659907 43518918774072991233989861)
        ·
          refine ⟨8159797270138685856373099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43518918774072991233989861 8159797270138685856373099)
          ·
            refine ⟨12239695905208028784559649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8159797270138685856373099 12239695905208028784559649)
            ·
              refine ⟨9179771928906021588419737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12239695905208028784559649 9179771928906021588419737)
              ·
                refine ⟨6884828946679516191314803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9179771928906021588419737 6884828946679516191314803)
                ·
                  refine ⟨10327243420019274286972205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6884828946679516191314803 10327243420019274286972205)
                  ·
                    refine ⟨3872716282507227857614577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10327243420019274286972205 3872716282507227857614577)
                    ·
                      refine ⟨2904537211880420893210933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3872716282507227857614577 2904537211880420893210933)
                      ·
                        rfl

theorem cell23_5656566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_5656566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656566 prefixEnd_5656566 := by exact prefixLift 5656566
  have htrace : WordTrace (prefixWord ++ tailWord_5656566) baseStart_5656566 baseEnd_5656566 := by
    simpa [prefixWord, tailWord_5656566, baseEnd_5656566] using wordTrace_append hprefix tailTrace_5656566
  have hstable : (prefixWord ++ tailWord_5656566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656566).length < 2 ^ (prefixWord ++ tailWord_5656566).sum := by decide
  have hdescent : baseEnd_5656566 < baseStart_5656566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656568 : List Nat := [2, 1, 2, 1, 1, 3, 4, 2, 7]
def baseStart_5656568 : Nat := 118140960795 + 5656568 * 2 ^ 59
def prefixEnd_5656568 : Nat := 4983230072969 + 3 ^ 40 * 5656568 * 2
def baseEnd_5656568 : Nat := 322726470982414431709547

theorem tailTrace_5656568 : CollatzResearch.WordTrace tailWord_5656568 prefixEnd_5656568 322726470982414431709547 := by
  unfold tailWord_5656568
  simp only [CollatzResearch.WordTrace]
  refine ⟨103155992085613837873577179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137541322780818450498102905 103155992085613837873577179)
  ·
    refine ⟨154733988128420756810365769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103155992085613837873577179 154733988128420756810365769)
    ·
      refine ⟨116050491096315567607774327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154733988128420756810365769 116050491096315567607774327)
      ·
        refine ⟨174075736644473351411661491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116050491096315567607774327 174075736644473351411661491)
        ·
          refine ⟨261113604966710027117492237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174075736644473351411661491 261113604966710027117492237)
          ·
            refine ⟨97917601862516260169059589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261113604966710027117492237 97917601862516260169059589)
            ·
              refine ⟨18359550349221798781698673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97917601862516260169059589 18359550349221798781698673)
              ·
                refine ⟨13769662761916349086274005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18359550349221798781698673 13769662761916349086274005)
                ·
                  refine ⟨322726470982414431709547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13769662761916349086274005 322726470982414431709547)
                  ·
                    rfl

theorem cell23_5656568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 7].length) (baseStart_5656568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656568 prefixEnd_5656568 := by exact prefixLift 5656568
  have htrace : WordTrace (prefixWord ++ tailWord_5656568) baseStart_5656568 baseEnd_5656568 := by
    simpa [prefixWord, tailWord_5656568, baseEnd_5656568] using wordTrace_append hprefix tailTrace_5656568
  have hstable : (prefixWord ++ tailWord_5656568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656568).length < 2 ^ (prefixWord ++ tailWord_5656568).sum := by decide
  have hdescent : baseEnd_5656568 < baseStart_5656568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656632 : List Nat := [2, 1, 2, 1, 6, 1, 2, 1, 2, 5]
def baseStart_5656632 : Nat := 118140960795 + 5656632 * 2 ^ 59
def prefixEnd_5656632 : Nat := 4983230072969 + 3 ^ 40 * 5656632 * 2
def baseEnd_5656632 : Nat := 968190367201205878328543

theorem tailTrace_5656632 : CollatzResearch.WordTrace tailWord_5656632 prefixEnd_5656632 968190367201205878328543 := by
  unfold tailWord_5656632
  simp only [CollatzResearch.WordTrace]
  refine ⟨103157159221497907338742075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137542878961997209784989433 103157159221497907338742075)
  ·
    refine ⟨154735738832246861008113113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103157159221497907338742075 154735738832246861008113113)
    ·
      refine ⟨116051804124185145756084835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154735738832246861008113113 116051804124185145756084835)
      ·
        refine ⟨174077706186277718634127253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116051804124185145756084835 174077706186277718634127253)
        ·
          refine ⟨8159892477481768060974715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 174077706186277718634127253 8159892477481768060974715)
          ·
            refine ⟨12239838716222652091462073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8159892477481768060974715 12239838716222652091462073)
            ·
              refine ⟨9179879037166989068596555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12239838716222652091462073 9179879037166989068596555)
              ·
                refine ⟨13769818555750483602894833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9179879037166989068596555 13769818555750483602894833)
                ·
                  refine ⟨10327363916812862702171125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13769818555750483602894833 10327363916812862702171125)
                  ·
                    refine ⟨968190367201205878328543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10327363916812862702171125 968190367201205878328543)
                    ·
                      rfl

theorem cell23_5656632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_5656632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656632 prefixEnd_5656632 := by exact prefixLift 5656632
  have htrace : WordTrace (prefixWord ++ tailWord_5656632) baseStart_5656632 baseEnd_5656632 := by
    simpa [prefixWord, tailWord_5656632, baseEnd_5656632] using wordTrace_append hprefix tailTrace_5656632
  have hstable : (prefixWord ++ tailWord_5656632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656632).length < 2 ^ (prefixWord ++ tailWord_5656632).sum := by decide
  have hdescent : baseEnd_5656632 < baseStart_5656632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656635 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 1, 6, 2]
def baseStart_5656635 : Nat := 118140960795 + 5656635 * 2 ^ 59
def prefixEnd_5656635 : Nat := 4983230072969 + 3 ^ 40 * 5656635 * 2
def baseEnd_5656635 : Nat := 2904572642045581123248115

theorem tailTrace_5656635 : CollatzResearch.WordTrace tailWord_5656635 prefixEnd_5656635 2904572642045581123248115 := by
  unfold tailWord_5656635
  simp only [CollatzResearch.WordTrace]
  refine ⟨206314427861984946189843359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137542951907989964126562239 206314427861984946189843359)
  ·
    refine ⟨309471641792977419284765039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206314427861984946189843359 309471641792977419284765039)
    ·
      refine ⟨464207462689466128927147559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309471641792977419284765039 464207462689466128927147559)
      ·
        refine ⟨696311194034199193390721339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464207462689466128927147559 696311194034199193390721339)
        ·
          refine ⟨1044466791051298790086082009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 696311194034199193390721339 1044466791051298790086082009)
          ·
            refine ⟨783350093288474092564561507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1044466791051298790086082009 783350093288474092564561507)
            ·
              refine ⟨1175025139932711138846842261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783350093288474092564561507 1175025139932711138846842261)
              ·
                refine ⟨55079303434345834633445731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1175025139932711138846842261 55079303434345834633445731)
                ·
                  refine ⟨82618955151518751950168597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55079303434345834633445731 82618955151518751950168597)
                  ·
                    refine ⟨3872763522727441497664153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82618955151518751950168597 3872763522727441497664153)
                    ·
                      refine ⟨2904572642045581123248115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3872763522727441497664153 2904572642045581123248115)
                      ·
                        rfl

theorem cell23_5656635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 6, 2].length) (baseStart_5656635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656635 prefixEnd_5656635 := by exact prefixLift 5656635
  have htrace : WordTrace (prefixWord ++ tailWord_5656635) baseStart_5656635 baseEnd_5656635 := by
    simpa [prefixWord, tailWord_5656635, baseEnd_5656635] using wordTrace_append hprefix tailTrace_5656635
  have hstable : (prefixWord ++ tailWord_5656635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656635).length < 2 ^ (prefixWord ++ tailWord_5656635).sum := by decide
  have hdescent : baseEnd_5656635 < baseStart_5656635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656669 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_5656669 : Nat := 118140960795 + 5656669 * 2 ^ 59
def prefixEnd_5656669 : Nat := 4983230072969 + 3 ^ 40 * 5656669 * 2
def baseEnd_5656669 : Nat := 2904590100387833990222959

theorem tailTrace_5656669 : CollatzResearch.WordTrace tailWord_5656669 prefixEnd_5656669 2904590100387833990222959 := by
  unfold tailWord_5656669
  simp only [CollatzResearch.WordTrace]
  refine ⟨206315667943861769996581061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137543778629241179997720707 206315667943861769996581061)
  ·
    refine ⟨38684187739474081874358949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206315667943861769996581061 38684187739474081874358949)
    ·
      refine ⟨7253285201151390351442303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38684187739474081874358949 7253285201151390351442303)
      ·
        refine ⟨10879927801727085527163455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7253285201151390351442303 10879927801727085527163455)
        ·
          refine ⟨16319891702590628290745183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10879927801727085527163455 16319891702590628290745183)
          ·
            refine ⟨24479837553885942436117775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16319891702590628290745183 24479837553885942436117775)
            ·
              refine ⟨36719756330828913654176663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24479837553885942436117775 36719756330828913654176663)
              ·
                refine ⟨55079634496243370481264995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36719756330828913654176663 55079634496243370481264995)
                ·
                  refine ⟨82619451744365055721897493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55079634496243370481264995 82619451744365055721897493)
                  ·
                    refine ⟨3872786800517111986963945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82619451744365055721897493 3872786800517111986963945)
                    ·
                      refine ⟨2904590100387833990222959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3872786800517111986963945 2904590100387833990222959)
                      ·
                        rfl

theorem cell23_5656669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_5656669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656669 prefixEnd_5656669 := by exact prefixLift 5656669
  have htrace : WordTrace (prefixWord ++ tailWord_5656669) baseStart_5656669 baseEnd_5656669 := by
    simpa [prefixWord, tailWord_5656669, baseEnd_5656669] using wordTrace_append hprefix tailTrace_5656669
  have hstable : (prefixWord ++ tailWord_5656669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656669).length < 2 ^ (prefixWord ++ tailWord_5656669).sum := by decide
  have hdescent : baseEnd_5656669 < baseStart_5656669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656675 : List Nat := [1, 1, 1, 5, 1, 1, 4, 3, 6]
def baseStart_5656675 : Nat := 118140960795 + 5656675 * 2 ^ 59
def prefixEnd_5656675 : Nat := 4983230072969 + 3 ^ 40 * 5656675 * 2
def baseEnd_5656675 : Nat := 322732575696862329638659

theorem tailTrace_5656675 : CollatzResearch.WordTrace tailWord_5656675 prefixEnd_5656675 322732575696862329638659 := by
  unfold tailWord_5656675
  simp only [CollatzResearch.WordTrace]
  refine ⟨206315886781840033021299479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137543924521226688680866319 206315886781840033021299479)
  ·
    refine ⟨309473830172760049531949219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206315886781840033021299479 309473830172760049531949219)
    ·
      refine ⟨464210745259140074297923829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309473830172760049531949219 464210745259140074297923829)
      ·
        refine ⟨43519757368044381965430359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 464210745259140074297923829 43519757368044381965430359)
        ·
          refine ⟨65279636052066572948145539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43519757368044381965430359 65279636052066572948145539)
          ·
            refine ⟨97919454078099859422218309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65279636052066572948145539 97919454078099859422218309)
            ·
              refine ⟨18359897639643723641665933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97919454078099859422218309 18359897639643723641665933)
              ·
                refine ⟨6884961614866396365624725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18359897639643723641665933 6884961614866396365624725)
                ·
                  refine ⟨322732575696862329638659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6884961614866396365624725 322732575696862329638659)
                  ·
                    rfl

theorem cell23_5656675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 6].length) (baseStart_5656675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656675 prefixEnd_5656675 := by exact prefixLift 5656675
  have htrace : WordTrace (prefixWord ++ tailWord_5656675) baseStart_5656675 baseEnd_5656675 := by
    simpa [prefixWord, tailWord_5656675, baseEnd_5656675] using wordTrace_append hprefix tailTrace_5656675
  have hstable : (prefixWord ++ tailWord_5656675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656675).length < 2 ^ (prefixWord ++ tailWord_5656675).sum := by decide
  have hdescent : baseEnd_5656675 < baseStart_5656675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656755 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 4]
def baseStart_5656755 : Nat := 118140960795 + 5656755 * 2 ^ 59
def prefixEnd_5656755 : Nat := 4983230072969 + 3 ^ 40 * 5656755 * 2
def baseEnd_5656755 : Nat := 2904634259724120653747563

theorem tailTrace_5656755 : CollatzResearch.WordTrace tailWord_5656755 prefixEnd_5656755 2904634259724120653747563 := by
  unfold tailWord_5656755
  simp only [CollatzResearch.WordTrace]
  refine ⟨206318804621550206684211719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137545869747700137789474479 206318804621550206684211719)
  ·
    refine ⟨309478206932325310026317579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206318804621550206684211719 309478206932325310026317579)
    ·
      refine ⟨464217310398487965039476369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309478206932325310026317579 464217310398487965039476369)
      ·
        refine ⟨348162982798865973779607277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 464217310398487965039476369 348162982798865973779607277)
        ·
          refine ⟨130561118549574740167352729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348162982798865973779607277 130561118549574740167352729)
          ·
            refine ⟨97920838912181055125514547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130561118549574740167352729 97920838912181055125514547)
            ·
              refine ⟨146881258368271582688271821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97920838912181055125514547 146881258368271582688271821)
              ·
                refine ⟨55080471888101843508101933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146881258368271582688271821 55080471888101843508101933)
                ·
                  refine ⟨20655176958038191315538225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55080471888101843508101933 20655176958038191315538225)
                  ·
                    refine ⟨15491382718528643486653669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20655176958038191315538225 15491382718528643486653669)
                    ·
                      refine ⟨2904634259724120653747563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15491382718528643486653669 2904634259724120653747563)
                      ·
                        rfl

theorem cell23_5656755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_5656755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656755 prefixEnd_5656755 := by exact prefixLift 5656755
  have htrace : WordTrace (prefixWord ++ tailWord_5656755) baseStart_5656755 baseEnd_5656755 := by
    simpa [prefixWord, tailWord_5656755, baseEnd_5656755] using wordTrace_append hprefix tailTrace_5656755
  have hstable : (prefixWord ++ tailWord_5656755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656755).length < 2 ^ (prefixWord ++ tailWord_5656755).sum := by decide
  have hdescent : baseEnd_5656755 < baseStart_5656755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656770 : List Nat := [3, 5, 1, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_5656770 : Nat := 118140960795 + 5656770 * 2 ^ 59
def prefixEnd_5656770 : Nat := 4983230072969 + 3 ^ 40 * 5656770 * 2
def baseEnd_5656770 : Nat := 2904641961933938095059995

theorem tailTrace_5656770 : CollatzResearch.WordTrace tailWord_5656770 prefixEnd_5656770 2904641961933938095059995 := by
  unfold tailWord_5656770
  simp only [CollatzResearch.WordTrace]
  refine ⟨51579837929123966061501941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137546234477663909497338509 51579837929123966061501941)
  ·
    refine ⟨4835609805855371818265807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51579837929123966061501941 4835609805855371818265807)
    ·
      refine ⟨7253414708783057727398711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4835609805855371818265807 7253414708783057727398711)
      ·
        refine ⟨10880122063174586591098067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7253414708783057727398711 10880122063174586591098067)
        ·
          refine ⟨16320183094761879886647101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10880122063174586591098067 16320183094761879886647101)
          ·
            refine ⟨6120068660535704957492663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16320183094761879886647101 6120068660535704957492663)
            ·
              refine ⟨9180102990803557436238995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6120068660535704957492663 9180102990803557436238995)
              ·
                refine ⟨13770154486205336154358493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9180102990803557436238995 13770154486205336154358493)
                ·
                  refine ⟨5163807932327001057884435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13770154486205336154358493 5163807932327001057884435)
                  ·
                    refine ⟨7745711898490501586826653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5163807932327001057884435 7745711898490501586826653)
                    ·
                      refine ⟨2904641961933938095059995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7745711898490501586826653 2904641961933938095059995)
                      ·
                        rfl

theorem cell23_5656770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_5656770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656770 prefixEnd_5656770 := by exact prefixLift 5656770
  have htrace : WordTrace (prefixWord ++ tailWord_5656770) baseStart_5656770 baseEnd_5656770 := by
    simpa [prefixWord, tailWord_5656770, baseEnd_5656770] using wordTrace_append hprefix tailTrace_5656770
  have hstable : (prefixWord ++ tailWord_5656770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656770).length < 2 ^ (prefixWord ++ tailWord_5656770).sum := by decide
  have hdescent : baseEnd_5656770 < baseStart_5656770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656772 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_5656772 : Nat := 118140960795 + 5656772 * 2 ^ 59
def prefixEnd_5656772 : Nat := 4983230072969 + 3 ^ 40 * 5656772 * 2
def baseEnd_5656772 : Nat := 2904642988895247087234985

theorem tailTrace_5656772 : CollatzResearch.WordTrace tailWord_5656772 prefixEnd_5656772 2904642988895247087234985 := by
  unfold tailWord_5656772
  simp only [CollatzResearch.WordTrace]
  refine ⟨103159712331244309293790285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137546283108325745725053713 103159712331244309293790285)
  ·
    refine ⟨38684892124216615985171357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103159712331244309293790285 38684892124216615985171357)
    ·
      refine ⟨14506834546581230994439259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38684892124216615985171357 14506834546581230994439259)
      ·
        refine ⟨21760251819871846491658889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14506834546581230994439259 21760251819871846491658889)
        ·
          refine ⟨16320188864903884868744167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21760251819871846491658889 16320188864903884868744167)
          ·
            refine ⟨24480283297355827303116251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16320188864903884868744167 24480283297355827303116251)
            ·
              refine ⟨36720424946033740954674377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24480283297355827303116251 36720424946033740954674377)
              ·
                refine ⟨27540318709525305716005783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36720424946033740954674377 27540318709525305716005783)
                ·
                  refine ⟨41310478064287958574008675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27540318709525305716005783 41310478064287958574008675)
                  ·
                    refine ⟨61965717096431937861013013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41310478064287958574008675 61965717096431937861013013)
                    ·
                      refine ⟨2904642988895247087234985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61965717096431937861013013 2904642988895247087234985)
                      ·
                        rfl

theorem cell23_5656772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_5656772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656772 prefixEnd_5656772 := by exact prefixLift 5656772
  have htrace : WordTrace (prefixWord ++ tailWord_5656772) baseStart_5656772 baseEnd_5656772 := by
    simpa [prefixWord, tailWord_5656772, baseEnd_5656772] using wordTrace_append hprefix tailTrace_5656772
  have hstable : (prefixWord ++ tailWord_5656772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656772).length < 2 ^ (prefixWord ++ tailWord_5656772).sum := by decide
  have hdescent : baseEnd_5656772 < baseStart_5656772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656782 : List Nat := [4, 1, 1, 1, 4, 2, 2, 8]
def baseStart_5656782 : Nat := 118140960795 + 5656782 * 2 ^ 59
def prefixEnd_5656782 : Nat := 4983230072969 + 3 ^ 40 * 5656782 * 2
def baseEnd_5656782 : Nat := 107579560137103409189257

theorem tailTrace_5656782 : CollatzResearch.WordTrace tailWord_5656782 prefixEnd_5656782 107579560137103409189257 := by
  unfold tailWord_5656782
  simp only [CollatzResearch.WordTrace]
  refine ⟨25789973674056548786930575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137546526261634926863629733 25789973674056548786930575)
  ·
    refine ⟨38684960511084823180395863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25789973674056548786930575 38684960511084823180395863)
    ·
      refine ⟨58027440766627234770593795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38684960511084823180395863 58027440766627234770593795)
      ·
        refine ⟨87041161149940852155890693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58027440766627234770593795 87041161149940852155890693)
        ·
          refine ⟨16320217715613909779229505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87041161149940852155890693 16320217715613909779229505)
          ·
            refine ⟨12240163286710432334422129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16320217715613909779229505 12240163286710432334422129)
            ·
              refine ⟨9180122465032824250816597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12240163286710432334422129 9180122465032824250816597)
              ·
                refine ⟨107579560137103409189257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9180122465032824250816597 107579560137103409189257)
                ·
                  rfl

theorem cell23_5656782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 8].length) (baseStart_5656782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656782 prefixEnd_5656782 := by exact prefixLift 5656782
  have htrace : WordTrace (prefixWord ++ tailWord_5656782) baseStart_5656782 baseEnd_5656782 := by
    simpa [prefixWord, tailWord_5656782, baseEnd_5656782] using wordTrace_append hprefix tailTrace_5656782
  have hstable : (prefixWord ++ tailWord_5656782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656782).length < 2 ^ (prefixWord ++ tailWord_5656782).sum := by decide
  have hdescent : baseEnd_5656782 < baseStart_5656782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656786 : List Nat := [3, 2, 2, 2, 1, 2, 4, 1, 2, 4]
def baseStart_5656786 : Nat := 118140960795 + 5656786 * 2 ^ 59
def prefixEnd_5656786 : Nat := 4983230072969 + 3 ^ 40 * 5656786 * 2
def baseEnd_5656786 : Nat := 968216725874803344153307

theorem tailTrace_5656786 : CollatzResearch.WordTrace tailWord_5656786 prefixEnd_5656786 968216725874803344153307 := by
  unfold tailWord_5656786
  simp only [CollatzResearch.WordTrace]
  refine ⟨51579983821109474744647553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137546623522958599319060141 51579983821109474744647553)
  ·
    refine ⟨38684987865832106058485665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51579983821109474744647553 38684987865832106058485665)
    ·
      refine ⟨29013740899374079543864249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38684987865832106058485665 29013740899374079543864249)
      ·
        refine ⟨21760305674530559657898187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29013740899374079543864249 21760305674530559657898187)
        ·
          refine ⟨32640458511795839486847281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21760305674530559657898187 32640458511795839486847281)
          ·
            refine ⟨24480343883846879615135461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32640458511795839486847281 24480343883846879615135461)
            ·
              refine ⟨4590064478221289927837899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24480343883846879615135461 4590064478221289927837899)
              ·
                refine ⟨6885096717331934891756849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4590064478221289927837899 6885096717331934891756849)
                ·
                  refine ⟨5163822537998951168817637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6885096717331934891756849 5163822537998951168817637)
                  ·
                    refine ⟨968216725874803344153307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5163822537998951168817637 968216725874803344153307)
                    ·
                      rfl

theorem cell23_5656786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_5656786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656786 prefixEnd_5656786 := by exact prefixLift 5656786
  have htrace : WordTrace (prefixWord ++ tailWord_5656786) baseStart_5656786 baseEnd_5656786 := by
    simpa [prefixWord, tailWord_5656786, baseEnd_5656786] using wordTrace_append hprefix tailTrace_5656786
  have hstable : (prefixWord ++ tailWord_5656786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656786).length < 2 ^ (prefixWord ++ tailWord_5656786).sum := by decide
  have hdescent : baseEnd_5656786 < baseStart_5656786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656813 : List Nat := [1, 5, 1, 2, 3, 1, 3, 1, 1, 2, 3]
def baseStart_5656813 : Nat := 118140960795 + 5656813 * 2 ^ 59
def prefixEnd_5656813 : Nat := 4983230072969 + 3 ^ 40 * 5656813 * 2
def baseEnd_5656813 : Nat := 2904664041602081426822297

theorem tailTrace_5656813 : CollatzResearch.WordTrace tailWord_5656813 prefixEnd_5656813 2904664041602081426822297 := by
  unfold tailWord_5656813
  simp only [CollatzResearch.WordTrace]
  refine ⟨206320920055340082589823093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137547280036893388393215395 206320920055340082589823093)
  ·
    refine ⟨19342586255188132742795915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206320920055340082589823093 19342586255188132742795915)
    ·
      refine ⟨29013879382782199114193873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19342586255188132742795915 29013879382782199114193873)
      ·
        refine ⟨21760409537086649335645405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29013879382782199114193873 21760409537086649335645405)
        ·
          refine ⟨8160153576407493500867027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21760409537086649335645405 8160153576407493500867027)
          ·
            refine ⟨12240230364611240251300541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8160153576407493500867027 12240230364611240251300541)
            ·
              refine ⟨4590086386729215094237703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12240230364611240251300541 4590086386729215094237703)
              ·
                refine ⟨6885129580093822641356555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4590086386729215094237703 6885129580093822641356555)
                ·
                  refine ⟨10327694370140733962034833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6885129580093822641356555 10327694370140733962034833)
                  ·
                    refine ⟨7745770777605550471526125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10327694370140733962034833 7745770777605550471526125)
                    ·
                      refine ⟨2904664041602081426822297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7745770777605550471526125 2904664041602081426822297)
                      ·
                        rfl

theorem cell23_5656813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_5656813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656813 prefixEnd_5656813 := by exact prefixLift 5656813
  have htrace : WordTrace (prefixWord ++ tailWord_5656813) baseStart_5656813 baseEnd_5656813 := by
    simpa [prefixWord, tailWord_5656813, baseEnd_5656813] using wordTrace_append hprefix tailTrace_5656813
  have hstable : (prefixWord ++ tailWord_5656813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656813).length < 2 ^ (prefixWord ++ tailWord_5656813).sum := by decide
  have hdescent : baseEnd_5656813 < baseStart_5656813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656822 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_5656822 : Nat := 118140960795 + 5656822 * 2 ^ 59
def prefixEnd_5656822 : Nat := 4983230072969 + 3 ^ 40 * 5656822 * 2
def baseEnd_5656822 : Nat := 2904668662927971891609755

theorem tailTrace_5656822 : CollatzResearch.WordTrace tailWord_5656822 prefixEnd_5656822 2904668662927971891609755 := by
  unfold tailWord_5656822
  simp only [CollatzResearch.WordTrace]
  refine ⟨12895078019519217320431295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137547498874871651417933813 12895078019519217320431295)
  ·
    refine ⟨19342617029278825980646943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12895078019519217320431295 19342617029278825980646943)
    ·
      refine ⟨29013925543918238970970415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19342617029278825980646943 29013925543918238970970415)
      ·
        refine ⟨43520888315877358456455623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29013925543918238970970415 43520888315877358456455623)
        ·
          refine ⟨65281332473816037684683435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43520888315877358456455623 65281332473816037684683435)
          ·
            refine ⟨97921998710724056527025153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65281332473816037684683435 97921998710724056527025153)
            ·
              refine ⟨73441499033043042395268865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97921998710724056527025153 73441499033043042395268865)
              ·
                refine ⟨55081124274782281796451649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73441499033043042395268865 55081124274782281796451649)
                ·
                  refine ⟨41310843206086711347338737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55081124274782281796451649 41310843206086711347338737)
                  ·
                    refine ⟨30983132404565033510504053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41310843206086711347338737 30983132404565033510504053)
                    ·
                      refine ⟨2904668662927971891609755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30983132404565033510504053 2904668662927971891609755)
                      ·
                        rfl

theorem cell23_5656822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_5656822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656822 prefixEnd_5656822 := by exact prefixLift 5656822
  have htrace : WordTrace (prefixWord ++ tailWord_5656822) baseStart_5656822 baseEnd_5656822 := by
    simpa [prefixWord, tailWord_5656822, baseEnd_5656822] using wordTrace_append hprefix tailTrace_5656822
  have hstable : (prefixWord ++ tailWord_5656822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656822).length < 2 ^ (prefixWord ++ tailWord_5656822).sum := by decide
  have hdescent : baseEnd_5656822 < baseStart_5656822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656826 : List Nat := [3, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3]
def baseStart_5656826 : Nat := 118140960795 + 5656826 * 2 ^ 59
def prefixEnd_5656826 : Nat := 4983230072969 + 3 ^ 40 * 5656826 * 2
def baseEnd_5656826 : Nat := 2904670716850589875959737

theorem tailTrace_5656826 : CollatzResearch.WordTrace tailWord_5656826 prefixEnd_5656826 2904670716850589875959737 := by
  unfold tailWord_5656826
  simp only [CollatzResearch.WordTrace]
  refine ⟨51580348551073246452511583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137547596136195323873364221 51580348551073246452511583)
  ·
    refine ⟨77370522826609869678767375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51580348551073246452511583 77370522826609869678767375)
    ·
      refine ⟨116055784239914804518151063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77370522826609869678767375 116055784239914804518151063)
      ·
        refine ⟨174083676359872206777226595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116055784239914804518151063 174083676359872206777226595)
        ·
          refine ⟨261125514539808310165839893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174083676359872206777226595 261125514539808310165839893)
          ·
            refine ⟨12240258494053514539023745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 261125514539808310165839893 12240258494053514539023745)
            ·
              refine ⟨9180193870540135904267809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12240258494053514539023745 9180193870540135904267809)
              ·
                refine ⟨6885145402905101928200857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9180193870540135904267809 6885145402905101928200857)
                ·
                  refine ⟨5163859052178826446150643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6885145402905101928200857 5163859052178826446150643)
                  ·
                    refine ⟨7745788578268239669225965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5163859052178826446150643 7745788578268239669225965)
                    ·
                      refine ⟨2904670716850589875959737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7745788578268239669225965 2904670716850589875959737)
                      ·
                        rfl

theorem cell23_5656826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3].length) (baseStart_5656826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656826 prefixEnd_5656826 := by exact prefixLift 5656826
  have htrace : WordTrace (prefixWord ++ tailWord_5656826) baseStart_5656826 baseEnd_5656826 := by
    simpa [prefixWord, tailWord_5656826, baseEnd_5656826] using wordTrace_append hprefix tailTrace_5656826
  have hstable : (prefixWord ++ tailWord_5656826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656826).length < 2 ^ (prefixWord ++ tailWord_5656826).sum := by decide
  have hdescent : baseEnd_5656826 < baseStart_5656826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656849 : List Nat := [1, 2, 2, 1, 1, 5, 1, 3, 1, 4, 2]
def baseStart_5656849 : Nat := 118140960795 + 5656849 * 2 ^ 59
def prefixEnd_5656849 : Nat := 4983230072969 + 3 ^ 40 * 5656849 * 2
def baseEnd_5656849 : Nat := 2904682526905643285972131

theorem tailTrace_5656849 : CollatzResearch.WordTrace tailWord_5656849 prefixEnd_5656849 2904682526905643285972131 := by
  unfold tailWord_5656849
  simp only [CollatzResearch.WordTrace]
  refine ⟨206322233083209660738133601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137548155388806440492089067 206322233083209660738133601)
  ·
    refine ⟨154741674812407245553600201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206322233083209660738133601 154741674812407245553600201)
    ·
      refine ⟨116056256109305434165200151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154741674812407245553600201 116056256109305434165200151)
      ·
        refine ⟨174084384163958151247800227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116056256109305434165200151 174084384163958151247800227)
        ·
          refine ⟨261126576245937226871700341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174084384163958151247800227 261126576245937226871700341)
          ·
            refine ⟨24480616523056615019221907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 261126576245937226871700341 24480616523056615019221907)
            ·
              refine ⟨36720924784584922528832861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24480616523056615019221907 36720924784584922528832861)
              ·
                refine ⟨13770346794219345948312323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36720924784584922528832861 13770346794219345948312323)
                ·
                  refine ⟨20655520191329018922468485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13770346794219345948312323 20655520191329018922468485)
                  ·
                    refine ⟨3872910035874191047962841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20655520191329018922468485 3872910035874191047962841)
                    ·
                      refine ⟨2904682526905643285972131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3872910035874191047962841 2904682526905643285972131)
                      ·
                        rfl

theorem cell23_5656849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 4, 2].length) (baseStart_5656849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656849 prefixEnd_5656849 := by exact prefixLift 5656849
  have htrace : WordTrace (prefixWord ++ tailWord_5656849) baseStart_5656849 baseEnd_5656849 := by
    simpa [prefixWord, tailWord_5656849, baseEnd_5656849] using wordTrace_append hprefix tailTrace_5656849
  have hstable : (prefixWord ++ tailWord_5656849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656849).length < 2 ^ (prefixWord ++ tailWord_5656849).sum := by decide
  have hdescent : baseEnd_5656849 < baseStart_5656849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656866 : List Nat := [3, 3, 1, 1, 3, 1, 2, 2, 1, 4, 2]
def baseStart_5656866 : Nat := 118140960795 + 5656866 * 2 ^ 59
def prefixEnd_5656866 : Nat := 4983230072969 + 3 ^ 40 * 5656866 * 2
def baseEnd_5656866 : Nat := 2904691256076769719459553

theorem tailTrace_5656866 : CollatzResearch.WordTrace tailWord_5656866 prefixEnd_5656866 2904691256076769719459553 := by
  unfold tailWord_5656866
  simp only [CollatzResearch.WordTrace]
  refine ⟨51580713281037018160375613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137548568749432048427668301 51580713281037018160375613)
  ·
    refine ⟨19342767480388881810140855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51580713281037018160375613 19342767480388881810140855)
    ·
      refine ⟨29014151220583322715211283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19342767480388881810140855 29014151220583322715211283)
      ·
        refine ⟨43521226830874984072816925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29014151220583322715211283 43521226830874984072816925)
        ·
          refine ⟨16320460061578119027306347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43521226830874984072816925 16320460061578119027306347)
          ·
            refine ⟨24480690092367178540959521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16320460061578119027306347 24480690092367178540959521)
            ·
              refine ⟨18360517569275383905719641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24480690092367178540959521 18360517569275383905719641)
              ·
                refine ⟨13770388176956537929289731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18360517569275383905719641 13770388176956537929289731)
                ·
                  refine ⟨20655582265434806893934597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13770388176956537929289731 20655582265434806893934597)
                  ·
                    refine ⟨3872921674769026292612737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20655582265434806893934597 3872921674769026292612737)
                    ·
                      refine ⟨2904691256076769719459553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3872921674769026292612737 2904691256076769719459553)
                      ·
                        rfl

theorem cell23_5656866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_5656866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656866 prefixEnd_5656866 := by exact prefixLift 5656866
  have htrace : WordTrace (prefixWord ++ tailWord_5656866) baseStart_5656866 baseEnd_5656866 := by
    simpa [prefixWord, tailWord_5656866, baseEnd_5656866] using wordTrace_append hprefix tailTrace_5656866
  have hstable : (prefixWord ++ tailWord_5656866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656866).length < 2 ^ (prefixWord ++ tailWord_5656866).sum := by decide
  have hdescent : baseEnd_5656866 < baseStart_5656866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656875 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 6]
def baseStart_5656875 : Nat := 118140960795 + 5656875 * 2 ^ 59
def prefixEnd_5656875 : Nat := 4983230072969 + 3 ^ 40 * 5656875 * 2
def baseEnd_5656875 : Nat := 2904695877402660184247011

theorem tailTrace_5656875 : CollatzResearch.WordTrace tailWord_5656875 prefixEnd_5656875 2904695877402660184247011 := by
  unfold tailWord_5656875
  simp only [CollatzResearch.WordTrace]
  refine ⟨206323181381115467178580079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137548787587410311452386719 206323181381115467178580079)
  ·
    refine ⟨309484772071673200767870119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206323181381115467178580079 309484772071673200767870119)
    ·
      refine ⟨464227158107509801151805179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309484772071673200767870119 464227158107509801151805179)
      ·
        refine ⟨696340737161264701727707769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464227158107509801151805179 696340737161264701727707769)
        ·
          refine ⟨522255552870948526295780827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 696340737161264701727707769 522255552870948526295780827)
          ·
            refine ⟨783383329306422789443671241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522255552870948526295780827 783383329306422789443671241)
            ·
              refine ⟨587537496979817092082753431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 783383329306422789443671241 587537496979817092082753431)
              ·
                refine ⟨881306245469725638124130147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587537496979817092082753431 881306245469725638124130147)
                ·
                  refine ⟨1321959368204588457186195221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881306245469725638124130147 1321959368204588457186195221)
                  ·
                    refine ⟨61966845384590083930602901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1321959368204588457186195221 61966845384590083930602901)
                    ·
                      refine ⟨2904695877402660184247011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61966845384590083930602901 2904695877402660184247011)
                      ·
                        rfl

theorem cell23_5656875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 6].length) (baseStart_5656875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656875 prefixEnd_5656875 := by exact prefixLift 5656875
  have htrace : WordTrace (prefixWord ++ tailWord_5656875) baseStart_5656875 baseEnd_5656875 := by
    simpa [prefixWord, tailWord_5656875, baseEnd_5656875] using wordTrace_append hprefix tailTrace_5656875
  have hstable : (prefixWord ++ tailWord_5656875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656875).length < 2 ^ (prefixWord ++ tailWord_5656875).sum := by decide
  have hdescent : baseEnd_5656875 < baseStart_5656875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656877 : List Nat := [1, 5, 3, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_5656877 : Nat := 118140960795 + 5656877 * 2 ^ 59
def prefixEnd_5656877 : Nat := 4983230072969 + 3 ^ 40 * 5656877 * 2
def baseEnd_5656877 : Nat := 2904696904363969176422003

theorem tailTrace_5656877 : CollatzResearch.WordTrace tailWord_5656877 prefixEnd_5656877 2904696904363969176422003 := by
  unfold tailWord_5656877
  simp only [CollatzResearch.WordTrace]
  refine ⟨206323254327108221520152885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137548836218072147680101923 206323254327108221520152885)
  ·
    refine ⟨19342805093166395767514333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206323254327108221520152885 19342805093166395767514333)
    ·
      refine ⟨7253551909937398412817875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19342805093166395767514333 7253551909937398412817875)
      ·
        refine ⟨10880327864906097619226813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7253551909937398412817875 10880327864906097619226813)
        ·
          refine ⟨4080122949339786607210055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10880327864906097619226813 4080122949339786607210055)
          ·
            refine ⟨6120184424009679910815083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4080122949339786607210055 6120184424009679910815083)
            ·
              refine ⟨9180276636014519866222625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6120184424009679910815083 9180276636014519866222625)
              ·
                refine ⟨6885207477010889899666969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9180276636014519866222625 6885207477010889899666969)
                ·
                  refine ⟨5163905607758167424750227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6885207477010889899666969 5163905607758167424750227)
                  ·
                    refine ⟨7745858411637251137125341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5163905607758167424750227 7745858411637251137125341)
                    ·
                      refine ⟨2904696904363969176422003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7745858411637251137125341 2904696904363969176422003)
                      ·
                        rfl

theorem cell23_5656877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_5656877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656877 prefixEnd_5656877 := by exact prefixLift 5656877
  have htrace : WordTrace (prefixWord ++ tailWord_5656877) baseStart_5656877 baseEnd_5656877 := by
    simpa [prefixWord, tailWord_5656877, baseEnd_5656877] using wordTrace_append hprefix tailTrace_5656877
  have hstable : (prefixWord ++ tailWord_5656877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656877).length < 2 ^ (prefixWord ++ tailWord_5656877).sum := by decide
  have hdescent : baseEnd_5656877 < baseStart_5656877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656889 : List Nat := [1, 2, 1, 6, 1, 2, 2, 1, 7]
def baseStart_5656889 : Nat := 118140960795 + 5656889 * 2 ^ 59
def prefixEnd_5656889 : Nat := 4983230072969 + 3 ^ 40 * 5656889 * 2
def baseEnd_5656889 : Nat := 322744785125758125496883

theorem tailTrace_5656889 : CollatzResearch.WordTrace tailWord_5656889 prefixEnd_5656889 322744785125758125496883 := by
  unfold tailWord_5656889
  simp only [CollatzResearch.WordTrace]
  refine ⟨206323692003064747569589721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137549128002043165046393147 206323692003064747569589721)
  ·
    refine ⟨154742769002298560677192291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206323692003064747569589721 154742769002298560677192291)
    ·
      refine ⟨232114153503447841015788437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154742769002298560677192291 232114153503447841015788437)
      ·
        refine ⟨10880350945474117547615083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 232114153503447841015788437 10880350945474117547615083)
        ·
          refine ⟨16320526418211176321422625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10880350945474117547615083 16320526418211176321422625)
          ·
            refine ⟨12240394813658382241066969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16320526418211176321422625 12240394813658382241066969)
            ·
              refine ⟨9180296110243786680800227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12240394813658382241066969 9180296110243786680800227)
              ·
                refine ⟨13770444165365680021200341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9180296110243786680800227 13770444165365680021200341)
                ·
                  refine ⟨322744785125758125496883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13770444165365680021200341 322744785125758125496883)
                  ·
                    rfl

theorem cell23_5656889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 7].length) (baseStart_5656889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656889 prefixEnd_5656889 := by exact prefixLift 5656889
  have htrace : WordTrace (prefixWord ++ tailWord_5656889) baseStart_5656889 baseEnd_5656889 := by
    simpa [prefixWord, tailWord_5656889, baseEnd_5656889] using wordTrace_append hprefix tailTrace_5656889
  have hstable : (prefixWord ++ tailWord_5656889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656889).length < 2 ^ (prefixWord ++ tailWord_5656889).sum := by decide
  have hdescent : baseEnd_5656889 < baseStart_5656889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5656900 : List Nat := [2, 3, 4, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_5656900 : Nat := 118140960795 + 5656900 * 2 ^ 59
def prefixEnd_5656900 : Nat := 4983230072969 + 3 ^ 40 * 5656900 * 2
def baseEnd_5656900 : Nat := 2904708714419022586434397

theorem tailTrace_5656900 : CollatzResearch.WordTrace tailWord_5656900 prefixEnd_5656900 2904708714419022586434397 := by
  unfold tailWord_5656900
  simp only [CollatzResearch.WordTrace]
  refine ⟨103162046603012448224120077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137549395470683264298826769 103162046603012448224120077)
  ·
    refine ⟨38685767476129668084045029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103162046603012448224120077 38685767476129668084045029)
    ·
      refine ⟨7253581401774312765758443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38685767476129668084045029 7253581401774312765758443)
      ·
        refine ⟨10880372102661469148637665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7253581401774312765758443 10880372102661469148637665)
        ·
          refine ⟨8160279076996101861478249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10880372102661469148637665 8160279076996101861478249)
          ·
            refine ⟨6120209307747076396108687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8160279076996101861478249 6120209307747076396108687)
            ·
              refine ⟨9180313961620614594163031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6120209307747076396108687 9180313961620614594163031)
              ·
                refine ⟨13770470942430921891244547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9180313961620614594163031 13770470942430921891244547)
                ·
                  refine ⟨20655706413646382836866821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13770470942430921891244547 20655706413646382836866821)
                  ·
                    refine ⟨3872944952558696781912529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20655706413646382836866821 3872944952558696781912529)
                    ·
                      refine ⟨2904708714419022586434397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3872944952558696781912529 2904708714419022586434397)
                      ·
                        rfl

theorem cell23_5656900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_5656900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5656900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5656900 prefixEnd_5656900 := by exact prefixLift 5656900
  have htrace : WordTrace (prefixWord ++ tailWord_5656900) baseStart_5656900 baseEnd_5656900 := by
    simpa [prefixWord, tailWord_5656900, baseEnd_5656900] using wordTrace_append hprefix tailTrace_5656900
  have hstable : (prefixWord ++ tailWord_5656900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5656900).length < 2 ^ (prefixWord ++ tailWord_5656900).sum := by decide
  have hdescent : baseEnd_5656900 < baseStart_5656900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5656900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657000 : List Nat := [2, 1, 6, 1, 1, 2, 1, 4, 1, 4]
def baseStart_5657000 : Nat := 118140960795 + 5657000 * 2 ^ 59
def prefixEnd_5657000 : Nat := 4983230072969 + 3 ^ 40 * 5657000 * 2
def baseEnd_5657000 : Nat := 968253354161490731727979

theorem tailTrace_5657000 : CollatzResearch.WordTrace tailWord_5657000 prefixEnd_5657000 968253354161490731727979 := by
  unfold tailWord_5657000
  simp only [CollatzResearch.WordTrace]
  refine ⟨103163870252831306763440227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137551827003775075684586969 103163870252831306763440227)
  ·
    refine ⟨154745805379246960145160341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103163870252831306763440227 154745805379246960145160341)
    ·
      refine ⟨7253709627152201256804391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 154745805379246960145160341 7253709627152201256804391)
      ·
        refine ⟨10880564440728301885206587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7253709627152201256804391 10880564440728301885206587)
        ·
          refine ⟨16320846661092452827809881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10880564440728301885206587 16320846661092452827809881)
          ·
            refine ⟨12240634995819339620857411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16320846661092452827809881 12240634995819339620857411)
            ·
              refine ⟨18360952493729009431286117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12240634995819339620857411 18360952493729009431286117)
              ·
                refine ⟨3442678592574189268366147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18360952493729009431286117 3442678592574189268366147)
                ·
                  refine ⟨5164017888861283902549221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3442678592574189268366147 5164017888861283902549221)
                  ·
                    refine ⟨968253354161490731727979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5164017888861283902549221 968253354161490731727979)
                    ·
                      rfl

theorem cell23_5657000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_5657000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657000 prefixEnd_5657000 := by exact prefixLift 5657000
  have htrace : WordTrace (prefixWord ++ tailWord_5657000) baseStart_5657000 baseEnd_5657000 := by
    simpa [prefixWord, tailWord_5657000, baseEnd_5657000] using wordTrace_append hprefix tailTrace_5657000
  have hstable : (prefixWord ++ tailWord_5657000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657000).length < 2 ^ (prefixWord ++ tailWord_5657000).sum := by decide
  have hdescent : baseEnd_5657000 < baseStart_5657000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657009 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 3, 5]
def baseStart_5657009 : Nat := 118140960795 + 5657009 * 2 ^ 59
def prefixEnd_5657009 : Nat := 4983230072969 + 3 ^ 40 * 5657009 * 2
def baseEnd_5657009 : Nat := 968254894603454219990465

theorem tailTrace_5657009 : CollatzResearch.WordTrace tailWord_5657009 prefixEnd_5657009 968254894603454219990465 := by
  unfold tailWord_5657009
  simp only [CollatzResearch.WordTrace]
  refine ⟨206328068762630008063958081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137552045841753338709305387 206328068762630008063958081)
  ·
    refine ⟨154746051571972506047968561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206328068762630008063958081 154746051571972506047968561)
    ·
      refine ⟨116059538678979379535976421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154746051571972506047968561 116059538678979379535976421)
      ·
        refine ⟨21761163502308633662995579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116059538678979379535976421 21761163502308633662995579)
        ·
          refine ⟨32641745253462950494493369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21761163502308633662995579 32641745253462950494493369)
          ·
            refine ⟨24481308940097212870870027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32641745253462950494493369 24481308940097212870870027)
            ·
              refine ⟨36721963410145819306305041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24481308940097212870870027 36721963410145819306305041)
              ·
                refine ⟨27541472557609364479728781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36721963410145819306305041 27541472557609364479728781)
                ·
                  refine ⟨10328052209103511679898293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27541472557609364479728781 10328052209103511679898293)
                  ·
                    refine ⟨968254894603454219990465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10328052209103511679898293 968254894603454219990465)
                    ·
                      rfl

theorem cell23_5657009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_5657009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657009 prefixEnd_5657009 := by exact prefixLift 5657009
  have htrace : WordTrace (prefixWord ++ tailWord_5657009) baseStart_5657009 baseEnd_5657009 := by
    simpa [prefixWord, tailWord_5657009, baseEnd_5657009] using wordTrace_append hprefix tailTrace_5657009
  have hstable : (prefixWord ++ tailWord_5657009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657009).length < 2 ^ (prefixWord ++ tailWord_5657009).sum := by decide
  have hdescent : baseEnd_5657009 < baseStart_5657009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657039 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 4, 4]
def baseStart_5657039 : Nat := 118140960795 + 5657039 * 2 ^ 59
def prefixEnd_5657039 : Nat := 4983230072969 + 3 ^ 40 * 5657039 * 2
def baseEnd_5657039 : Nat := 968260029409999180865419

theorem tailTrace_5657039 : CollatzResearch.WordTrace tailWord_5657039 prefixEnd_5657039 968260029409999180865419 := by
  unfold tailWord_5657039
  simp only [CollatzResearch.WordTrace]
  refine ⟨206329162952521323187550171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137552775301680882125033447 206329162952521323187550171)
  ·
    refine ⟨309493744428781984781325257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206329162952521323187550171 309493744428781984781325257)
    ·
      refine ⟨232120308321586488585993943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309493744428781984781325257 232120308321586488585993943)
      ·
        refine ⟨348180462482379732878990915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232120308321586488585993943 348180462482379732878990915)
        ·
          refine ⟨522270693723569599318486373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348180462482379732878990915 522270693723569599318486373)
          ·
            refine ⟨97925755073169299872216195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 522270693723569599318486373 97925755073169299872216195)
            ·
              refine ⟨146888632609753949808324293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97925755073169299872216195 146888632609753949808324293)
              ·
                refine ⟨27541618614328865589060805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146888632609753949808324293 27541618614328865589060805)
                ·
                  refine ⟨5164053490186662297948901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27541618614328865589060805 5164053490186662297948901)
                  ·
                    refine ⟨968260029409999180865419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5164053490186662297948901 968260029409999180865419)
                    ·
                      rfl

theorem cell23_5657039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 4].length) (baseStart_5657039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657039 prefixEnd_5657039 := by exact prefixLift 5657039
  have htrace : WordTrace (prefixWord ++ tailWord_5657039) baseStart_5657039 baseEnd_5657039 := by
    simpa [prefixWord, tailWord_5657039, baseEnd_5657039] using wordTrace_append hprefix tailTrace_5657039
  have hstable : (prefixWord ++ tailWord_5657039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657039).length < 2 ^ (prefixWord ++ tailWord_5657039).sum := by decide
  have hdescent : baseEnd_5657039 < baseStart_5657039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657049 : List Nat := [1, 2, 1, 2, 4, 1, 2, 3, 1, 1, 5]
def baseStart_5657049 : Nat := 118140960795 + 5657049 * 2 ^ 59
def prefixEnd_5657049 : Nat := 4983230072969 + 3 ^ 40 * 5657049 * 2
def baseEnd_5657049 : Nat := 2904785223036542503471211

theorem tailTrace_5657049 : CollatzResearch.WordTrace tailWord_5657049 prefixEnd_5657049 2904785223036542503471211 := by
  unfold tailWord_5657049
  simp only [CollatzResearch.WordTrace]
  refine ⟨206329527682485094895414201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137553018454990063263609467 206329527682485094895414201)
  ·
    refine ⟨154747145761863821171560651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206329527682485094895414201 154747145761863821171560651)
    ·
      refine ⟨232120718642795731757340977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154747145761863821171560651 232120718642795731757340977)
      ·
        refine ⟨174090538982096798818005733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232120718642795731757340977 174090538982096798818005733)
        ·
          refine ⟨32641976059143149778376075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174090538982096798818005733 32641976059143149778376075)
          ·
            refine ⟨48962964088714724667564113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32641976059143149778376075 48962964088714724667564113)
            ·
              refine ⟨36722223066536043500673085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48962964088714724667564113 36722223066536043500673085)
              ·
                refine ⟨13770833649951016312752407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36722223066536043500673085 13770833649951016312752407)
                ·
                  refine ⟨20656250474926524469128611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13770833649951016312752407 20656250474926524469128611)
                  ·
                    refine ⟨30984375712389786703692917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20656250474926524469128611 30984375712389786703692917)
                    ·
                      refine ⟨2904785223036542503471211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30984375712389786703692917 2904785223036542503471211)
                      ·
                        rfl

theorem cell23_5657049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_5657049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657049 prefixEnd_5657049 := by exact prefixLift 5657049
  have htrace : WordTrace (prefixWord ++ tailWord_5657049) baseStart_5657049 baseEnd_5657049 := by
    simpa [prefixWord, tailWord_5657049, baseEnd_5657049] using wordTrace_append hprefix tailTrace_5657049
  have hstable : (prefixWord ++ tailWord_5657049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657049).length < 2 ^ (prefixWord ++ tailWord_5657049).sum := by decide
  have hdescent : baseEnd_5657049 < baseStart_5657049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657066 : List Nat := [3, 1, 3, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_5657066 : Nat := 118140960795 + 5657066 * 2 ^ 59
def prefixEnd_5657066 : Nat := 4983230072969 + 3 ^ 40 * 5657066 * 2
def baseEnd_5657066 : Nat := 2904793952207668936958633

theorem tailTrace_5657066 : CollatzResearch.WordTrace tailWord_5657066 prefixEnd_5657066 2904793952207668936958633 := by
  unfold tailWord_5657066
  simp only [CollatzResearch.WordTrace]
  refine ⟨51582536930855876699695763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137553431815615671199188701 51582536930855876699695763)
  ·
    refine ⟨77373805396283815049543645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51582536930855876699695763 77373805396283815049543645)
    ·
      refine ⟨29015177023606430643578867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77373805396283815049543645 29015177023606430643578867)
      ·
        refine ⟨43522765535409645965368301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29015177023606430643578867 43522765535409645965368301)
        ·
          refine ⟨16321037075778617237013113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43522765535409645965368301 16321037075778617237013113)
          ·
            refine ⟨12240777806833962927759835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16321037075778617237013113 12240777806833962927759835)
            ·
              refine ⟨18361166710250944391639753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12240777806833962927759835 18361166710250944391639753)
              ·
                refine ⟨13770875032688208293729815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18361166710250944391639753 13770875032688208293729815)
                ·
                  refine ⟨20656312549032312440594723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13770875032688208293729815 20656312549032312440594723)
                  ·
                    refine ⟨30984468823548468660892085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20656312549032312440594723 30984468823548468660892085)
                    ·
                      refine ⟨2904793952207668936958633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30984468823548468660892085 2904793952207668936958633)
                      ·
                        rfl

theorem cell23_5657066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_5657066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657066 prefixEnd_5657066 := by exact prefixLift 5657066
  have htrace : WordTrace (prefixWord ++ tailWord_5657066) baseStart_5657066 baseEnd_5657066 := by
    simpa [prefixWord, tailWord_5657066, baseEnd_5657066] using wordTrace_append hprefix tailTrace_5657066
  have hstable : (prefixWord ++ tailWord_5657066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657066).length < 2 ^ (prefixWord ++ tailWord_5657066).sum := by decide
  have hdescent : baseEnd_5657066 < baseStart_5657066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657073 : List Nat := [1, 2, 2, 2, 3, 1, 5, 1, 2, 4]
def baseStart_5657073 : Nat := 118140960795 + 5657073 * 2 ^ 59
def prefixEnd_5657073 : Nat := 4983230072969 + 3 ^ 40 * 5657073 * 2
def baseEnd_5657073 : Nat := 968265848857416803190367

theorem tailTrace_5657073 : CollatzResearch.WordTrace tailWord_5657073 prefixEnd_5657073 968265848857416803190367 := by
  unfold tailWord_5657073
  simp only [CollatzResearch.WordTrace]
  refine ⟨206330403034398146994287873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137553602022932097996191915 206330403034398146994287873)
  ·
    refine ⟨154747802275798610245715905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206330403034398146994287873 154747802275798610245715905)
    ·
      refine ⟨116060851706848957684286929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154747802275798610245715905 116060851706848957684286929)
      ·
        refine ⟨87045638780136718263215197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116060851706848957684286929 87045638780136718263215197)
        ·
          refine ⟨32642114542551269348705699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87045638780136718263215197 32642114542551269348705699)
          ·
            refine ⟨48963171813826904023058549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32642114542551269348705699 48963171813826904023058549)
            ·
              refine ⟨4590297357546272252161739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48963171813826904023058549 4590297357546272252161739)
              ·
                refine ⟨6885446036319408378242609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4590297357546272252161739 6885446036319408378242609)
                ·
                  refine ⟨5164084527239556283681957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6885446036319408378242609 5164084527239556283681957)
                  ·
                    refine ⟨968265848857416803190367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5164084527239556283681957 968265848857416803190367)
                    ·
                      rfl

theorem cell23_5657073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 2, 4].length) (baseStart_5657073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657073 prefixEnd_5657073 := by exact prefixLift 5657073
  have htrace : WordTrace (prefixWord ++ tailWord_5657073) baseStart_5657073 baseEnd_5657073 := by
    simpa [prefixWord, tailWord_5657073, baseEnd_5657073] using wordTrace_append hprefix tailTrace_5657073
  have hstable : (prefixWord ++ tailWord_5657073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657073).length < 2 ^ (prefixWord ++ tailWord_5657073).sum := by decide
  have hdescent : baseEnd_5657073 < baseStart_5657073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657109 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_5657109 : Nat := 118140960795 + 5657109 * 2 ^ 59
def prefixEnd_5657109 : Nat := 4983230072969 + 3 ^ 40 * 5657109 * 2
def baseEnd_5657109 : Nat := 2904816031875812268720935

theorem tailTrace_5657109 : CollatzResearch.WordTrace tailWord_5657109 prefixEnd_5657109 2904816031875812268720935 := by
  unfold tailWord_5657109
  simp only [CollatzResearch.WordTrace]
  refine ⟨206331716062267725142598381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137554477374845150095065587 206331716062267725142598381)
  ·
    refine ⟨77374393523350396928474393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206331716062267725142598381 77374393523350396928474393)
    ·
      refine ⟨58030795142512797696355795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77374393523350396928474393 58030795142512797696355795)
      ·
        refine ⟨87046192713769196544533693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58030795142512797696355795 87046192713769196544533693)
        ·
          refine ⟨32642322267663448704200135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87046192713769196544533693 32642322267663448704200135)
          ·
            refine ⟨48963483401495173056300203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32642322267663448704200135 48963483401495173056300203)
            ·
              refine ⟨73445225102242759584450305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48963483401495173056300203 73445225102242759584450305)
              ·
                refine ⟨55083918826682069688337729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73445225102242759584450305 55083918826682069688337729)
                ·
                  refine ⟨41312939120011552266253297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55083918826682069688337729 41312939120011552266253297)
                  ·
                    refine ⟨30984704340008664199689973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41312939120011552266253297 30984704340008664199689973)
                    ·
                      refine ⟨2904816031875812268720935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30984704340008664199689973 2904816031875812268720935)
                      ·
                        rfl

theorem cell23_5657109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_5657109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657109 prefixEnd_5657109 := by exact prefixLift 5657109
  have htrace : WordTrace (prefixWord ++ tailWord_5657109) baseStart_5657109 baseEnd_5657109 := by
    simpa [prefixWord, tailWord_5657109, baseEnd_5657109] using wordTrace_append hprefix tailTrace_5657109
  have hstable : (prefixWord ++ tailWord_5657109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657109).length < 2 ^ (prefixWord ++ tailWord_5657109).sum := by decide
  have hdescent : baseEnd_5657109 < baseStart_5657109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657119 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 4]
def baseStart_5657119 : Nat := 118140960795 + 5657119 * 2 ^ 59
def prefixEnd_5657119 : Nat := 4983230072969 + 3 ^ 40 * 5657119 * 2
def baseEnd_5657119 : Nat := 2904821166682357229595889

theorem tailTrace_5657119 : CollatzResearch.WordTrace tailWord_5657119 prefixEnd_5657119 2904821166682357229595889 := by
  unfold tailWord_5657119
  simp only [CollatzResearch.WordTrace]
  refine ⟨206332080792231496850462411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137554720528154331233641607 206332080792231496850462411)
  ·
    refine ⟨309498121188347245275693617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206332080792231496850462411 309498121188347245275693617)
    ·
      refine ⟨232123590891260433956770213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309498121188347245275693617 232123590891260433956770213)
      ·
        refine ⟨43523173292111331366894415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232123590891260433956770213 43523173292111331366894415)
        ·
          refine ⟨65284759938166997050341623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43523173292111331366894415 65284759938166997050341623)
          ·
            refine ⟨97927139907250495575512435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65284759938166997050341623 97927139907250495575512435)
            ·
              refine ⟨146890709860875743363268653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97927139907250495575512435 146890709860875743363268653)
              ·
                refine ⟨55084016197828403761225745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146890709860875743363268653 55084016197828403761225745)
                ·
                  refine ⟨41313012148371302820919309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55084016197828403761225745 41313012148371302820919309)
                  ·
                    refine ⟨15492379555639238557844741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41313012148371302820919309 15492379555639238557844741)
                    ·
                      refine ⟨2904821166682357229595889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15492379555639238557844741 2904821166682357229595889)
                      ·
                        rfl

theorem cell23_5657119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_5657119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657119 prefixEnd_5657119 := by exact prefixLift 5657119
  have htrace : WordTrace (prefixWord ++ tailWord_5657119) baseStart_5657119 baseEnd_5657119 := by
    simpa [prefixWord, tailWord_5657119, baseEnd_5657119] using wordTrace_append hprefix tailTrace_5657119
  have hstable : (prefixWord ++ tailWord_5657119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657119).length < 2 ^ (prefixWord ++ tailWord_5657119).sum := by decide
  have hdescent : baseEnd_5657119 < baseStart_5657119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657124 : List Nat := [2, 3, 1, 5, 2, 1, 2, 1, 2, 4]
def baseStart_5657124 : Nat := 118140960795 + 5657124 * 2 ^ 59
def prefixEnd_5657124 : Nat := 4983230072969 + 3 ^ 40 * 5657124 * 2
def baseEnd_5657124 : Nat := 968274578028543236677789

theorem tailTrace_5657124 : CollatzResearch.WordTrace tailWord_5657124 prefixEnd_5657124 968274578028543236677789 := by
  unfold tailWord_5657124
  simp only [CollatzResearch.WordTrace]
  refine ⟨103166131578606691352197213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137554842104808921802929617 103166131578606691352197213)
  ·
    refine ⟨38687299341977509257073955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103166131578606691352197213 38687299341977509257073955)
    ·
      refine ⟨58030949012966263885610933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38687299341977509257073955 58030949012966263885610933)
      ·
        refine ⟨5440401469965587239276025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58030949012966263885610933 5440401469965587239276025)
        ·
          refine ⟨4080301102474190429457019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5440401469965587239276025 4080301102474190429457019)
          ·
            refine ⟨6120451653711285644185529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4080301102474190429457019 6120451653711285644185529)
            ·
              refine ⟨4590338740283464233139147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6120451653711285644185529 4590338740283464233139147)
              ·
                refine ⟨6885508110425196349708721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4590338740283464233139147 6885508110425196349708721)
                ·
                  refine ⟨5164131082818897262281541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6885508110425196349708721 5164131082818897262281541)
                  ·
                    refine ⟨968274578028543236677789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5164131082818897262281541 968274578028543236677789)
                    ·
                      rfl

theorem cell23_5657124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_5657124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657124 prefixEnd_5657124 := by exact prefixLift 5657124
  have htrace : WordTrace (prefixWord ++ tailWord_5657124) baseStart_5657124 baseEnd_5657124 := by
    simpa [prefixWord, tailWord_5657124, baseEnd_5657124] using wordTrace_append hprefix tailTrace_5657124
  have hstable : (prefixWord ++ tailWord_5657124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657124).length < 2 ^ (prefixWord ++ tailWord_5657124).sum := by decide
  have hdescent : baseEnd_5657124 < baseStart_5657124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657130 : List Nat := [3, 1, 4, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_5657130 : Nat := 118140960795 + 5657130 * 2 ^ 59
def prefixEnd_5657130 : Nat := 4983230072969 + 3 ^ 40 * 5657130 * 2
def baseEnd_5657130 : Nat := 2904826814969556686558339

theorem tailTrace_5657130 : CollatzResearch.WordTrace tailWord_5657130 prefixEnd_5657130 2904826814969556686558339 := by
  unfold tailWord_5657130
  simp only [CollatzResearch.WordTrace]
  refine ⟨51583120498797911432278211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137554987996794430486075229 51583120498797911432278211)
  ·
    refine ⟨77374680748196867148417317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51583120498797911432278211 77374680748196867148417317)
    ·
      refine ⟨14507752640286912590328247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77374680748196867148417317 14507752640286912590328247)
      ·
        refine ⟨21761628960430368885492371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14507752640286912590328247 21761628960430368885492371)
        ·
          refine ⟨32642443440645553328238557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21761628960430368885492371 32642443440645553328238557)
          ·
            refine ⟨12240916290242082498089459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32642443440645553328238557 12240916290242082498089459)
            ·
              refine ⟨18361374435363123747134189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12240916290242082498089459 18361374435363123747134189)
              ·
                refine ⟨6885515413261171405175321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18361374435363123747134189 6885515413261171405175321)
                ·
                  refine ⟨5164136559945878553881491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6885515413261171405175321 5164136559945878553881491)
                  ·
                    refine ⟨7746204839918817830822237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5164136559945878553881491 7746204839918817830822237)
                    ·
                      refine ⟨2904826814969556686558339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7746204839918817830822237 2904826814969556686558339)
                      ·
                        rfl

theorem cell23_5657130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_5657130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657130 prefixEnd_5657130 := by exact prefixLift 5657130
  have htrace : WordTrace (prefixWord ++ tailWord_5657130) baseStart_5657130 baseEnd_5657130 := by
    simpa [prefixWord, tailWord_5657130, baseEnd_5657130] using wordTrace_append hprefix tailTrace_5657130
  have hstable : (prefixWord ++ tailWord_5657130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657130).length < 2 ^ (prefixWord ++ tailWord_5657130).sum := by decide
  have hdescent : baseEnd_5657130 < baseStart_5657130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657139 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 5]
def baseStart_5657139 : Nat := 118140960795 + 5657139 * 2 ^ 59
def prefixEnd_5657139 : Nat := 4983230072969 + 3 ^ 40 * 5657139 * 2
def baseEnd_5657139 : Nat := 2904831436295447151345797

theorem tailTrace_5657139 : CollatzResearch.WordTrace tailWord_5657139 prefixEnd_5657139 2904831436295447151345797 := by
  unfold tailWord_5657139
  simp only [CollatzResearch.WordTrace]
  refine ⟨206332810252159040266190471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137555206834772693510793647 206332810252159040266190471)
  ·
    refine ⟨309499215378238560399285707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206332810252159040266190471 309499215378238560399285707)
    ·
      refine ⟨464248823067357840598928561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309499215378238560399285707 464248823067357840598928561)
      ·
        refine ⟨348186617300518380449196421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 464248823067357840598928561 348186617300518380449196421)
        ·
          refine ⟨65284990743847196334224329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 348186617300518380449196421 65284990743847196334224329)
          ·
            refine ⟨48963743057885397250668247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65284990743847196334224329 48963743057885397250668247)
            ·
              refine ⟨73445614586828095876002371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48963743057885397250668247 73445614586828095876002371)
              ·
                refine ⟨110168421880242143814003557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73445614586828095876002371 110168421880242143814003557)
                ·
                  refine ⟨20656579102545401965125667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110168421880242143814003557 20656579102545401965125667)
                  ·
                    refine ⟨30984868653818102947688501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20656579102545401965125667 30984868653818102947688501)
                    ·
                      refine ⟨2904831436295447151345797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30984868653818102947688501 2904831436295447151345797)
                      ·
                        rfl

theorem cell23_5657139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_5657139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657139 prefixEnd_5657139 := by exact prefixLift 5657139
  have htrace : WordTrace (prefixWord ++ tailWord_5657139) baseStart_5657139 baseEnd_5657139 := by
    simpa [prefixWord, tailWord_5657139, baseEnd_5657139] using wordTrace_append hprefix tailTrace_5657139
  have hstable : (prefixWord ++ tailWord_5657139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657139).length < 2 ^ (prefixWord ++ tailWord_5657139).sum := by decide
  have hdescent : baseEnd_5657139 < baseStart_5657139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657153 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_5657153 : Nat := 118140960795 + 5657153 * 2 ^ 59
def prefixEnd_5657153 : Nat := 4983230072969 + 3 ^ 40 * 5657153 * 2
def baseEnd_5657153 : Nat := 2904838625024610096570733

theorem tailTrace_5657153 : CollatzResearch.WordTrace tailWord_5657153 prefixEnd_5657153 2904838625024610096570733 := by
  unfold tailWord_5657153
  simp only [CollatzResearch.WordTrace]
  refine ⟨206333320874108320657200113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137555547249405547104800075 206333320874108320657200113)
  ·
    refine ⟨154749990655581240492900085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206333320874108320657200113 154749990655581240492900085)
    ·
      refine ⟨14507811623960741296209383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154749990655581240492900085 14507811623960741296209383)
      ·
        refine ⟨21761717435941111944314075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14507811623960741296209383 21761717435941111944314075)
        ·
          refine ⟨32642576153911667916471113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21761717435941111944314075 32642576153911667916471113)
          ·
            refine ⟨24481932115433750937353335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32642576153911667916471113 24481932115433750937353335)
            ·
              refine ⟨36722898173150626406030003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24481932115433750937353335 36722898173150626406030003)
              ·
                refine ⟨55084347259725939609045005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36722898173150626406030003 55084347259725939609045005)
                ·
                  refine ⟨20656630222397227353391877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55084347259725939609045005 20656630222397227353391877)
                  ·
                    refine ⟨3873118166699480128760977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20656630222397227353391877 3873118166699480128760977)
                    ·
                      refine ⟨2904838625024610096570733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3873118166699480128760977 2904838625024610096570733)
                      ·
                        rfl

theorem cell23_5657153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_5657153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657153 prefixEnd_5657153 := by exact prefixLift 5657153
  have htrace : WordTrace (prefixWord ++ tailWord_5657153) baseStart_5657153 baseEnd_5657153 := by
    simpa [prefixWord, tailWord_5657153, baseEnd_5657153] using wordTrace_append hprefix tailTrace_5657153
  have hstable : (prefixWord ++ tailWord_5657153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657153).length < 2 ^ (prefixWord ++ tailWord_5657153).sum := by decide
  have hdescent : baseEnd_5657153 < baseStart_5657153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657199 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 7]
def baseStart_5657199 : Nat := 118140960795 + 5657199 * 2 ^ 59
def prefixEnd_5657199 : Nat := 4983230072969 + 3 ^ 40 * 5657199 * 2
def baseEnd_5657199 : Nat := 2904862245134716916595521

theorem tailTrace_5657199 : CollatzResearch.WordTrace tailWord_5657199 prefixEnd_5657199 2904862245134716916595521 := by
  unfold tailWord_5657199
  simp only [CollatzResearch.WordTrace]
  refine ⟨206334998631941670513374651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137556665754627780342249767 206334998631941670513374651)
  ·
    refine ⟨309502497947912505770061977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206334998631941670513374651 309502497947912505770061977)
    ·
      refine ⟨232126873460934379327546483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309502497947912505770061977 232126873460934379327546483)
      ·
        refine ⟨348190310191401568991319725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232126873460934379327546483 348190310191401568991319725)
        ·
          refine ⟨130571366321775588371744897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348190310191401568991319725 130571366321775588371744897)
          ·
            refine ⟨97928524741331691278808673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130571366321775588371744897 97928524741331691278808673)
            ·
              refine ⟨73446393555998768459106505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97928524741331691278808673 73446393555998768459106505)
              ·
                refine ⟨55084795166999076344329879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73446393555998768459106505 55084795166999076344329879)
                ·
                  refine ⟨82627192750498614516494819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55084795166999076344329879 82627192750498614516494819)
                  ·
                    refine ⟨123940789125747921774742229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82627192750498614516494819 123940789125747921774742229)
                    ·
                      refine ⟨2904862245134716916595521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123940789125747921774742229 2904862245134716916595521)
                      ·
                        rfl

theorem cell23_5657199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_5657199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657199 prefixEnd_5657199 := by exact prefixLift 5657199
  have htrace : WordTrace (prefixWord ++ tailWord_5657199) baseStart_5657199 baseEnd_5657199 := by
    simpa [prefixWord, tailWord_5657199, baseEnd_5657199] using wordTrace_append hprefix tailTrace_5657199
  have hstable : (prefixWord ++ tailWord_5657199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657199).length < 2 ^ (prefixWord ++ tailWord_5657199).sum := by decide
  have hdescent : baseEnd_5657199 < baseStart_5657199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657300 : List Nat := [2, 4, 1, 3, 2, 1, 1, 3, 6]
def baseStart_5657300 : Nat := 118140960795 + 5657300 * 2 ^ 59
def prefixEnd_5657300 : Nat := 4983230072969 + 3 ^ 40 * 5657300 * 2
def baseEnd_5657300 : Nat := 322768234075646780159173

theorem tailTrace_5657300 : CollatzResearch.WordTrace tailWord_5657300 prefixEnd_5657300 322768234075646780159173 := by
  unfold tailWord_5657300
  simp only [CollatzResearch.WordTrace]
  refine ⟨103169341202287882381400677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137559121603050509841867569 103169341202287882381400677)
  ·
    refine ⟨19344251475428977946512627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103169341202287882381400677 19344251475428977946512627)
    ·
      refine ⟨29016377213143466919768941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19344251475428977946512627 29016377213143466919768941)
      ·
        refine ⟨10881141454928800094913353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29016377213143466919768941 10881141454928800094913353)
        ·
          refine ⟨8160856091196600071185015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10881141454928800094913353 8160856091196600071185015)
          ·
            refine ⟨12241284136794900106777523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8160856091196600071185015 12241284136794900106777523)
            ·
              refine ⟨18361926205192350160166285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12241284136794900106777523 18361926205192350160166285)
              ·
                refine ⟨6885722326947131310062357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18361926205192350160166285 6885722326947131310062357)
                ·
                  refine ⟨322768234075646780159173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6885722326947131310062357 322768234075646780159173)
                  ·
                    rfl

theorem cell23_5657300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_5657300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657300 prefixEnd_5657300 := by exact prefixLift 5657300
  have htrace : WordTrace (prefixWord ++ tailWord_5657300) baseStart_5657300 baseEnd_5657300 := by
    simpa [prefixWord, tailWord_5657300, baseEnd_5657300] using wordTrace_append hprefix tailTrace_5657300
  have hstable : (prefixWord ++ tailWord_5657300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657300).length < 2 ^ (prefixWord ++ tailWord_5657300).sum := by decide
  have hdescent : baseEnd_5657300 < baseStart_5657300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657313 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 3, 5]
def baseStart_5657313 : Nat := 118140960795 + 5657313 * 2 ^ 59
def prefixEnd_5657313 : Nat := 4983230072969 + 3 ^ 40 * 5657313 * 2
def baseEnd_5657313 : Nat := 968306927309776490189999

theorem tailTrace_5657313 : CollatzResearch.WordTrace tailWord_5657313 prefixEnd_5657313 968306927309776490189999 := by
  unfold tailWord_5657313
  simp only [CollatzResearch.WordTrace]
  refine ⟨206339156553528667983024593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137559437702352445322016395 206339156553528667983024593)
  ·
    refine ⟨154754367415146500987268445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206339156553528667983024593 154754367415146500987268445)
    ·
      refine ⟨58032887780679937870225667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154754367415146500987268445 58032887780679937870225667)
      ·
        refine ⟨87049331671019906805338501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58032887780679937870225667 87049331671019906805338501)
        ·
          refine ⟨16321749688316232526000969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87049331671019906805338501 16321749688316232526000969)
          ·
            refine ⟨12241312266237174394500727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16321749688316232526000969 12241312266237174394500727)
            ·
              refine ⟨18361968399355761591751091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12241312266237174394500727 18361968399355761591751091)
              ·
                refine ⟨27542952599033642387626637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18361968399355761591751091 27542952599033642387626637)
                ·
                  refine ⟨10328607224637615895359989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27542952599033642387626637 10328607224637615895359989)
                  ·
                    refine ⟨968306927309776490189999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10328607224637615895359989 968306927309776490189999)
                    ·
                      rfl

theorem cell23_5657313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_5657313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657313 prefixEnd_5657313 := by exact prefixLift 5657313
  have htrace : WordTrace (prefixWord ++ tailWord_5657313) baseStart_5657313 baseEnd_5657313 := by
    simpa [prefixWord, tailWord_5657313, baseEnd_5657313] using wordTrace_append hprefix tailTrace_5657313
  have hstable : (prefixWord ++ tailWord_5657313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657313).length < 2 ^ (prefixWord ++ tailWord_5657313).sum := by decide
  have hdescent : baseEnd_5657313 < baseStart_5657313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657353 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 3, 2, 3]
def baseStart_5657353 : Nat := 118140960795 + 5657353 * 2 ^ 59
def prefixEnd_5657353 : Nat := 4983230072969 + 3 ^ 40 * 5657353 * 2
def baseEnd_5657353 : Nat := 2904941321155509314069813

theorem tailTrace_5657353 : CollatzResearch.WordTrace tailWord_5657353 prefixEnd_5657353 2904941321155509314069813 := by
  unfold tailWord_5657353
  simp only [CollatzResearch.WordTrace]
  refine ⟨206340615473383754814480713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137560410315589169876320475 206340615473383754814480713)
  ·
    refine ⟨154755461605037816110860535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206340615473383754814480713 154755461605037816110860535)
    ·
      refine ⟨232133192407556724166290803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154755461605037816110860535 232133192407556724166290803)
      ·
        refine ⟨348199788611335086249436205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232133192407556724166290803 348199788611335086249436205)
        ·
          refine ⟨130574920729250657343538577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348199788611335086249436205 130574920729250657343538577)
          ·
            refine ⟨97931190546937993007653933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130574920729250657343538577 97931190546937993007653933)
            ·
              refine ⟨36724196455101747377870225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97931190546937993007653933 36724196455101747377870225)
              ·
                refine ⟨27543147341326310533402669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36724196455101747377870225 27543147341326310533402669)
                ·
                  refine ⟨10328680252997366450026001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27543147341326310533402669 10328680252997366450026001)
                  ·
                    refine ⟨7746510189748024837519501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10328680252997366450026001 7746510189748024837519501)
                    ·
                      refine ⟨2904941321155509314069813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7746510189748024837519501 2904941321155509314069813)
                      ·
                        rfl

theorem cell23_5657353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 2, 3].length) (baseStart_5657353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657353 prefixEnd_5657353 := by exact prefixLift 5657353
  have htrace : WordTrace (prefixWord ++ tailWord_5657353) baseStart_5657353 baseEnd_5657353 := by
    simpa [prefixWord, tailWord_5657353, baseEnd_5657353] using wordTrace_append hprefix tailTrace_5657353
  have hstable : (prefixWord ++ tailWord_5657353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657353).length < 2 ^ (prefixWord ++ tailWord_5657353).sum := by decide
  have hdescent : baseEnd_5657353 < baseStart_5657353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657363 : List Nat := [1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 4]
def baseStart_5657363 : Nat := 118140960795 + 5657363 * 2 ^ 59
def prefixEnd_5657363 : Nat := 4983230072969 + 3 ^ 40 * 5657363 * 2
def baseEnd_5657363 : Nat := 2904946455962054274944767

theorem tailTrace_5657363 : CollatzResearch.WordTrace tailWord_5657363 prefixEnd_5657363 2904946455962054274944767 := by
  unfold tailWord_5657363
  simp only [CollatzResearch.WordTrace]
  refine ⟨206340980203347526522344743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137560653468898351014896495 206340980203347526522344743)
  ·
    refine ⟨309511470305021289783517115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206340980203347526522344743 309511470305021289783517115)
    ·
      refine ⟨464267205457531934675275673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309511470305021289783517115 464267205457531934675275673)
      ·
        refine ⟨348200404093148951006456755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 464267205457531934675275673 348200404093148951006456755)
        ·
          refine ⟨522300606139723426509685133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348200404093148951006456755 522300606139723426509685133)
          ·
            refine ⟨195862727302396284941131925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 522300606139723426509685133 195862727302396284941131925)
            ·
              refine ⟨9181065342299825856615559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 195862727302396284941131925 9181065342299825856615559)
              ·
                refine ⟨13771598013449738784923339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9181065342299825856615559 13771598013449738784923339)
                ·
                  refine ⟨20657397020174608177385009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13771598013449738784923339 20657397020174608177385009)
                  ·
                    refine ⟨15493047765130956133038757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20657397020174608177385009 15493047765130956133038757)
                    ·
                      refine ⟨2904946455962054274944767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15493047765130956133038757 2904946455962054274944767)
                      ·
                        rfl

theorem cell23_5657363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 4].length) (baseStart_5657363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657363 prefixEnd_5657363 := by exact prefixLift 5657363
  have htrace : WordTrace (prefixWord ++ tailWord_5657363) baseStart_5657363 baseEnd_5657363 := by
    simpa [prefixWord, tailWord_5657363, baseEnd_5657363] using wordTrace_append hprefix tailTrace_5657363
  have hstable : (prefixWord ++ tailWord_5657363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657363).length < 2 ^ (prefixWord ++ tailWord_5657363).sum := by decide
  have hdescent : baseEnd_5657363 < baseStart_5657363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657370 : List Nat := [3, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3]
def baseStart_5657370 : Nat := 118140960795 + 5657370 * 2 ^ 59
def prefixEnd_5657370 : Nat := 4983230072969 + 3 ^ 40 * 5657370 * 2
def baseEnd_5657370 : Nat := 2904950050326635747557235

theorem tailTrace_5657370 : CollatzResearch.WordTrace tailWord_5657370 prefixEnd_5657370 2904950050326635747557235 := by
  unfold tailWord_5657370
  simp only [CollatzResearch.WordTrace]
  refine ⟨51585308878580541679462391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137560823676214777811899709 51585308878580541679462391)
  ·
    refine ⟨77377963317870812519193587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51585308878580541679462391 77377963317870812519193587)
    ·
      refine ⟨116066944976806218778790381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77377963317870812519193587 116066944976806218778790381)
      ·
        refine ⟨43525104366302332042046393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116066944976806218778790381 43525104366302332042046393)
        ·
          refine ⟨32643828274726749031534795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43525104366302332042046393 32643828274726749031534795)
          ·
            refine ⟨48965742412090123547302193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32643828274726749031534795 48965742412090123547302193)
            ·
              refine ⟨36724306809067592660476645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48965742412090123547302193 36724306809067592660476645)
              ·
                refine ⟨6885807526700173623839371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36724306809067592660476645 6885807526700173623839371)
                ·
                  refine ⟨10328711290050260435759057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6885807526700173623839371 10328711290050260435759057)
                  ·
                    refine ⟨7746533467537695326819293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10328711290050260435759057 7746533467537695326819293)
                    ·
                      refine ⟨2904950050326635747557235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7746533467537695326819293 2904950050326635747557235)
                      ·
                        rfl

theorem cell23_5657370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_5657370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657370 prefixEnd_5657370 := by exact prefixLift 5657370
  have htrace : WordTrace (prefixWord ++ tailWord_5657370) baseStart_5657370 baseEnd_5657370 := by
    simpa [prefixWord, tailWord_5657370, baseEnd_5657370] using wordTrace_append hprefix tailTrace_5657370
  have hstable : (prefixWord ++ tailWord_5657370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657370).length < 2 ^ (prefixWord ++ tailWord_5657370).sum := by decide
  have hdescent : baseEnd_5657370 < baseStart_5657370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657400 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 4, 1, 3]
def baseStart_5657400 : Nat := 118140960795 + 5657400 * 2 ^ 59
def prefixEnd_5657400 : Nat := 4983230072969 + 3 ^ 40 * 5657400 * 2
def baseEnd_5657400 : Nat := 2904965454746270630182097

theorem tailTrace_5657400 : CollatzResearch.WordTrace tailWord_5657400 prefixEnd_5657400 2904965454746270630182097 := by
  unfold tailWord_5657400
  simp only [CollatzResearch.WordTrace]
  refine ⟨103171164852106740920720827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137561553136142321227627769 103171164852106740920720827)
  ·
    refine ⟨154756747278160111381081241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103171164852106740920720827 154756747278160111381081241)
    ·
      refine ⟨116067560458620083535810931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154756747278160111381081241 116067560458620083535810931)
      ·
        refine ⟨174101340687930125303716397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116067560458620083535810931 174101340687930125303716397)
        ·
          refine ⟨65288002757973796988893649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174101340687930125303716397 65288002757973796988893649)
          ·
            refine ⟨48966002068480347741670237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65288002757973796988893649 48966002068480347741670237)
            ·
              refine ⟨18362250775680130403126339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48966002068480347741670237 18362250775680130403126339)
              ·
                refine ⟨27543376163520195604689509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18362250775680130403126339 27543376163520195604689509)
                ·
                  refine ⟨5164383030660036675879283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27543376163520195604689509 5164383030660036675879283)
                  ·
                    refine ⟨7746574545990055013818925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5164383030660036675879283 7746574545990055013818925)
                    ·
                      refine ⟨2904965454746270630182097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7746574545990055013818925 2904965454746270630182097)
                      ·
                        rfl

theorem cell23_5657400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 4, 1, 3].length) (baseStart_5657400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657400 prefixEnd_5657400 := by exact prefixLift 5657400
  have htrace : WordTrace (prefixWord ++ tailWord_5657400) baseStart_5657400 baseEnd_5657400 := by
    simpa [prefixWord, tailWord_5657400, baseEnd_5657400] using wordTrace_append hprefix tailTrace_5657400
  have hstable : (prefixWord ++ tailWord_5657400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657400).length < 2 ^ (prefixWord ++ tailWord_5657400).sum := by decide
  have hdescent : baseEnd_5657400 < baseStart_5657400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657440 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 3, 4, 2]
def baseStart_5657440 : Nat := 118140960795 + 5657440 * 2 ^ 59
def prefixEnd_5657440 : Nat := 4983230072969 + 3 ^ 40 * 5657440 * 2
def baseEnd_5657440 : Nat := 2904985993972450473681913

theorem tailTrace_5657440 : CollatzResearch.WordTrace tailWord_5657440 prefixEnd_5657440 2904985993972450473681913 := by
  unfold tailWord_5657440
  simp only [CollatzResearch.WordTrace]
  refine ⟨103171894312034284336448887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137562525749379045781931849 103171894312034284336448887)
  ·
    refine ⟨154757841468051426504673331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103171894312034284336448887 154757841468051426504673331)
    ·
      refine ⟨232136762202077139757009997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154757841468051426504673331 232136762202077139757009997)
      ·
        refine ⟨87051285825778927408878749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232136762202077139757009997 87051285825778927408878749)
        ·
          refine ⟨32644232184667097778329531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87051285825778927408878749 32644232184667097778329531)
          ·
            refine ⟨48966348277000646667494297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32644232184667097778329531 48966348277000646667494297)
            ·
              refine ⟨36724761207750485000620723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48966348277000646667494297 36724761207750485000620723)
              ·
                refine ⟨55087141811625727500931085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36724761207750485000620723 55087141811625727500931085)
                ·
                  refine ⟨20657678179359647812849157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55087141811625727500931085 20657678179359647812849157)
                  ·
                    refine ⟨3873314658629933964909217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20657678179359647812849157 3873314658629933964909217)
                    ·
                      refine ⟨2904985993972450473681913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3873314658629933964909217 2904985993972450473681913)
                      ·
                        rfl

theorem cell23_5657440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_5657440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657440 prefixEnd_5657440 := by exact prefixLift 5657440
  have htrace : WordTrace (prefixWord ++ tailWord_5657440) baseStart_5657440 baseEnd_5657440 := by
    simpa [prefixWord, tailWord_5657440, baseEnd_5657440] using wordTrace_append hprefix tailTrace_5657440
  have hstable : (prefixWord ++ tailWord_5657440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657440).length < 2 ^ (prefixWord ++ tailWord_5657440).sum := by decide
  have hdescent : baseEnd_5657440 < baseStart_5657440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657443 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 5]
def baseStart_5657443 : Nat := 118140960795 + 5657443 * 2 ^ 59
def prefixEnd_5657443 : Nat := 4983230072969 + 3 ^ 40 * 5657443 * 2
def baseEnd_5657443 : Nat := 2904987534414413961944399

theorem tailTrace_5657443 : CollatzResearch.WordTrace tailWord_5657443 prefixEnd_5657443 2904987534414413961944399 := by
  unfold tailWord_5657443
  simp only [CollatzResearch.WordTrace]
  refine ⟨206343898043057700185256983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137562598695371800123504655 206343898043057700185256983)
  ·
    refine ⟨309515847064586550277885475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206343898043057700185256983 309515847064586550277885475)
    ·
      refine ⟨464273770596879825416828213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309515847064586550277885475 464273770596879825416828213)
      ·
        refine ⟨43525665993457483632827645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 464273770596879825416828213 43525665993457483632827645)
        ·
          refine ⟨16322124747546556362310367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43525665993457483632827645 16322124747546556362310367)
          ·
            refine ⟨24483187121319834543465551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16322124747546556362310367 24483187121319834543465551)
            ·
              refine ⟨36724780681979751815198327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24483187121319834543465551 36724780681979751815198327)
              ·
                refine ⟨55087171022969627722797491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36724780681979751815198327 55087171022969627722797491)
                ·
                  refine ⟨82630756534454441584196237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55087171022969627722797491 82630756534454441584196237)
                  ·
                    refine ⟨30986533700420415594073589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82630756534454441584196237 30986533700420415594073589)
                    ·
                      refine ⟨2904987534414413961944399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30986533700420415594073589 2904987534414413961944399)
                      ·
                        rfl

theorem cell23_5657443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_5657443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657443 prefixEnd_5657443 := by exact prefixLift 5657443
  have htrace : WordTrace (prefixWord ++ tailWord_5657443) baseStart_5657443 baseEnd_5657443 := by
    simpa [prefixWord, tailWord_5657443, baseEnd_5657443] using wordTrace_append hprefix tailTrace_5657443
  have hstable : (prefixWord ++ tailWord_5657443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657443).length < 2 ^ (prefixWord ++ tailWord_5657443).sum := by decide
  have hdescent : baseEnd_5657443 < baseStart_5657443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657457 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 4, 2, 2]
def baseStart_5657457 : Nat := 118140960795 + 5657457 * 2 ^ 59
def prefixEnd_5657457 : Nat := 4983230072969 + 3 ^ 40 * 5657457 * 2
def baseEnd_5657457 : Nat := 2904994723143576907169335

theorem tailTrace_5657457 : CollatzResearch.WordTrace tailWord_5657457 prefixEnd_5657457 2904994723143576907169335 := by
  unfold tailWord_5657457
  simp only [CollatzResearch.WordTrace]
  refine ⟨206344408665006980576266625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137562939110004653717511083 206344408665006980576266625)
  ·
    refine ⟨154758306498755235432199969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206344408665006980576266625 154758306498755235432199969)
    ·
      refine ⟨116068729874066426574149977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154758306498755235432199969 116068729874066426574149977)
      ·
        refine ⟨87051547405549819930612483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116068729874066426574149977 87051547405549819930612483)
        ·
          refine ⟨130577321108324729895918725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87051547405549819930612483 130577321108324729895918725)
          ·
            refine ⟨24483247707810886855484761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130577321108324729895918725 24483247707810886855484761)
            ·
              refine ⟨18362435780858165141613571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24483247707810886855484761 18362435780858165141613571)
              ·
                refine ⟨27543653671287247712420357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18362435780858165141613571 27543653671287247712420357)
                ·
                  refine ⟨5164435063366358946078817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27543653671287247712420357 5164435063366358946078817)
                  ·
                    refine ⟨3873326297524769209559113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5164435063366358946078817 3873326297524769209559113)
                    ·
                      refine ⟨2904994723143576907169335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3873326297524769209559113 2904994723143576907169335)
                      ·
                        rfl

theorem cell23_5657457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_5657457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657457 prefixEnd_5657457 := by exact prefixLift 5657457
  have htrace : WordTrace (prefixWord ++ tailWord_5657457) baseStart_5657457 baseEnd_5657457 := by
    simpa [prefixWord, tailWord_5657457, baseEnd_5657457] using wordTrace_append hprefix tailTrace_5657457
  have hstable : (prefixWord ++ tailWord_5657457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657457).length < 2 ^ (prefixWord ++ tailWord_5657457).sum := by decide
  have hdescent : baseEnd_5657457 < baseStart_5657457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657494 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_5657494 : Nat := 118140960795 + 5657494 * 2 ^ 59
def prefixEnd_5657494 : Nat := 4983230072969 + 3 ^ 40 * 5657494 * 2
def baseEnd_5657494 : Nat := 2905013721927793262406665

theorem tailTrace_5657494 : CollatzResearch.WordTrace tailWord_5657494 prefixEnd_5657494 2905013721927793262406665 := by
  unfold tailWord_5657494
  simp only [CollatzResearch.WordTrace]
  refine ⟨12896609885367058493460221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137563838777248623930242357 12896609885367058493460221)
  ·
    refine ⟨4836228707012646935047583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12896609885367058493460221 4836228707012646935047583)
    ·
      refine ⟨7254343060518970402571375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4836228707012646935047583 7254343060518970402571375)
      ·
        refine ⟨10881514590778455603857063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7254343060518970402571375 10881514590778455603857063)
        ·
          refine ⟨16322271886167683405785595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10881514590778455603857063 16322271886167683405785595)
          ·
            refine ⟨24483407829251525108678393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16322271886167683405785595 24483407829251525108678393)
            ·
              refine ⟨18362555871938643831508795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24483407829251525108678393 18362555871938643831508795)
              ·
                refine ⟨27543833807907965747263193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18362555871938643831508795 27543833807907965747263193)
                ·
                  refine ⟨20657875355930974310447395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27543833807907965747263193 20657875355930974310447395)
                  ·
                    refine ⟨30986813033896461465671093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20657875355930974310447395 30986813033896461465671093)
                    ·
                      refine ⟨2905013721927793262406665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30986813033896461465671093 2905013721927793262406665)
                      ·
                        rfl

theorem cell23_5657494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_5657494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657494 prefixEnd_5657494 := by exact prefixLift 5657494
  have htrace : WordTrace (prefixWord ++ tailWord_5657494) baseStart_5657494 baseEnd_5657494 := by
    simpa [prefixWord, tailWord_5657494, baseEnd_5657494] using wordTrace_append hprefix tailTrace_5657494
  have hstable : (prefixWord ++ tailWord_5657494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657494).length < 2 ^ (prefixWord ++ tailWord_5657494).sum := by decide
  have hdescent : baseEnd_5657494 < baseStart_5657494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657524 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_5657524 : Nat := 118140960795 + 5657524 * 2 ^ 59
def prefixEnd_5657524 : Nat := 4983230072969 + 3 ^ 40 * 5657524 * 2
def baseEnd_5657524 : Nat := 2905029126347428145031527

theorem tailTrace_5657524 : CollatzResearch.WordTrace tailWord_5657524 prefixEnd_5657524 2905029126347428145031527 := by
  unfold tailWord_5657524
  simp only [CollatzResearch.WordTrace]
  refine ⟨103173426177882125509477813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137564568237176167345970417 103173426177882125509477813)
  ·
    refine ⟨9672508704176449266513545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103173426177882125509477813 9672508704176449266513545)
    ·
      refine ⟨7254381528132336949885159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9672508704176449266513545 7254381528132336949885159)
      ·
        refine ⟨10881572292198505424827739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7254381528132336949885159 10881572292198505424827739)
        ·
          refine ⟨16322358438297758137241609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10881572292198505424827739 16322358438297758137241609)
          ·
            refine ⟨12241768828723318602931207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16322358438297758137241609 12241768828723318602931207)
            ·
              refine ⟨18362653243084977904396811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12241768828723318602931207 18362653243084977904396811)
              ·
                refine ⟨27543979864627466856595217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18362653243084977904396811 27543979864627466856595217)
                ·
                  refine ⟨20657984898470600142446413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27543979864627466856595217 20657984898470600142446413)
                  ·
                    refine ⟨7746744336926475053417405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20657984898470600142446413 7746744336926475053417405)
                    ·
                      refine ⟨2905029126347428145031527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7746744336926475053417405 2905029126347428145031527)
                      ·
                        rfl

theorem cell23_5657524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_5657524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657524 prefixEnd_5657524 := by exact prefixLift 5657524
  have htrace : WordTrace (prefixWord ++ tailWord_5657524) baseStart_5657524 baseEnd_5657524 := by
    simpa [prefixWord, tailWord_5657524, baseEnd_5657524] using wordTrace_append hprefix tailTrace_5657524
  have hstable : (prefixWord ++ tailWord_5657524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657524).length < 2 ^ (prefixWord ++ tailWord_5657524).sum := by decide
  have hdescent : baseEnd_5657524 < baseStart_5657524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657544 : List Nat := [2, 1, 3, 1, 6, 1, 1, 1, 2, 5]
def baseStart_5657544 : Nat := 118140960795 + 5657544 * 2 ^ 59
def prefixEnd_5657544 : Nat := 4983230072969 + 3 ^ 40 * 5657544 * 2
def baseEnd_5657544 : Nat := 968346465320172688927145

theorem tailTrace_5657544 : CollatzResearch.WordTrace tailWord_5657544 prefixEnd_5657544 968346465320172688927145 := by
  unfold tailWord_5657544
  simp only [CollatzResearch.WordTrace]
  refine ⟨103173790907845897217341843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137565054543794529623122457 103173790907845897217341843)
  ·
    refine ⟨154760686361768845826012765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103173790907845897217341843 154760686361768845826012765)
    ·
      refine ⟨58035257385663317184754787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154760686361768845826012765 58035257385663317184754787)
      ·
        refine ⟨87052886078494975777132181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58035257385663317184754787 87052886078494975777132181)
        ·
          refine ⟨4080604034929451989553071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 87052886078494975777132181 4080604034929451989553071)
          ·
            refine ⟨6120906052394177984329607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4080604034929451989553071 6120906052394177984329607)
            ·
              refine ⟨9181359078591266976494411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6120906052394177984329607 9181359078591266976494411)
              ·
                refine ⟨13772038617886900464741617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9181359078591266976494411 13772038617886900464741617)
                ·
                  refine ⟨10329028963415175348556213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13772038617886900464741617 10329028963415175348556213)
                  ·
                    refine ⟨968346465320172688927145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10329028963415175348556213 968346465320172688927145)
                    ·
                      rfl

theorem cell23_5657544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_5657544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657544 prefixEnd_5657544 := by exact prefixLift 5657544
  have htrace : WordTrace (prefixWord ++ tailWord_5657544) baseStart_5657544 baseEnd_5657544 := by
    simpa [prefixWord, tailWord_5657544, baseEnd_5657544] using wordTrace_append hprefix tailTrace_5657544
  have hstable : (prefixWord ++ tailWord_5657544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657544).length < 2 ^ (prefixWord ++ tailWord_5657544).sum := by decide
  have hdescent : baseEnd_5657544 < baseStart_5657544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657547 : List Nat := [1, 1, 1, 1, 3, 7, 1, 1, 2, 1, 4]
def baseStart_5657547 : Nat := 118140960795 + 5657547 * 2 ^ 59
def prefixEnd_5657547 : Nat := 4983230072969 + 3 ^ 40 * 5657547 * 2
def baseEnd_5657547 : Nat := 2905040936402481555043921

theorem tailTrace_5657547 : CollatzResearch.WordTrace tailWord_5657547 prefixEnd_5657547 2905040936402481555043921 := by
  unfold tailWord_5657547
  simp only [CollatzResearch.WordTrace]
  refine ⟨206347691234680925947042895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137565127489787283964695263 206347691234680925947042895)
  ·
    refine ⟨309521536852021388920564343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206347691234680925947042895 309521536852021388920564343)
    ·
      refine ⟨464282305278032083380846515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309521536852021388920564343 464282305278032083380846515)
      ·
        refine ⟨696423457917048125071269773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464282305278032083380846515 696423457917048125071269773)
        ·
          refine ⟨261158796718893046901726165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 696423457917048125071269773 261158796718893046901726165)
          ·
            refine ⟨6120909298099055786759207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 261158796718893046901726165 6120909298099055786759207)
            ·
              refine ⟨9181363947148583680138811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6120909298099055786759207 9181363947148583680138811)
              ·
                refine ⟨13772045920722875520208217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9181363947148583680138811 13772045920722875520208217)
                ·
                  refine ⟨10329034440542156640156163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13772045920722875520208217 10329034440542156640156163)
                  ·
                    refine ⟨15493551660813234960234245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10329034440542156640156163 15493551660813234960234245)
                    ·
                      refine ⟨2905040936402481555043921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15493551660813234960234245 2905040936402481555043921)
                      ·
                        rfl

theorem cell23_5657547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 1, 4].length) (baseStart_5657547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657547 prefixEnd_5657547 := by exact prefixLift 5657547
  have htrace : WordTrace (prefixWord ++ tailWord_5657547) baseStart_5657547 baseEnd_5657547 := by
    simpa [prefixWord, tailWord_5657547, baseEnd_5657547] using wordTrace_append hprefix tailTrace_5657547
  have hstable : (prefixWord ++ tailWord_5657547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657547).length < 2 ^ (prefixWord ++ tailWord_5657547).sum := by decide
  have hdescent : baseEnd_5657547 < baseStart_5657547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657553 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 8]
def baseStart_5657553 : Nat := 118140960795 + 5657553 * 2 ^ 59
def prefixEnd_5657553 : Nat := 4983230072969 + 3 ^ 40 * 5657553 * 2
def baseEnd_5657553 : Nat := 322782668587378725729877

theorem tailTrace_5657553 : CollatzResearch.WordTrace tailWord_5657553 prefixEnd_5657553 322782668587378725729877 := by
  unfold tailWord_5657553
  simp only [CollatzResearch.WordTrace]
  refine ⟨206347910072659188971761313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137565273381772792647840875 206347910072659188971761313)
  ·
    refine ⟨154760932554494391728820985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206347910072659188971761313 154760932554494391728820985)
    ·
      refine ⟨116070699415870793796615739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154760932554494391728820985 116070699415870793796615739)
      ·
        refine ⟨174106049123806190694923609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116070699415870793796615739 174106049123806190694923609)
        ·
          refine ⟨130579536842854643021192707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174106049123806190694923609 130579536842854643021192707)
          ·
            refine ⟨195869305264281964531789061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130579536842854643021192707 195869305264281964531789061)
            ·
              refine ⟨36725494737052868349710449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195869305264281964531789061 36725494737052868349710449)
              ·
                refine ⟨27544121052789651262282837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36725494737052868349710449 27544121052789651262282837)
                ·
                  refine ⟨322782668587378725729877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27544121052789651262282837 322782668587378725729877)
                  ·
                    rfl

theorem cell23_5657553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 8].length) (baseStart_5657553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657553 prefixEnd_5657553 := by exact prefixLift 5657553
  have htrace : WordTrace (prefixWord ++ tailWord_5657553) baseStart_5657553 baseEnd_5657553 := by
    simpa [prefixWord, tailWord_5657553, baseEnd_5657553] using wordTrace_append hprefix tailTrace_5657553
  have hstable : (prefixWord ++ tailWord_5657553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657553).length < 2 ^ (prefixWord ++ tailWord_5657553).sum := by decide
  have hdescent : baseEnd_5657553 < baseStart_5657553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657607 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 1, 5, 2]
def baseStart_5657607 : Nat := 118140960795 + 5657607 * 2 ^ 59
def prefixEnd_5657607 : Nat := 4983230072969 + 3 ^ 40 * 5657607 * 2
def baseEnd_5657607 : Nat := 2905071745241751320293645

theorem tailTrace_5657607 : CollatzResearch.WordTrace tailWord_5657607 prefixEnd_5657607 2905071745241751320293645 := by
  unfold tailWord_5657607
  simp only [CollatzResearch.WordTrace]
  refine ⟨206349879614463556194227075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137566586409642370796151383 206349879614463556194227075)
  ·
    refine ⟨309524819421695334291340613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206349879614463556194227075 309524819421695334291340613)
    ·
      refine ⟨58035903641567875179626365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 309524819421695334291340613 58035903641567875179626365)
      ·
        refine ⟨21763463865587953192359887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58035903641567875179626365 21763463865587953192359887)
        ·
          refine ⟨32645195798381929788539831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21763463865587953192359887 32645195798381929788539831)
          ·
            refine ⟨48967793697572894682809747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32645195798381929788539831 48967793697572894682809747)
            ·
              refine ⟨73451690546359342024214621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48967793697572894682809747 73451690546359342024214621)
              ·
                refine ⟨27544383954884753259080483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73451690546359342024214621 27544383954884753259080483)
                ·
                  refine ⟨41316575932327129888620725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27544383954884753259080483 41316575932327129888620725)
                  ·
                    refine ⟨3873428993655668427058193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41316575932327129888620725 3873428993655668427058193)
                    ·
                      refine ⟨2905071745241751320293645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3873428993655668427058193 2905071745241751320293645)
                      ·
                        rfl

theorem cell23_5657607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_5657607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657607 prefixEnd_5657607 := by exact prefixLift 5657607
  have htrace : WordTrace (prefixWord ++ tailWord_5657607) baseStart_5657607 baseEnd_5657607 := by
    simpa [prefixWord, tailWord_5657607, baseEnd_5657607] using wordTrace_append hprefix tailTrace_5657607
  have hstable : (prefixWord ++ tailWord_5657607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657607).length < 2 ^ (prefixWord ++ tailWord_5657607).sum := by decide
  have hdescent : baseEnd_5657607 < baseStart_5657607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657618 : List Nat := [3, 2, 5, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_5657618 : Nat := 118140960795 + 5657618 * 2 ^ 59
def prefixEnd_5657618 : Nat := 4983230072969 + 3 ^ 40 * 5657618 * 2
def baseEnd_5657618 : Nat := 2905077393528950777256095

theorem tailTrace_5657618 : CollatzResearch.WordTrace tailWord_5657618 prefixEnd_5657618 2905077393528950777256095 := by
  unfold tailWord_5657618
  simp only [CollatzResearch.WordTrace]
  refine ⟨51587570204355926268219377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137566853878282470048585005 51587570204355926268219377)
  ·
    refine ⟨38690677653266944701164533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51587570204355926268219377 38690677653266944701164533)
    ·
      refine ⟨3627251029993776065734175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38690677653266944701164533 3627251029993776065734175)
      ·
        refine ⟨5440876544990664098601263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3627251029993776065734175 5440876544990664098601263)
        ·
          refine ⟨8161314817485996147901895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5440876544990664098601263 8161314817485996147901895)
          ·
            refine ⟨12241972226228994221852843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8161314817485996147901895 12241972226228994221852843)
            ·
              refine ⟨18362958339343491332779265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12241972226228994221852843 18362958339343491332779265)
              ·
                refine ⟨13772218754507618499584449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18362958339343491332779265 13772218754507618499584449)
                ·
                  refine ⟨10329164065880713874688337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13772218754507618499584449 10329164065880713874688337)
                  ·
                    refine ⟨7746873049410535406016253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10329164065880713874688337 7746873049410535406016253)
                    ·
                      refine ⟨2905077393528950777256095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7746873049410535406016253 2905077393528950777256095)
                      ·
                        rfl

theorem cell23_5657618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_5657618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657618 prefixEnd_5657618 := by exact prefixLift 5657618
  have htrace : WordTrace (prefixWord ++ tailWord_5657618) baseStart_5657618 baseEnd_5657618 := by
    simpa [prefixWord, tailWord_5657618, baseEnd_5657618] using wordTrace_append hprefix tailTrace_5657618
  have hstable : (prefixWord ++ tailWord_5657618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657618).length < 2 ^ (prefixWord ++ tailWord_5657618).sum := by decide
  have hdescent : baseEnd_5657618 < baseStart_5657618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657624 : List Nat := [2, 1, 2, 3, 2, 3, 1, 2, 2, 3, 2]
def baseStart_5657624 : Nat := 118140960795 + 5657624 * 2 ^ 59
def prefixEnd_5657624 : Nat := 4983230072969 + 3 ^ 40 * 5657624 * 2
def baseEnd_5657624 : Nat := 2905080474412877753781067

theorem tailTrace_5657624 : CollatzResearch.WordTrace tailWord_5657624 prefixEnd_5657624 2905080474412877753781067 := by
  unfold tailWord_5657624
  simp only [CollatzResearch.WordTrace]
  refine ⟨103175249827700984048797963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137566999770267978731730617 103175249827700984048797963)
  ·
    refine ⟨154762874741551476073196945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103175249827700984048797963 154762874741551476073196945)
    ·
      refine ⟨116072156056163607054897709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154762874741551476073196945 116072156056163607054897709)
      ·
        refine ⟨43527058521061352645586641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116072156056163607054897709 43527058521061352645586641)
        ·
          refine ⟨32645293890796014484189981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43527058521061352645586641 32645293890796014484189981)
          ·
            refine ⟨12241985209048505431571243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32645293890796014484189981 12241985209048505431571243)
            ·
              refine ⟨18362977813572758147356865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12241985209048505431571243 18362977813572758147356865)
              ·
                refine ⟨13772233360179568610517649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18362977813572758147356865 13772233360179568610517649)
                ·
                  refine ⟨10329175020134676457888237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13772233360179568610517649 10329175020134676457888237)
                  ·
                    refine ⟨3873440632550503671708089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10329175020134676457888237 3873440632550503671708089)
                    ·
                      refine ⟨2905080474412877753781067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3873440632550503671708089 2905080474412877753781067)
                      ·
                        rfl

theorem cell23_5657624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_5657624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657624 prefixEnd_5657624 := by exact prefixLift 5657624
  have htrace : WordTrace (prefixWord ++ tailWord_5657624) baseStart_5657624 baseEnd_5657624 := by
    simpa [prefixWord, tailWord_5657624, baseEnd_5657624] using wordTrace_append hprefix tailTrace_5657624
  have hstable : (prefixWord ++ tailWord_5657624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657624).length < 2 ^ (prefixWord ++ tailWord_5657624).sum := by decide
  have hdescent : baseEnd_5657624 < baseStart_5657624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657650 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_5657650 : Nat := 118140960795 + 5657650 * 2 ^ 59
def prefixEnd_5657650 : Nat := 4983230072969 + 3 ^ 40 * 5657650 * 2
def baseEnd_5657650 : Nat := 2905093824909894652055947

theorem tailTrace_5657650 : CollatzResearch.WordTrace tailWord_5657650 prefixEnd_5657650 2905093824909894652055947 := by
  unfold tailWord_5657650
  simp only [CollatzResearch.WordTrace]
  refine ⟨51587861988326943634510601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137567631968871849692028269 51587861988326943634510601)
  ·
    refine ⟨38690896491245207725882951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51587861988326943634510601 38690896491245207725882951)
    ·
      refine ⟨58036344736867811588824427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38690896491245207725882951 58036344736867811588824427)
      ·
        refine ⟨87054517105301717383236641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58036344736867811588824427 87054517105301717383236641)
        ·
          refine ⟨65290887828976288037427481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87054517105301717383236641 65290887828976288037427481)
          ·
            refine ⟨48968165871732216028070611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65290887828976288037427481 48968165871732216028070611)
            ·
              refine ⟨73452248807598324042105917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48968165871732216028070611 73452248807598324042105917)
              ·
                refine ⟨27544593302849371515789719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73452248807598324042105917 27544593302849371515789719)
                ·
                  refine ⟨41316889954274057273684579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27544593302849371515789719 41316889954274057273684579)
                  ·
                    refine ⟨61975334931411085910526869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41316889954274057273684579 61975334931411085910526869)
                    ·
                      refine ⟨2905093824909894652055947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61975334931411085910526869 2905093824909894652055947)
                      ·
                        rfl

theorem cell23_5657650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_5657650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657650 prefixEnd_5657650 := by exact prefixLift 5657650
  have htrace : WordTrace (prefixWord ++ tailWord_5657650) baseStart_5657650 baseEnd_5657650 := by
    simpa [prefixWord, tailWord_5657650, baseEnd_5657650] using wordTrace_append hprefix tailTrace_5657650
  have hstable : (prefixWord ++ tailWord_5657650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657650).length < 2 ^ (prefixWord ++ tailWord_5657650).sum := by decide
  have hdescent : baseEnd_5657650 < baseStart_5657650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657654 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_5657654 : Nat := 118140960795 + 5657654 * 2 ^ 59
def prefixEnd_5657654 : Nat := 4983230072969 + 3 ^ 40 * 5657654 * 2
def baseEnd_5657654 : Nat := 2905095878832512636405929

theorem tailTrace_5657654 : CollatzResearch.WordTrace tailWord_5657654 prefixEnd_5657654 2905095878832512636405929 := by
  unfold tailWord_5657654
  simp only [CollatzResearch.WordTrace]
  refine ⟨12896974615330830201324251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137567729230195522147458677 12896974615330830201324251)
  ·
    refine ⟨19345461922996245301986377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12896974615330830201324251 19345461922996245301986377)
    ·
      refine ⟨14509096442247183976489783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19345461922996245301986377 14509096442247183976489783)
      ·
        refine ⟨21763644663370775964734675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14509096442247183976489783 21763644663370775964734675)
        ·
          refine ⟨32645466995056163947102013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21763644663370775964734675 32645466995056163947102013)
          ·
            refine ⟨12242050123146061480163255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32645466995056163947102013 12242050123146061480163255)
            ·
              refine ⟨18363075184719092220244883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12242050123146061480163255 18363075184719092220244883)
              ·
                refine ⟨27544612777078638330367325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18363075184719092220244883 27544612777078638330367325)
                ·
                  refine ⟨10329229791404489373887747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27544612777078638330367325 10329229791404489373887747)
                  ·
                    refine ⟨15493844687106734060831621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10329229791404489373887747 15493844687106734060831621)
                    ·
                      refine ⟨2905095878832512636405929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15493844687106734060831621 2905095878832512636405929)
                      ·
                        rfl

theorem cell23_5657654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_5657654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657654 prefixEnd_5657654 := by exact prefixLift 5657654
  have htrace : WordTrace (prefixWord ++ tailWord_5657654) baseStart_5657654 baseEnd_5657654 := by
    simpa [prefixWord, tailWord_5657654, baseEnd_5657654] using wordTrace_append hprefix tailTrace_5657654
  have hstable : (prefixWord ++ tailWord_5657654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657654).length < 2 ^ (prefixWord ++ tailWord_5657654).sum := by decide
  have hdescent : baseEnd_5657654 < baseStart_5657654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657660 : List Nat := [2, 2, 2, 2, 2, 2, 2, 9]
def baseStart_5657660 : Nat := 118140960795 + 5657660 * 2 ^ 59
def prefixEnd_5657660 : Nat := 4983230072969 + 3 ^ 40 * 5657660 * 2
def baseEnd_5657660 : Nat := 107596257767275541219663

theorem tailTrace_5657660 : CollatzResearch.WordTrace tailWord_5657660 prefixEnd_5657660 107596257767275541219663 := by
  unfold tailWord_5657660
  simp only [CollatzResearch.WordTrace]
  refine ⟨103175906341635773122953217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137567875122181030830604289 103175906341635773122953217)
  ·
    refine ⟨77381929756226829842214913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103175906341635773122953217 77381929756226829842214913)
    ·
      refine ⟨58036447317170122381661185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77381929756226829842214913 58036447317170122381661185)
      ·
        refine ⟨43527335487877591786245889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58036447317170122381661185 43527335487877591786245889)
        ·
          refine ⟨32645501615908193839684417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43527335487877591786245889 32645501615908193839684417)
          ·
            refine ⟨24484126211931145379763313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32645501615908193839684417 24484126211931145379763313)
            ·
              refine ⟨18363094658948359034822485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24484126211931145379763313 18363094658948359034822485)
              ·
                refine ⟨107596257767275541219663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18363094658948359034822485 107596257767275541219663)
                ·
                  rfl

theorem cell23_5657660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 9].length) (baseStart_5657660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657660 prefixEnd_5657660 := by exact prefixLift 5657660
  have htrace : WordTrace (prefixWord ++ tailWord_5657660) baseStart_5657660 baseEnd_5657660 := by
    simpa [prefixWord, tailWord_5657660, baseEnd_5657660] using wordTrace_append hprefix tailTrace_5657660
  have hstable : (prefixWord ++ tailWord_5657660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657660).length < 2 ^ (prefixWord ++ tailWord_5657660).sum := by decide
  have hdescent : baseEnd_5657660 < baseStart_5657660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657700 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_5657700 : Nat := 118140960795 + 5657700 * 2 ^ 59
def prefixEnd_5657700 : Nat := 4983230072969 + 3 ^ 40 * 5657700 * 2
def baseEnd_5657700 : Nat := 2905119498942619456430717

theorem tailTrace_5657700 : CollatzResearch.WordTrace tailWord_5657700 prefixEnd_5657700 2905119498942619456430717 := by
  unfold tailWord_5657700
  simp only [CollatzResearch.WordTrace]
  refine ⟨103176635801563316538681277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137568847735417755384908369 103176635801563316538681277)
  ·
    refine ⟨38691238425586243702005479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103176635801563316538681277 38691238425586243702005479)
    ·
      refine ⟨58036857638379365553008219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38691238425586243702005479 58036857638379365553008219)
      ·
        refine ⟨87055286457569048329512329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58036857638379365553008219 87055286457569048329512329)
        ·
          refine ⟨65291464843176786247134247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87055286457569048329512329 65291464843176786247134247)
          ·
            refine ⟨97937197264765179370701371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65291464843176786247134247 97937197264765179370701371)
            ·
              refine ⟨146905795897147769056052057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97937197264765179370701371 146905795897147769056052057)
              ·
                refine ⟨110179346922860826792039043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146905795897147769056052057 110179346922860826792039043)
                ·
                  refine ⟨165269020384291240188058565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110179346922860826792039043 165269020384291240188058565)
                  ·
                    refine ⟨30987941322054607535260981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 165269020384291240188058565 30987941322054607535260981)
                    ·
                      refine ⟨2905119498942619456430717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30987941322054607535260981 2905119498942619456430717)
                      ·
                        rfl

theorem cell23_5657700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_5657700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657700 prefixEnd_5657700 := by exact prefixLift 5657700
  have htrace : WordTrace (prefixWord ++ tailWord_5657700) baseStart_5657700 baseEnd_5657700 := by
    simpa [prefixWord, tailWord_5657700, baseEnd_5657700] using wordTrace_append hprefix tailTrace_5657700
  have hstable : (prefixWord ++ tailWord_5657700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657700).length < 2 ^ (prefixWord ++ tailWord_5657700).sum := by decide
  have hdescent : baseEnd_5657700 < baseStart_5657700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657714 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 3, 3, 2]
def baseStart_5657714 : Nat := 118140960795 + 5657714 * 2 ^ 59
def prefixEnd_5657714 : Nat := 4983230072969 + 3 ^ 40 * 5657714 * 2
def baseEnd_5657714 : Nat := 2905126687671782401655653

theorem tailTrace_5657714 : CollatzResearch.WordTrace tailWord_5657714 prefixEnd_5657714 2905126687671782401655653 := by
  unfold tailWord_5657714
  simp only [CollatzResearch.WordTrace]
  refine ⟨51588445556268978367093049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137569188150050608978914797 51588445556268978367093049)
  ·
    refine ⟨38691334167201733775319787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51588445556268978367093049 38691334167201733775319787)
    ·
      refine ⟨58037001250802600662979681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38691334167201733775319787 58037001250802600662979681)
      ·
        refine ⟨43527750938101950497234761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58037001250802600662979681 43527750938101950497234761)
        ·
          refine ⟨32645813203576462872926071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43527750938101950497234761 32645813203576462872926071)
          ·
            refine ⟨48968719805364694309389107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32645813203576462872926071 48968719805364694309389107)
            ·
              refine ⟨73453079708047041464083661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48968719805364694309389107 73453079708047041464083661)
              ·
                refine ⟨27544904890517640549031373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73453079708047041464083661 27544904890517640549031373)
                ·
                  refine ⟨10329339333944115205886765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27544904890517640549031373 10329339333944115205886765)
                  ·
                    refine ⟨3873502250229043202207537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10329339333944115205886765 3873502250229043202207537)
                    ·
                      refine ⟨2905126687671782401655653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3873502250229043202207537 2905126687671782401655653)
                      ·
                        rfl

theorem cell23_5657714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_5657714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657714 prefixEnd_5657714 := by exact prefixLift 5657714
  have htrace : WordTrace (prefixWord ++ tailWord_5657714) baseStart_5657714 baseEnd_5657714 := by
    simpa [prefixWord, tailWord_5657714, baseEnd_5657714] using wordTrace_append hprefix tailTrace_5657714
  have hstable : (prefixWord ++ tailWord_5657714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657714).length < 2 ^ (prefixWord ++ tailWord_5657714).sum := by decide
  have hdescent : baseEnd_5657714 < baseStart_5657714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657757 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_5657757 : Nat := 118140960795 + 5657757 * 2 ^ 59
def prefixEnd_5657757 : Nat := 4983230072969 + 3 ^ 40 * 5657757 * 2
def baseEnd_5657757 : Nat := 2905148767339925733417955

theorem tailTrace_5657757 : CollatzResearch.WordTrace tailWord_5657757 prefixEnd_5657757 2905148767339925733417955 := by
  unfold tailWord_5657757
  simp only [CollatzResearch.WordTrace]
  refine ⟨206355350563920131812187525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137570233709280087874791683 206355350563920131812187525)
  ·
    refine ⟨38691628230735024714785161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206355350563920131812187525 38691628230735024714785161)
    ·
      refine ⟨29018721173051268536088871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38691628230735024714785161 29018721173051268536088871)
      ·
        refine ⟨43528081759576902804133307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29018721173051268536088871 43528081759576902804133307)
        ·
          refine ⟨65292122639365354206199961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43528081759576902804133307 65292122639365354206199961)
          ·
            refine ⟨48969091979524015654649971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65292122639365354206199961 48969091979524015654649971)
            ·
              refine ⟨73453637969286023481974957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48969091979524015654649971 73453637969286023481974957)
              ·
                refine ⟨27545114238482258805740609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73453637969286023481974957 27545114238482258805740609)
                ·
                  refine ⟨20658835678861694104305457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27545114238482258805740609 20658835678861694104305457)
                  ·
                    refine ⟨15494126759146270578229093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20658835678861694104305457 15494126759146270578229093)
                    ·
                      refine ⟨2905148767339925733417955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15494126759146270578229093 2905148767339925733417955)
                      ·
                        rfl

theorem cell23_5657757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_5657757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657757 prefixEnd_5657757 := by exact prefixLift 5657757
  have htrace : WordTrace (prefixWord ++ tailWord_5657757) baseStart_5657757 baseEnd_5657757 := by
    simpa [prefixWord, tailWord_5657757, baseEnd_5657757] using wordTrace_append hprefix tailTrace_5657757
  have hstable : (prefixWord ++ tailWord_5657757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657757).length < 2 ^ (prefixWord ++ tailWord_5657757).sum := by decide
  have hdescent : baseEnd_5657757 < baseStart_5657757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657817 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 6, 1, 4]
def baseStart_5657817 : Nat := 118140960795 + 5657817 * 2 ^ 59
def prefixEnd_5657817 : Nat := 4983230072969 + 3 ^ 40 * 5657817 * 2
def baseEnd_5657817 : Nat := 2905179576179195498667679

theorem tailTrace_5657817 : CollatzResearch.WordTrace tailWord_5657817 prefixEnd_5657817 2905179576179195498667679 := by
  unfold tailWord_5657817
  simp only [CollatzResearch.WordTrace]
  refine ⟨206357538943702762059371705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137571692629135174706247803 206357538943702762059371705)
  ·
    refine ⟨154768154207777071544528779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206357538943702762059371705 154768154207777071544528779)
    ·
      refine ⟨232152231311665607316793169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154768154207777071544528779 232152231311665607316793169)
      ·
        refine ⟨174114173483749205487594877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232152231311665607316793169 174114173483749205487594877)
        ·
          refine ⟨65292815056405952057848079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174114173483749205487594877 65292815056405952057848079)
          ·
            refine ⟨97939222584608928086772119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65292815056405952057848079 97939222584608928086772119)
            ·
              refine ⟨146908833876913392130158179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97939222584608928086772119 146908833876913392130158179)
              ·
                refine ⟨220363250815370088195237269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146908833876913392130158179 220363250815370088195237269)
                ·
                  refine ⟨10329527381970472884151747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 220363250815370088195237269 10329527381970472884151747)
                  ·
                    refine ⟨15494291072955709326227621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10329527381970472884151747 15494291072955709326227621)
                    ·
                      refine ⟨2905179576179195498667679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15494291072955709326227621 2905179576179195498667679)
                      ·
                        rfl

theorem cell23_5657817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_5657817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657817 prefixEnd_5657817 := by exact prefixLift 5657817
  have htrace : WordTrace (prefixWord ++ tailWord_5657817) baseStart_5657817 baseEnd_5657817 := by
    simpa [prefixWord, tailWord_5657817, baseEnd_5657817] using wordTrace_append hprefix tailTrace_5657817
  have hstable : (prefixWord ++ tailWord_5657817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657817).length < 2 ^ (prefixWord ++ tailWord_5657817).sum := by decide
  have hdescent : baseEnd_5657817 < baseStart_5657817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657831 : List Nat := [1, 1, 5, 3, 2, 1, 2, 1, 2, 5]
def baseStart_5657831 : Nat := 118140960795 + 5657831 * 2 ^ 59
def prefixEnd_5657831 : Nat := 4983230072969 + 3 ^ 40 * 5657831 * 2
def baseEnd_5657831 : Nat := 968395588302786147964205

theorem tailTrace_5657831 : CollatzResearch.WordTrace tailWord_5657831 prefixEnd_5657831 968395588302786147964205 := by
  unfold tailWord_5657831
  simp only [CollatzResearch.WordTrace]
  refine ⟨206358049565652042450381347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137572033043768028300254231 206358049565652042450381347)
  ·
    refine ⟨309537074348478063675572021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206358049565652042450381347 309537074348478063675572021)
    ·
      refine ⟨29019100720169818469584877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 309537074348478063675572021 29019100720169818469584877)
      ·
        refine ⟨10882162770063681926094329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29019100720169818469584877 10882162770063681926094329)
        ·
          refine ⟨8161622077547761444570747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10882162770063681926094329 8161622077547761444570747)
          ·
            refine ⟨12242433116321642166856121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8161622077547761444570747 12242433116321642166856121)
            ·
              refine ⟨9181824837241231625142091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12242433116321642166856121 9181824837241231625142091)
              ·
                refine ⟨13772737255861847437713137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9181824837241231625142091 13772737255861847437713137)
                ·
                  refine ⟨10329552941896385578284853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13772737255861847437713137 10329552941896385578284853)
                  ·
                    refine ⟨968395588302786147964205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10329552941896385578284853 968395588302786147964205)
                    ·
                      rfl

theorem cell23_5657831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_5657831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657831 prefixEnd_5657831 := by exact prefixLift 5657831
  have htrace : WordTrace (prefixWord ++ tailWord_5657831) baseStart_5657831 baseEnd_5657831 := by
    simpa [prefixWord, tailWord_5657831, baseEnd_5657831] using wordTrace_append hprefix tailTrace_5657831
  have hstable : (prefixWord ++ tailWord_5657831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657831).length < 2 ^ (prefixWord ++ tailWord_5657831).sum := by decide
  have hdescent : baseEnd_5657831 < baseStart_5657831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657834 : List Nat := [3, 1, 3, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_5657834 : Nat := 118140960795 + 5657834 * 2 ^ 59
def prefixEnd_5657834 : Nat := 4983230072969 + 3 ^ 40 * 5657834 * 2
def baseEnd_5657834 : Nat := 2905188305350321932155101

theorem tailTrace_5657834 : CollatzResearch.WordTrace tailWord_5657834 prefixEnd_5657834 2905188305350321932155101 := by
  unfold tailWord_5657834
  simp only [CollatzResearch.WordTrace]
  refine ⟨51589539746160293490685139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137572105989760782641827037 51589539746160293490685139)
  ·
    refine ⟨77384309619240440236027709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51589539746160293490685139 77384309619240440236027709)
    ·
      refine ⟨29019116107215165088510391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77384309619240440236027709 29019116107215165088510391)
      ·
        refine ⟨43528674160822747632765587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29019116107215165088510391 43528674160822747632765587)
        ·
          refine ⟨65293011241234121449148381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43528674160822747632765587 65293011241234121449148381)
          ·
            refine ⟨24484879215462795543430643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65293011241234121449148381 24484879215462795543430643)
            ·
              refine ⟨36727318823194193315145965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24484879215462795543430643 36727318823194193315145965)
              ·
                refine ⟨13772744558697822493179737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36727318823194193315145965 13772744558697822493179737)
                ·
                  refine ⟨10329558419023366869884803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13772744558697822493179737 10329558419023366869884803)
                  ·
                    refine ⟨15494337628535050304827205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10329558419023366869884803 15494337628535050304827205)
                    ·
                      refine ⟨2905188305350321932155101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15494337628535050304827205 2905188305350321932155101)
                      ·
                        rfl

theorem cell23_5657834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_5657834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657834 prefixEnd_5657834 := by exact prefixLift 5657834
  have htrace : WordTrace (prefixWord ++ tailWord_5657834) baseStart_5657834 baseEnd_5657834 := by
    simpa [prefixWord, tailWord_5657834, baseEnd_5657834] using wordTrace_append hprefix tailTrace_5657834
  have hstable : (prefixWord ++ tailWord_5657834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657834).length < 2 ^ (prefixWord ++ tailWord_5657834).sum := by decide
  have hdescent : baseEnd_5657834 < baseStart_5657834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657861 : List Nat := [1, 3, 1, 1, 2, 1, 5, 4, 1, 4]
def baseStart_5657861 : Nat := 118140960795 + 5657861 * 2 ^ 59
def prefixEnd_5657861 : Nat := 4983230072969 + 3 ^ 40 * 5657861 * 2
def baseEnd_5657861 : Nat := 968400723109331108839159

theorem tailTrace_5657861 : CollatzResearch.WordTrace tailWord_5657861 prefixEnd_5657861 968400723109331108839159 := by
  unfold tailWord_5657861
  simp only [CollatzResearch.WordTrace]
  refine ⟨206359143755543357573973437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137572762503695571715982291 206359143755543357573973437)
  ·
    refine ⟨77384678908328759090240039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206359143755543357573973437 77384678908328759090240039)
    ·
      refine ⟨116077018362493138635360059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77384678908328759090240039 116077018362493138635360059)
      ·
        refine ⟨174115527543739707953040089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116077018362493138635360059 174115527543739707953040089)
        ·
          refine ⟨130586645657804780964780067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174115527543739707953040089 130586645657804780964780067)
          ·
            refine ⟨195879968486707171447170101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130586645657804780964780067 195879968486707171447170101)
            ·
              refine ⟨18363747045628797323172197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 195879968486707171447170101 18363747045628797323172197)
              ·
                refine ⟨3443202571055399498094787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18363747045628797323172197 3443202571055399498094787)
                ·
                  refine ⟨5164803856583099247142181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3443202571055399498094787 5164803856583099247142181)
                  ·
                    refine ⟨968400723109331108839159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5164803856583099247142181 968400723109331108839159)
                    ·
                      rfl

theorem cell23_5657861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 1, 4].length) (baseStart_5657861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657861 prefixEnd_5657861 := by exact prefixLift 5657861
  have htrace : WordTrace (prefixWord ++ tailWord_5657861) baseStart_5657861 baseEnd_5657861 := by
    simpa [prefixWord, tailWord_5657861, baseEnd_5657861] using wordTrace_append hprefix tailTrace_5657861
  have hstable : (prefixWord ++ tailWord_5657861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657861).length < 2 ^ (prefixWord ++ tailWord_5657861).sum := by decide
  have hdescent : baseEnd_5657861 < baseStart_5657861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657888 : List Nat := [2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 3]
def baseStart_5657888 : Nat := 118140960795 + 5657888 * 2 ^ 59
def prefixEnd_5657888 : Nat := 4983230072969 + 3 ^ 40 * 5657888 * 2
def baseEnd_5657888 : Nat := 2905216033305664720879853

theorem tailTrace_5657888 : CollatzResearch.WordTrace tailWord_5657888 prefixEnd_5657888 2905216033305664720879853 := by
  unfold tailWord_5657888
  simp only [CollatzResearch.WordTrace]
  refine ⟨103180064263222770592603159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137573419017630360790137545 103180064263222770592603159)
  ·
    refine ⟨154770096394834155888904739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103180064263222770592603159 154770096394834155888904739)
    ·
      refine ⟨232155144592251233833357109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154770096394834155888904739 232155144592251233833357109)
      ·
        refine ⟨21764544805523553171877229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 232155144592251233833357109 21764544805523553171877229)
        ·
          refine ⟨8161704302071332439453961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21764544805523553171877229 8161704302071332439453961)
          ·
            refine ⟨6121278226553499329590471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8161704302071332439453961 6121278226553499329590471)
            ·
              refine ⟨9181917339830248994385707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6121278226553499329590471 9181917339830248994385707)
              ·
                refine ⟨13772876009745373491578561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9181917339830248994385707 13772876009745373491578561)
                ·
                  refine ⟨10329657007309030118683921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13772876009745373491578561 10329657007309030118683921)
                  ·
                    refine ⟨7747242755481772589012941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10329657007309030118683921 7747242755481772589012941)
                    ·
                      refine ⟨2905216033305664720879853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7747242755481772589012941 2905216033305664720879853)
                      ·
                        rfl

theorem cell23_5657888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_5657888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657888 prefixEnd_5657888 := by exact prefixLift 5657888
  have htrace : WordTrace (prefixWord ++ tailWord_5657888) baseStart_5657888 baseEnd_5657888 := by
    simpa [prefixWord, tailWord_5657888, baseEnd_5657888] using wordTrace_append hprefix tailTrace_5657888
  have hstable : (prefixWord ++ tailWord_5657888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657888).length < 2 ^ (prefixWord ++ tailWord_5657888).sum := by decide
  have hdescent : baseEnd_5657888 < baseStart_5657888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657904 : List Nat := [2, 1, 1, 1, 2, 2, 5, 3, 1, 5]
def baseStart_5657904 : Nat := 118140960795 + 5657904 * 2 ^ 59
def prefixEnd_5657904 : Nat := 4983230072969 + 3 ^ 40 * 5657904 * 2
def baseEnd_5657904 : Nat := 968408082998712219426593

theorem tailTrace_5657904 : CollatzResearch.WordTrace tailWord_5657904 prefixEnd_5657904 968408082998712219426593 := by
  unfold tailWord_5657904
  simp only [CollatzResearch.WordTrace]
  refine ⟨103180356047193787958894383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137573808062925050611859177 103180356047193787958894383)
  ·
    refine ⟨154770534070790681938341575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103180356047193787958894383 154770534070790681938341575)
    ·
      refine ⟨232155801106186022907512363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154770534070790681938341575 232155801106186022907512363)
      ·
        refine ⟨348233701659279034361268545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232155801106186022907512363 348233701659279034361268545)
        ·
          refine ⟨261175276244459275770951409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348233701659279034361268545 261175276244459275770951409)
          ·
            refine ⟨195881457183344456828213557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261175276244459275770951409 195881457183344456828213557)
            ·
              refine ⟨18363886610938542827645021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 195881457183344456828213557 18363886610938542827645021)
              ·
                refine ⟨6886457479101953560366883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18363886610938542827645021 6886457479101953560366883)
                ·
                  refine ⟨10329686218652930340550325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6886457479101953560366883 10329686218652930340550325)
                  ·
                    refine ⟨968408082998712219426593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10329686218652930340550325 968408082998712219426593)
                    ·
                      rfl

theorem cell23_5657904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 1, 5].length) (baseStart_5657904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657904 prefixEnd_5657904 := by exact prefixLift 5657904
  have htrace : WordTrace (prefixWord ++ tailWord_5657904) baseStart_5657904 baseEnd_5657904 := by
    simpa [prefixWord, tailWord_5657904, baseEnd_5657904] using wordTrace_append hprefix tailTrace_5657904
  have hstable : (prefixWord ++ tailWord_5657904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657904).length < 2 ^ (prefixWord ++ tailWord_5657904).sum := by decide
  have hdescent : baseEnd_5657904 < baseStart_5657904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657918 : List Nat := [4, 2, 1, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_5657918 : Nat := 118140960795 + 5657918 * 2 ^ 59
def prefixEnd_5657918 : Nat := 4983230072969 + 3 ^ 40 * 5657918 * 2
def baseEnd_5657918 : Nat := 2905231437725299603504715

theorem tailTrace_5657918 : CollatzResearch.WordTrace tailWord_5657918 prefixEnd_5657918 2905231437725299603504715 := by
  unfold tailWord_5657918
  simp only [CollatzResearch.WordTrace]
  refine ⟨25795152839542107038599801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137574148477557904205865605 25795152839542107038599801)
  ·
    refine ⟨19346364629656580278949851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25795152839542107038599801 19346364629656580278949851)
    ·
      refine ⟨29019546944484870418424777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19346364629656580278949851 29019546944484870418424777)
      ·
        refine ⟨21764660208363652813818583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29019546944484870418424777 21764660208363652813818583)
        ·
          refine ⟨32646990312545479220727875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21764660208363652813818583 32646990312545479220727875)
          ·
            refine ⟨48970485468818218831091813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32646990312545479220727875 48970485468818218831091813)
            ·
              refine ⟨9181966025403416030829715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48970485468818218831091813 9181966025403416030829715)
              ·
                refine ⟨13772949038105124046244573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9181966025403416030829715 13772949038105124046244573)
                ·
                  refine ⟨5164855889289421517341715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13772949038105124046244573 5164855889289421517341715)
                  ·
                    refine ⟨7747283833934132276012573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5164855889289421517341715 7747283833934132276012573)
                    ·
                      refine ⟨2905231437725299603504715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7747283833934132276012573 2905231437725299603504715)
                      ·
                        rfl

theorem cell23_5657918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_5657918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657918 prefixEnd_5657918 := by exact prefixLift 5657918
  have htrace : WordTrace (prefixWord ++ tailWord_5657918) baseStart_5657918 baseEnd_5657918 := by
    simpa [prefixWord, tailWord_5657918, baseEnd_5657918] using wordTrace_append hprefix tailTrace_5657918
  have hstable : (prefixWord ++ tailWord_5657918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657918).length < 2 ^ (prefixWord ++ tailWord_5657918).sum := by decide
  have hdescent : baseEnd_5657918 < baseStart_5657918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657941 : List Nat := [1, 3, 2, 2, 3, 1, 1, 4, 1, 1, 4]
def baseStart_5657941 : Nat := 118140960795 + 5657941 * 2 ^ 59
def prefixEnd_5657941 : Nat := 4983230072969 + 3 ^ 40 * 5657941 * 2
def baseEnd_5657941 : Nat := 2905243247780353013517109

theorem tailTrace_5657941 : CollatzResearch.WordTrace tailWord_5657941 prefixEnd_5657941 2905243247780353013517109 := by
  unfold tailWord_5657941
  simp only [CollatzResearch.WordTrace]
  refine ⟨206362061595253531236885677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137574707730169020824590451 206362061595253531236885677)
  ·
    refine ⟨77385773098220074213832129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206362061595253531236885677 77385773098220074213832129)
    ·
      refine ⟨58039329823665055660374097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77385773098220074213832129 58039329823665055660374097)
      ·
        refine ⟨43529497367748791745280573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58039329823665055660374097 43529497367748791745280573)
        ·
          refine ⟨16323561512905796904480215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43529497367748791745280573 16323561512905796904480215)
          ·
            refine ⟨24485342269358695356720323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16323561512905796904480215 24485342269358695356720323)
            ·
              refine ⟨36728013404038043035080485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24485342269358695356720323 36728013404038043035080485)
              ·
                refine ⟨6886502513257133069077591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36728013404038043035080485 6886502513257133069077591)
                ·
                  refine ⟨10329753769885699603616387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6886502513257133069077591 10329753769885699603616387)
                  ·
                    refine ⟨15494630654828549405424581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10329753769885699603616387 15494630654828549405424581)
                    ·
                      refine ⟨2905243247780353013517109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15494630654828549405424581 2905243247780353013517109)
                      ·
                        rfl

theorem cell23_5657941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_5657941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657941 prefixEnd_5657941 := by exact prefixLift 5657941
  have htrace : WordTrace (prefixWord ++ tailWord_5657941) baseStart_5657941 baseEnd_5657941 := by
    simpa [prefixWord, tailWord_5657941, baseEnd_5657941] using wordTrace_append hprefix tailTrace_5657941
  have hstable : (prefixWord ++ tailWord_5657941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657941).length < 2 ^ (prefixWord ++ tailWord_5657941).sum := by decide
  have hdescent : baseEnd_5657941 < baseStart_5657941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5657964 : List Nat := [2, 2, 1, 1, 5, 3, 9]
def baseStart_5657964 : Nat := 118140960795 + 5657964 * 2 ^ 59
def prefixEnd_5657964 : Nat := 4983230072969 + 3 ^ 40 * 5657964 * 2
def baseEnd_5657964 : Nat := 35867346393029708932463

theorem tailTrace_5657964 : CollatzResearch.WordTrace tailWord_5657964 prefixEnd_5657964 35867346393029708932463 := by
  unfold tailWord_5657964
  simp only [CollatzResearch.WordTrace]
  refine ⟨103181450237085103082486473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137575266982780137443315297 103181450237085103082486473)
  ·
    refine ⟨77386087677813827311864855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103181450237085103082486473 77386087677813827311864855)
    ·
      refine ⟨116079131516720740967797283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77386087677813827311864855 116079131516720740967797283)
      ·
        refine ⟨174118697275081111451695925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116079131516720740967797283 174118697275081111451695925)
        ·
          refine ⟨16323627869538854198596493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174118697275081111451695925 16323627869538854198596493)
          ·
            refine ⟨6121360451077070324473685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16323627869538854198596493 6121360451077070324473685)
            ·
              refine ⟨35867346393029708932463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6121360451077070324473685 35867346393029708932463)
              ·
                rfl

theorem cell23_5657964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 9].length) (baseStart_5657964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5657964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5657964 prefixEnd_5657964 := by exact prefixLift 5657964
  have htrace : WordTrace (prefixWord ++ tailWord_5657964) baseStart_5657964 baseEnd_5657964 := by
    simpa [prefixWord, tailWord_5657964, baseEnd_5657964] using wordTrace_append hprefix tailTrace_5657964
  have hstable : (prefixWord ++ tailWord_5657964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5657964).length < 2 ^ (prefixWord ++ tailWord_5657964).sum := by decide
  have hdescent : baseEnd_5657964 < baseStart_5657964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5657964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658001 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 3, 3, 2]
def baseStart_5658001 : Nat := 118140960795 + 5658001 * 2 ^ 59
def prefixEnd_5658001 : Nat := 4983230072969 + 3 ^ 40 * 5658001 * 2
def baseEnd_5658001 : Nat := 2905274056619622778766833

theorem tailTrace_5658001 : CollatzResearch.WordTrace tailWord_5658001 prefixEnd_5658001 2905274056619622778766833 := by
  unfold tailWord_5658001
  simp only [CollatzResearch.WordTrace]
  refine ⟨206364249975036161484069857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137576166650024107656046571 206364249975036161484069857)
  ·
    refine ⟨154773187481277121113052393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206364249975036161484069857 154773187481277121113052393)
    ·
      refine ⟨116079890610957840834789295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154773187481277121113052393 116079890610957840834789295)
      ·
        refine ⟨174119835916436761252183943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116079890610957840834789295 174119835916436761252183943)
        ·
          refine ⟨261179753874655141878275915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174119835916436761252183943 261179753874655141878275915)
          ·
            refine ⟨391769630811982712817413873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261179753874655141878275915 391769630811982712817413873)
            ·
              refine ⟨293827223108987034613060405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391769630811982712817413873 293827223108987034613060405)
              ·
                refine ⟨27546302166467534494974413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 293827223108987034613060405 27546302166467534494974413)
                ·
                  refine ⟨10329863312425325435615405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27546302166467534494974413 10329863312425325435615405)
                  ·
                    refine ⟨3873698742159497038355777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10329863312425325435615405 3873698742159497038355777)
                    ·
                      refine ⟨2905274056619622778766833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3873698742159497038355777 2905274056619622778766833)
                      ·
                        rfl

theorem cell23_5658001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 3, 2].length) (baseStart_5658001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658001 prefixEnd_5658001 := by exact prefixLift 5658001
  have htrace : WordTrace (prefixWord ++ tailWord_5658001) baseStart_5658001 baseEnd_5658001 := by
    simpa [prefixWord, tailWord_5658001, baseEnd_5658001] using wordTrace_append hprefix tailTrace_5658001
  have hstable : (prefixWord ++ tailWord_5658001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658001).length < 2 ^ (prefixWord ++ tailWord_5658001).sum := by decide
  have hdescent : baseEnd_5658001 < baseStart_5658001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658008 : List Nat := [2, 1, 2, 5, 2, 1, 1, 2, 1, 3, 3]
def baseStart_5658008 : Nat := 118140960795 + 5658008 * 2 ^ 59
def prefixEnd_5658008 : Nat := 4983230072969 + 3 ^ 40 * 5658008 * 2
def baseEnd_5658008 : Nat := 2905277650984204251379301

theorem tailTrace_5658008 : CollatzResearch.WordTrace tailWord_5658008 prefixEnd_5658008 2905277650984204251379301 := by
  unfold tailWord_5658008
  simp only [CollatzResearch.WordTrace]
  refine ⟨103182252643005400839787339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137576336857340534453049785 103182252643005400839787339)
  ·
    refine ⟨154773378964508101259681009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103182252643005400839787339 154773378964508101259681009)
    ·
      refine ⟨116080034223381075944760757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154773378964508101259681009 116080034223381075944760757)
      ·
        refine ⟨10882503208441975869821321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116080034223381075944760757 10882503208441975869821321)
        ·
          refine ⟨8161877406331481902365991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10882503208441975869821321 8161877406331481902365991)
          ·
            refine ⟨12242816109497222853548987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8161877406331481902365991 12242816109497222853548987)
            ·
              refine ⟨18364224164245834280323481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12242816109497222853548987 18364224164245834280323481)
              ·
                refine ⟨13773168123184375710242611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18364224164245834280323481 13773168123184375710242611)
                ·
                  refine ⟨20659752184776563565363917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13773168123184375710242611 20659752184776563565363917)
                  ·
                    refine ⟨7747407069291211337011469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20659752184776563565363917 7747407069291211337011469)
                    ·
                      refine ⟨2905277650984204251379301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7747407069291211337011469 2905277650984204251379301)
                      ·
                        rfl

theorem cell23_5658008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_5658008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658008 prefixEnd_5658008 := by exact prefixLift 5658008
  have htrace : WordTrace (prefixWord ++ tailWord_5658008) baseStart_5658008 baseEnd_5658008 := by
    simpa [prefixWord, tailWord_5658008, baseEnd_5658008] using wordTrace_append hprefix tailTrace_5658008
  have hstable : (prefixWord ++ tailWord_5658008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658008).length < 2 ^ (prefixWord ++ tailWord_5658008).sum := by decide
  have hdescent : baseEnd_5658008 < baseStart_5658008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658012 : List Nat := [2, 2, 3, 4, 1, 1, 3, 1, 1, 2, 3]
def baseStart_5658012 : Nat := 118140960795 + 5658012 * 2 ^ 59
def prefixEnd_5658012 : Nat := 4983230072969 + 3 ^ 40 * 5658012 * 2
def baseEnd_5658012 : Nat := 2905279704906822235729283

theorem tailTrace_5658012 : CollatzResearch.WordTrace tailWord_5658012 prefixEnd_5658012 2905279704906822235729283 := by
  unfold tailWord_5658012
  simp only [CollatzResearch.WordTrace]
  refine ⟨103182325588998155181360145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137576434118664206908480193 103182325588998155181360145)
  ·
    refine ⟨77386744191748616386020109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103182325588998155181360145 77386744191748616386020109)
    ·
      refine ⟨29020029071905731144757541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77386744191748616386020109 29020029071905731144757541)
      ·
        refine ⟨5441255450982324589642039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29020029071905731144757541 5441255450982324589642039)
        ·
          refine ⟨8161883176473486884463059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5441255450982324589642039 8161883176473486884463059)
          ·
            refine ⟨12242824764710230326694589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8161883176473486884463059 12242824764710230326694589)
            ·
              refine ⟨4591059286766336372510471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12242824764710230326694589 4591059286766336372510471)
              ·
                refine ⟨6886588930149504558765707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4591059286766336372510471 6886588930149504558765707)
                ·
                  refine ⟨10329883395224256838148561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6886588930149504558765707 10329883395224256838148561)
                  ·
                    refine ⟨7747412546418192628611421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10329883395224256838148561 7747412546418192628611421)
                    ·
                      refine ⟨2905279704906822235729283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7747412546418192628611421 2905279704906822235729283)
                      ·
                        rfl

theorem cell23_5658012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_5658012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658012 prefixEnd_5658012 := by exact prefixLift 5658012
  have htrace : WordTrace (prefixWord ++ tailWord_5658012) baseStart_5658012 baseEnd_5658012 := by
    simpa [prefixWord, tailWord_5658012, baseEnd_5658012] using wordTrace_append hprefix tailTrace_5658012
  have hstable : (prefixWord ++ tailWord_5658012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658012).length < 2 ^ (prefixWord ++ tailWord_5658012).sum := by decide
  have hdescent : baseEnd_5658012 < baseStart_5658012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658034 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_5658034 : Nat := 118140960795 + 5658034 * 2 ^ 59
def prefixEnd_5658034 : Nat := 4983230072969 + 3 ^ 40 * 5658034 * 2
def baseEnd_5658034 : Nat := 2905291001481221149654181

theorem tailTrace_5658034 : CollatzResearch.WordTrace tailWord_5658034 prefixEnd_5658034 2905291001481221149654181 := by
  unfold tailWord_5658034
  simp only [CollatzResearch.WordTrace]
  refine ⟨51591363395979152030005289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137576969055944405413347437 51591363395979152030005289)
  ·
    refine ⟨38693522546984364022503967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51591363395979152030005289 38693522546984364022503967)
    ·
      refine ⟨58040283820476546033755951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38693522546984364022503967 58040283820476546033755951)
      ·
        refine ⟨87060425730714819050633927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58040283820476546033755951 87060425730714819050633927)
        ·
          refine ⟨130590638596072228575950891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87060425730714819050633927 130590638596072228575950891)
          ·
            refine ⟨195885957894108342863926337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130590638596072228575950891 195885957894108342863926337)
            ·
              refine ⟨146914468420581257147944753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195885957894108342863926337 146914468420581257147944753)
              ·
                refine ⟨110185851315435942860958565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146914468420581257147944753 110185851315435942860958565)
                ·
                  refine ⟨20659847121644239286429731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110185851315435942860958565 20659847121644239286429731)
                  ·
                    refine ⟨30989770682466358929644597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20659847121644239286429731 30989770682466358929644597)
                    ·
                      refine ⟨2905291001481221149654181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30989770682466358929644597 2905291001481221149654181)
                      ·
                        rfl

theorem cell23_5658034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_5658034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658034 prefixEnd_5658034 := by exact prefixLift 5658034
  have htrace : WordTrace (prefixWord ++ tailWord_5658034) baseStart_5658034 baseEnd_5658034 := by
    simpa [prefixWord, tailWord_5658034, baseEnd_5658034] using wordTrace_append hprefix tailTrace_5658034
  have hstable : (prefixWord ++ tailWord_5658034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658034).length < 2 ^ (prefixWord ++ tailWord_5658034).sum := by decide
  have hdescent : baseEnd_5658034 < baseStart_5658034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658041 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 2, 6]
def baseStart_5658041 : Nat := 118140960795 + 5658041 * 2 ^ 59
def prefixEnd_5658041 : Nat := 4983230072969 + 3 ^ 40 * 5658041 * 2
def baseEnd_5658041 : Nat := 968431531948600874088883

theorem tailTrace_5658041 : CollatzResearch.WordTrace tailWord_5658041 prefixEnd_5658041 968431531948600874088883 := by
  unfold tailWord_5658041
  simp only [CollatzResearch.WordTrace]
  refine ⟨206365708894891248315525977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137577139263260832210350651 206365708894891248315525977)
  ·
    refine ⟨154774281671168436236644483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206365708894891248315525977 154774281671168436236644483)
    ·
      refine ⟨232161422506752654354966725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154774281671168436236644483 232161422506752654354966725)
      ·
        refine ⟨43530266720016122691556261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232161422506752654354966725 43530266720016122691556261)
        ·
          refine ⟨8161925010003023004666799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43530266720016122691556261 8161925010003023004666799)
          ·
            refine ⟨12242887515004534507000199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8161925010003023004666799 12242887515004534507000199)
            ·
              refine ⟨18364331272506801760500299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12242887515004534507000199 18364331272506801760500299)
              ·
                refine ⟨27546496908760202640750449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18364331272506801760500299 27546496908760202640750449)
                ·
                  refine ⟨20659872681570151980562837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27546496908760202640750449 20659872681570151980562837)
                  ·
                    refine ⟨968431531948600874088883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20659872681570151980562837 968431531948600874088883)
                    ·
                      rfl

theorem cell23_5658041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 6].length) (baseStart_5658041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658041 prefixEnd_5658041 := by exact prefixLift 5658041
  have htrace : WordTrace (prefixWord ++ tailWord_5658041) baseStart_5658041 baseEnd_5658041 := by
    simpa [prefixWord, tailWord_5658041, baseEnd_5658041] using wordTrace_append hprefix tailTrace_5658041
  have hstable : (prefixWord ++ tailWord_5658041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658041).length < 2 ^ (prefixWord ++ tailWord_5658041).sum := by decide
  have hdescent : baseEnd_5658041 < baseStart_5658041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658081 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 2, 3, 3]
def baseStart_5658081 : Nat := 118140960795 + 5658081 * 2 ^ 59
def prefixEnd_5658081 : Nat := 4983230072969 + 3 ^ 40 * 5658081 * 2
def baseEnd_5658081 : Nat := 2905315135071982465766465

theorem tailTrace_5658081 : CollatzResearch.WordTrace tailWord_5658081 prefixEnd_5658081 2905315135071982465766465 := by
  unfold tailWord_5658081
  simp only [CollatzResearch.WordTrace]
  refine ⟨206367167814746335146982097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137578111876497556764654731 206367167814746335146982097)
  ·
    refine ⟨154775375861059751360236573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206367167814746335146982097 154775375861059751360236573)
    ·
      refine ⟨58040765947897406760088715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154775375861059751360236573 58040765947897406760088715)
      ·
        refine ⟨87061148921846110140133073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58040765947897406760088715 87061148921846110140133073)
        ·
          refine ⟨65295861691384582605099805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87061148921846110140133073 65295861691384582605099805)
          ·
            refine ⟨24485948134269218476912427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65295861691384582605099805 24485948134269218476912427)
            ·
              refine ⟨36728922201403827715368641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24485948134269218476912427 36728922201403827715368641)
              ·
                refine ⟨27546691651052870786526481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36728922201403827715368641 27546691651052870786526481)
                ·
                  refine ⟨20660018738289653089894861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27546691651052870786526481 20660018738289653089894861)
                  ·
                    refine ⟨7747507026858619908710573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20660018738289653089894861 7747507026858619908710573)
                    ·
                      refine ⟨2905315135071982465766465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7747507026858619908710573 2905315135071982465766465)
                      ·
                        rfl

theorem cell23_5658081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_5658081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658081 prefixEnd_5658081 := by exact prefixLift 5658081
  have htrace : WordTrace (prefixWord ++ tailWord_5658081) baseStart_5658081 baseEnd_5658081 := by
    simpa [prefixWord, tailWord_5658081, baseEnd_5658081] using wordTrace_append hprefix tailTrace_5658081
  have hstable : (prefixWord ++ tailWord_5658081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658081).length < 2 ^ (prefixWord ++ tailWord_5658081).sum := by decide
  have hdescent : baseEnd_5658081 < baseStart_5658081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658091 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 2, 5, 2]
def baseStart_5658091 : Nat := 118140960795 + 5658091 * 2 ^ 59
def prefixEnd_5658091 : Nat := 4983230072969 + 3 ^ 40 * 5658091 * 2
def baseEnd_5658091 : Nat := 2905320269878527426641419

theorem tailTrace_5658091 : CollatzResearch.WordTrace tailWord_5658091 prefixEnd_5658091 2905320269878527426641419 := by
  unfold tailWord_5658091
  simp only [CollatzResearch.WordTrace]
  refine ⟨206367532544710106854846127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137578355029806737903230751 206367532544710106854846127)
  ·
    refine ⟨309551298817065160282269191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206367532544710106854846127 309551298817065160282269191)
    ·
      refine ⟨464326948225597740423403787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309551298817065160282269191 464326948225597740423403787)
      ·
        refine ⟨696490422338396610635105681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464326948225597740423403787 696490422338396610635105681)
        ·
          refine ⟨522367816753797457976329261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 696490422338396610635105681 522367816753797457976329261)
          ·
            refine ⟨195887931282674046741123473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 522367816753797457976329261 195887931282674046741123473)
            ·
              refine ⟨146915948462005535055842605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195887931282674046741123473 146915948462005535055842605)
              ·
                refine ⟨55093480673252075645940977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146915948462005535055842605 55093480673252075645940977)
                ·
                  refine ⟨41320110504939056734455733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55093480673252075645940977 41320110504939056734455733)
                  ·
                    refine ⟨3873760359838036568855225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41320110504939056734455733 3873760359838036568855225)
                    ·
                      refine ⟨2905320269878527426641419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3873760359838036568855225 2905320269878527426641419)
                      ·
                        rfl

theorem cell23_5658091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 5, 2].length) (baseStart_5658091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658091 prefixEnd_5658091 := by exact prefixLift 5658091
  have htrace : WordTrace (prefixWord ++ tailWord_5658091) baseStart_5658091 baseEnd_5658091 := by
    simpa [prefixWord, tailWord_5658091, baseEnd_5658091] using wordTrace_append hprefix tailTrace_5658091
  have hstable : (prefixWord ++ tailWord_5658091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658091).length < 2 ^ (prefixWord ++ tailWord_5658091).sum := by decide
  have hdescent : baseEnd_5658091 < baseStart_5658091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658098 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 2, 3, 3]
def baseStart_5658098 : Nat := 118140960795 + 5658098 * 2 ^ 59
def prefixEnd_5658098 : Nat := 4983230072969 + 3 ^ 40 * 5658098 * 2
def baseEnd_5658098 : Nat := 2905323864243108899253887

theorem tailTrace_5658098 : CollatzResearch.WordTrace tailWord_5658098 prefixEnd_5658098 2905323864243108899253887 := by
  unfold tailWord_5658098
  simp only [CollatzResearch.WordTrace]
  refine ⟨51591946963921186762587737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137578525237123164700233965 51591946963921186762587737)
  ·
    refine ⟨38693960222940890071940803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51591946963921186762587737 38693960222940890071940803)
    ·
      refine ⟨58040940334411335107911205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38693960222940890071940803 58040940334411335107911205)
      ·
        refine ⟨10882676312702125332733351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58040940334411335107911205 10882676312702125332733351)
        ·
          refine ⟨16324014469053187999100027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10882676312702125332733351 16324014469053187999100027)
          ·
            refine ⟨24486021703579781998650041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16324014469053187999100027 24486021703579781998650041)
            ·
              refine ⟨18364516277684836498987531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24486021703579781998650041 18364516277684836498987531)
              ·
                refine ⟨27546774416527254748481297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18364516277684836498987531 27546774416527254748481297)
                ·
                  refine ⟨20660080812395441061360973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27546774416527254748481297 20660080812395441061360973)
                  ·
                    refine ⟨7747530304648290398010365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20660080812395441061360973 7747530304648290398010365)
                    ·
                      refine ⟨2905323864243108899253887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7747530304648290398010365 2905323864243108899253887)
                      ·
                        rfl

theorem cell23_5658098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_5658098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658098 prefixEnd_5658098 := by exact prefixLift 5658098
  have htrace : WordTrace (prefixWord ++ tailWord_5658098) baseStart_5658098 baseEnd_5658098 := by
    simpa [prefixWord, tailWord_5658098, baseEnd_5658098] using wordTrace_append hprefix tailTrace_5658098
  have hstable : (prefixWord ++ tailWord_5658098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658098).length < 2 ^ (prefixWord ++ tailWord_5658098).sum := by decide
  have hdescent : baseEnd_5658098 < baseStart_5658098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658121 : List Nat := [1, 2, 1, 1, 3, 1, 4, 3, 2, 1, 4]
def baseStart_5658121 : Nat := 118140960795 + 5658121 * 2 ^ 59
def prefixEnd_5658121 : Nat := 4983230072969 + 3 ^ 40 * 5658121 * 2
def baseEnd_5658121 : Nat := 2905335674298162309266281

theorem tailTrace_5658121 : CollatzResearch.WordTrace tailWord_5658121 prefixEnd_5658121 2905335674298162309266281 := by
  unfold tailWord_5658121
  simp only [CollatzResearch.WordTrace]
  refine ⟨206368626734601421978438217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137579084489734281318958811 206368626734601421978438217)
  ·
    refine ⟨154776470050951066483828663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206368626734601421978438217 154776470050951066483828663)
    ·
      refine ⟨232164705076426599725742995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154776470050951066483828663 232164705076426599725742995)
      ·
        refine ⟨348247057614639899588614493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232164705076426599725742995 348247057614639899588614493)
        ·
          refine ⟨130592646605489962345730435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348247057614639899588614493 130592646605489962345730435)
          ·
            refine ⟨195888969908234943518595653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130592646605489962345730435 195888969908234943518595653)
            ·
              refine ⟨36729181857794051909736685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195888969908234943518595653 36729181857794051909736685)
              ·
                refine ⟨13773443196672769466151257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36729181857794051909736685 13773443196672769466151257)
                ·
                  refine ⟨10330082397504577099613443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13773443196672769466151257 10330082397504577099613443)
                  ·
                    refine ⟨15495123596256865649420165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10330082397504577099613443 15495123596256865649420165)
                    ·
                      refine ⟨2905335674298162309266281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15495123596256865649420165 2905335674298162309266281)
                      ·
                        rfl

theorem cell23_5658121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 1, 4].length) (baseStart_5658121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658121 prefixEnd_5658121 := by exact prefixLift 5658121
  have htrace : WordTrace (prefixWord ++ tailWord_5658121) baseStart_5658121 baseEnd_5658121 := by
    simpa [prefixWord, tailWord_5658121, baseEnd_5658121] using wordTrace_append hprefix tailTrace_5658121
  have hstable : (prefixWord ++ tailWord_5658121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658121).length < 2 ^ (prefixWord ++ tailWord_5658121).sum := by decide
  have hdescent : baseEnd_5658121 < baseStart_5658121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658222 : List Nat := [4, 1, 2, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_5658222 : Nat := 118140960795 + 5658222 * 2 ^ 59
def prefixEnd_5658222 : Nat := 4983230072969 + 3 ^ 40 * 5658222 * 2
def baseEnd_5658222 : Nat := 2905387535844266414103317

theorem tailTrace_5658222 : CollatzResearch.WordTrace tailWord_5658222 prefixEnd_5658222 2905387535844266414103317 := by
  unfold tailWord_5658222
  simp only [CollatzResearch.WordTrace]
  refine ⟨25796538813404439528483115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137581540338157010818576613 25796538813404439528483115)
  ·
    refine ⟨38694808220106659292724673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25796538813404439528483115 38694808220106659292724673)
    ·
      refine ⟨29021106165079994469543505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38694808220106659292724673 29021106165079994469543505)
      ·
        refine ⟨21765829623809995852157629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29021106165079994469543505 21765829623809995852157629)
        ·
          refine ⟨8162186108928748444559111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21765829623809995852157629 8162186108928748444559111)
          ·
            refine ⟨12243279163393122666838667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8162186108928748444559111 12243279163393122666838667)
            ·
              refine ⟨18364918745089684000258001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12243279163393122666838667 18364918745089684000258001)
              ·
                refine ⟨13773689058817263000193501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18364918745089684000258001 13773689058817263000193501)
                ·
                  refine ⟨5165133397056473625072563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13773689058817263000193501 5165133397056473625072563)
                  ·
                    refine ⟨7747700095584710437608845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5165133397056473625072563 7747700095584710437608845)
                    ·
                      refine ⟨2905387535844266414103317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7747700095584710437608845 2905387535844266414103317)
                      ·
                        rfl

theorem cell23_5658222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_5658222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658222 prefixEnd_5658222 := by exact prefixLift 5658222
  have htrace : WordTrace (prefixWord ++ tailWord_5658222) baseStart_5658222 baseEnd_5658222 := by
    simpa [prefixWord, tailWord_5658222, baseEnd_5658222] using wordTrace_append hprefix tailTrace_5658222
  have hstable : (prefixWord ++ tailWord_5658222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658222).length < 2 ^ (prefixWord ++ tailWord_5658222).sum := by decide
  have hdescent : baseEnd_5658222 < baseStart_5658222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658245 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 5, 2, 2]
def baseStart_5658245 : Nat := 118140960795 + 5658245 * 2 ^ 59
def prefixEnd_5658245 : Nat := 4983230072969 + 3 ^ 40 * 5658245 * 2
def baseEnd_5658245 : Nat := 2905399345899319824115711

theorem tailTrace_5658245 : CollatzResearch.WordTrace tailWord_5658245 prefixEnd_5658245 2905399345899319824115711 := by
  unfold tailWord_5658245
  simp only [CollatzResearch.WordTrace]
  refine ⟨206373149386152191155952189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137582099590768127437301459 206373149386152191155952189)
  ·
    refine ⟨77389931019807071683482071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206373149386152191155952189 77389931019807071683482071)
    ·
      refine ⟨116084896529710607525223107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77389931019807071683482071 116084896529710607525223107)
      ·
        refine ⟨174127344794565911287834661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116084896529710607525223107 174127344794565911287834661)
        ·
          refine ⟨32648877148981108366468999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174127344794565911287834661 32648877148981108366468999)
          ·
            refine ⟨48973315723471662549703499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32648877148981108366468999 48973315723471662549703499)
            ·
              refine ⟨73459973585207493824555249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48973315723471662549703499 73459973585207493824555249)
              ·
                refine ⟨55094980188905620368416437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73459973585207493824555249 55094980188905620368416437)
                ·
                  refine ⟨5165154392709901909539041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55094980188905620368416437 5165154392709901909539041)
                  ·
                    refine ⟨3873865794532426432154281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5165154392709901909539041 3873865794532426432154281)
                    ·
                      refine ⟨2905399345899319824115711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3873865794532426432154281 2905399345899319824115711)
                      ·
                        rfl

theorem cell23_5658245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 2, 2].length) (baseStart_5658245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658245 prefixEnd_5658245 := by exact prefixLift 5658245
  have htrace : WordTrace (prefixWord ++ tailWord_5658245) baseStart_5658245 baseEnd_5658245 := by
    simpa [prefixWord, tailWord_5658245, baseEnd_5658245] using wordTrace_append hprefix tailTrace_5658245
  have hstable : (prefixWord ++ tailWord_5658245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658245).length < 2 ^ (prefixWord ++ tailWord_5658245).sum := by decide
  have hdescent : baseEnd_5658245 < baseStart_5658245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658272 : List Nat := [2, 1, 1, 4, 3, 2, 3, 1, 2, 4]
def baseStart_5658272 : Nat := 118140960795 + 5658272 * 2 ^ 59
def prefixEnd_5658272 : Nat := 4983230072969 + 3 ^ 40 * 5658272 * 2
def baseEnd_5658272 : Nat := 968471069958997072826029

theorem tailTrace_5658272 : CollatzResearch.WordTrace tailWord_5658272 prefixEnd_5658272 968471069958997072826029 := by
  unfold tailWord_5658272
  simp only [CollatzResearch.WordTrace]
  refine ⟨103187067078527187383592535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137582756104702916511456713 103187067078527187383592535)
  ·
    refine ⟨154780600617790781075388803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103187067078527187383592535 154780600617790781075388803)
    ·
      refine ⟨232170900926686171613083205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154780600617790781075388803 232170900926686171613083205)
      ·
        refine ⟨43532043923753657177453101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232170900926686171613083205 43532043923753657177453101)
        ·
          refine ⟨16324516471407621441544913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43532043923753657177453101 16324516471407621441544913)
          ·
            refine ⟨12243387353555716081158685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16324516471407621441544913 12243387353555716081158685)
            ·
              refine ⟨4591270257583393530434507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12243387353555716081158685 4591270257583393530434507)
              ·
                refine ⟨6886905386375090295651761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4591270257583393530434507 6886905386375090295651761)
                ·
                  refine ⟨5165179039781317721738821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6886905386375090295651761 5165179039781317721738821)
                  ·
                    refine ⟨968471069958997072826029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5165179039781317721738821 968471069958997072826029)
                    ·
                      rfl

theorem cell23_5658272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 2, 4].length) (baseStart_5658272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658272 prefixEnd_5658272 := by exact prefixLift 5658272
  have htrace : WordTrace (prefixWord ++ tailWord_5658272) baseStart_5658272 baseEnd_5658272 := by
    simpa [prefixWord, tailWord_5658272, baseEnd_5658272] using wordTrace_append hprefix tailTrace_5658272
  have hstable : (prefixWord ++ tailWord_5658272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658272).length < 2 ^ (prefixWord ++ tailWord_5658272).sum := by decide
  have hdescent : baseEnd_5658272 < baseStart_5658272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658291 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 5]
def baseStart_5658291 : Nat := 118140960795 + 5658291 * 2 ^ 59
def prefixEnd_5658291 : Nat := 4983230072969 + 3 ^ 40 * 5658291 * 2
def baseEnd_5658291 : Nat := 2905422966009426644140499

theorem tailTrace_5658291 : CollatzResearch.WordTrace tailWord_5658291 prefixEnd_5658291 2905422966009426644140499 := by
  unfold tailWord_5658291
  simp only [CollatzResearch.WordTrace]
  refine ⟨206374827143985541012126727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137583218095990360674751151 206374827143985541012126727)
  ·
    refine ⟨309562240715978311518190091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206374827143985541012126727 309562240715978311518190091)
    ·
      refine ⟨464343361073967467277285137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309562240715978311518190091 464343361073967467277285137)
      ·
        refine ⟨348257520805475600457963853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 464343361073967467277285137 348257520805475600457963853)
        ·
          refine ⟨130596570302053350171736445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348257520805475600457963853 130596570302053350171736445)
          ·
            refine ⟨48973713863270006314401167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130596570302053350171736445 48973713863270006314401167)
            ·
              refine ⟨73460570794905009471601751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48973713863270006314401167 73460570794905009471601751)
              ·
                refine ⟨110190856192357514207402627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73460570794905009471601751 110190856192357514207402627)
                ·
                  refine ⟨165286284288536271311103941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110190856192357514207402627 165286284288536271311103941)
                  ·
                    refine ⟨30991178304100550870831989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 165286284288536271311103941 30991178304100550870831989)
                    ·
                      refine ⟨2905422966009426644140499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30991178304100550870831989 2905422966009426644140499)
                      ·
                        rfl

theorem cell23_5658291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_5658291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658291 prefixEnd_5658291 := by exact prefixLift 5658291
  have htrace : WordTrace (prefixWord ++ tailWord_5658291) baseStart_5658291 baseEnd_5658291 := by
    simpa [prefixWord, tailWord_5658291, baseEnd_5658291] using wordTrace_append hprefix tailTrace_5658291
  have hstable : (prefixWord ++ tailWord_5658291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658291).length < 2 ^ (prefixWord ++ tailWord_5658291).sum := by decide
  have hdescent : baseEnd_5658291 < baseStart_5658291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658295 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 4, 1, 3]
def baseStart_5658295 : Nat := 118140960795 + 5658295 * 2 ^ 59
def prefixEnd_5658295 : Nat := 4983230072969 + 3 ^ 40 * 5658295 * 2
def baseEnd_5658295 : Nat := 2905425019932044628490481

theorem tailTrace_5658295 : CollatzResearch.WordTrace tailWord_5658295 prefixEnd_5658295 2905425019932044628490481 := by
  unfold tailWord_5658295
  simp only [CollatzResearch.WordTrace]
  refine ⟨206374973035971049695272339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137583315357314033130181559 206374973035971049695272339)
  ·
    refine ⟨309562459553956574542908509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206374973035971049695272339 309562459553956574542908509)
    ·
      refine ⟨116085922332733715453590691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309562459553956574542908509 116085922332733715453590691)
      ·
        refine ⟨174128883499100573180386037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116085922332733715453590691 174128883499100573180386037)
        ·
          refine ⟨16324582828040678735661191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174128883499100573180386037 16324582828040678735661191)
          ·
            refine ⟨24486874242061018103491787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16324582828040678735661191 24486874242061018103491787)
            ·
              refine ⟨36730311363091527155237681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24486874242061018103491787 36730311363091527155237681)
              ·
                refine ⟨27547733522318645366428261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36730311363091527155237681 27547733522318645366428261)
                ·
                  refine ⟨5165200035434746006205299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27547733522318645366428261 5165200035434746006205299)
                  ·
                    refine ⟨7747800053152119009307949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5165200035434746006205299 7747800053152119009307949)
                    ·
                      refine ⟨2905425019932044628490481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7747800053152119009307949 2905425019932044628490481)
                      ·
                        rfl

theorem cell23_5658295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 1, 3].length) (baseStart_5658295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658295 prefixEnd_5658295 := by exact prefixLift 5658295
  have htrace : WordTrace (prefixWord ++ tailWord_5658295) baseStart_5658295 baseEnd_5658295 := by
    simpa [prefixWord, tailWord_5658295, baseEnd_5658295] using wordTrace_append hprefix tailTrace_5658295
  have hstable : (prefixWord ++ tailWord_5658295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658295).length < 2 ^ (prefixWord ++ tailWord_5658295).sum := by decide
  have hdescent : baseEnd_5658295 < baseStart_5658295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658308 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_5658308 : Nat := 118140960795 + 5658308 * 2 ^ 59
def prefixEnd_5658308 : Nat := 4983230072969 + 3 ^ 40 * 5658308 * 2
def baseEnd_5658308 : Nat := 2905431695180553077627921

theorem tailTrace_5658308 : CollatzResearch.WordTrace tailWord_5658308 prefixEnd_5658308 2905431695180553077627921 := by
  unfold tailWord_5658308
  simp only [CollatzResearch.WordTrace]
  refine ⟨103187723592461976457747789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137583631456615968610330385 103187723592461976457747789)
  ·
    refine ⟨38695396347173241171655421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103187723592461976457747789 38695396347173241171655421)
    ·
      refine ⟨14510773630189965439370783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38695396347173241171655421 14510773630189965439370783)
      ·
        refine ⟨21766160445284948159056175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14510773630189965439370783 21766160445284948159056175)
        ·
          refine ⟨32649240667927422238584263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21766160445284948159056175 32649240667927422238584263)
          ·
            refine ⟨48973861001891133357876395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32649240667927422238584263 48973861001891133357876395)
            ·
              refine ⟨73460791502836700036814593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48973861001891133357876395 73460791502836700036814593)
              ·
                refine ⟨55095593627127525027610945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73460791502836700036814593 55095593627127525027610945)
                ·
                  refine ⟨41321695220345643770708209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55095593627127525027610945 41321695220345643770708209)
                  ·
                    refine ⟨30991271415259232828031157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41321695220345643770708209 30991271415259232828031157)
                    ·
                      refine ⟨2905431695180553077627921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30991271415259232828031157 2905431695180553077627921)
                      ·
                        rfl

theorem cell23_5658308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_5658308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658308 prefixEnd_5658308 := by exact prefixLift 5658308
  have htrace : WordTrace (prefixWord ++ tailWord_5658308) baseStart_5658308 baseEnd_5658308 := by
    simpa [prefixWord, tailWord_5658308, baseEnd_5658308] using wordTrace_append hprefix tailTrace_5658308
  have hstable : (prefixWord ++ tailWord_5658308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658308).length < 2 ^ (prefixWord ++ tailWord_5658308).sum := by decide
  have hdescent : baseEnd_5658308 < baseStart_5658308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658318 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_5658318 : Nat := 118140960795 + 5658318 * 2 ^ 59
def prefixEnd_5658318 : Nat := 4983230072969 + 3 ^ 40 * 5658318 * 2
def baseEnd_5658318 : Nat := 2905436829987098038502875

theorem tailTrace_5658318 : CollatzResearch.WordTrace tailWord_5658318 prefixEnd_5658318 2905436829987098038502875 := by
  unfold tailWord_5658318
  simp only [CollatzResearch.WordTrace]
  refine ⟨25796976489360965577919951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137583874609925149748906405 25796976489360965577919951)
  ·
    refine ⟨38695464734041448366879927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25796976489360965577919951 38695464734041448366879927)
    ·
      refine ⟨58043197101062172550319891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38695464734041448366879927 58043197101062172550319891)
      ·
        refine ⟨87064795651593258825479837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58043197101062172550319891 87064795651593258825479837)
        ·
          refine ⟨32649298369347472059554939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87064795651593258825479837 32649298369347472059554939)
          ·
            refine ⟨48973947554021208089332409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32649298369347472059554939 48973947554021208089332409)
            ·
              refine ⟨36730460665515906066999307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48973947554021208089332409 36730460665515906066999307)
              ·
                refine ⟨55095690998273859100498961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36730460665515906066999307 55095690998273859100498961)
                ·
                  refine ⟨41321768248705394325374221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55095690998273859100498961 41321768248705394325374221)
                  ·
                    refine ⟨15495663093264522872015333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41321768248705394325374221 15495663093264522872015333)
                    ·
                      refine ⟨2905436829987098038502875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15495663093264522872015333 2905436829987098038502875)
                      ·
                        rfl

theorem cell23_5658318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_5658318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658318 prefixEnd_5658318 := by exact prefixLift 5658318
  have htrace : WordTrace (prefixWord ++ tailWord_5658318) baseStart_5658318 baseEnd_5658318 := by
    simpa [prefixWord, tailWord_5658318, baseEnd_5658318] using wordTrace_append hprefix tailTrace_5658318
  have hstable : (prefixWord ++ tailWord_5658318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658318).length < 2 ^ (prefixWord ++ tailWord_5658318).sum := by decide
  have hdescent : baseEnd_5658318 < baseStart_5658318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658329 : List Nat := [1, 2, 1, 2, 3, 5, 2, 1, 2, 1, 3]
def baseStart_5658329 : Nat := 118140960795 + 5658329 * 2 ^ 59
def prefixEnd_5658329 : Nat := 4983230072969 + 3 ^ 40 * 5658329 * 2
def baseEnd_5658329 : Nat := 2905442478274297495465325

theorem tailTrace_5658329 : CollatzResearch.WordTrace tailWord_5658329 prefixEnd_5658329 2905442478274297495465325 := by
  unfold tailWord_5658329
  simp only [CollatzResearch.WordTrace]
  refine ⟨206376213117847873502010041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137584142078565249001340027 206376213117847873502010041)
  ·
    refine ⟨154782159838385905126507531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206376213117847873502010041 154782159838385905126507531)
    ·
      refine ⟨232173239757578857689761297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154782159838385905126507531 232173239757578857689761297)
      ·
        refine ⟨174129929818184143267320973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232173239757578857689761297 174129929818184143267320973)
        ·
          refine ⟨65298723681819053725245365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174129929818184143267320973 65298723681819053725245365)
          ·
            refine ⟨6121755345170536286741753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65298723681819053725245365 6121755345170536286741753)
            ·
              refine ⟨4591316508877902215056315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6121755345170536286741753 4591316508877902215056315)
              ·
                refine ⟨6886974763316853322584473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4591316508877902215056315 6886974763316853322584473)
                ·
                  refine ⟨5165231072487639991938355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6886974763316853322584473 5165231072487639991938355)
                  ·
                    refine ⟨7747846608731459987907533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5165231072487639991938355 7747846608731459987907533)
                    ·
                      refine ⟨2905442478274297495465325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7747846608731459987907533 2905442478274297495465325)
                      ·
                        rfl

theorem cell23_5658329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 2, 1, 3].length) (baseStart_5658329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658329 prefixEnd_5658329 := by exact prefixLift 5658329
  have htrace : WordTrace (prefixWord ++ tailWord_5658329) baseStart_5658329 baseEnd_5658329 := by
    simpa [prefixWord, tailWord_5658329, baseEnd_5658329] using wordTrace_append hprefix tailTrace_5658329
  have hstable : (prefixWord ++ tailWord_5658329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658329).length < 2 ^ (prefixWord ++ tailWord_5658329).sum := by decide
  have hdescent : baseEnd_5658329 < baseStart_5658329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658335 : List Nat := [1, 1, 2, 3, 2, 2, 2, 3, 1, 4, 2]
def baseStart_5658335 : Nat := 118140960795 + 5658335 * 2 ^ 59
def prefixEnd_5658335 : Nat := 4983230072969 + 3 ^ 40 * 5658335 * 2
def baseEnd_5658335 : Nat := 2905445559158224471990297

theorem tailTrace_5658335 : CollatzResearch.WordTrace tailWord_5658335 prefixEnd_5658335 2905445559158224471990297 := by
  unfold tailWord_5658335
  simp only [CollatzResearch.WordTrace]
  refine ⟨206376431955826136526728459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137584287970550757684485639 206376431955826136526728459)
  ·
    refine ⟨309564647933739204790092689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206376431955826136526728459 309564647933739204790092689)
    ·
      refine ⟨232173485950304403592569517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309564647933739204790092689 232173485950304403592569517)
      ·
        refine ⟨87065057231364151347213569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232173485950304403592569517 87065057231364151347213569)
        ·
          refine ⟨65298792923523113510410177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87065057231364151347213569 65298792923523113510410177)
          ·
            refine ⟨48974094692642335132807633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65298792923523113510410177 48974094692642335132807633)
            ·
              refine ⟨36730571019481751349605725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48974094692642335132807633 36730571019481751349605725)
              ·
                refine ⟨13773964132305656756102147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36730571019481751349605725 13773964132305656756102147)
                ·
                  refine ⟨20660946198458485134153221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13773964132305656756102147 20660946198458485134153221)
                  ·
                    refine ⟨3873927412210965962653729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20660946198458485134153221 3873927412210965962653729)
                    ·
                      refine ⟨2905445559158224471990297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3873927412210965962653729 2905445559158224471990297)
                      ·
                        rfl

theorem cell23_5658335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_5658335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658335 prefixEnd_5658335 := by exact prefixLift 5658335
  have htrace : WordTrace (prefixWord ++ tailWord_5658335) baseStart_5658335 baseEnd_5658335 := by
    simpa [prefixWord, tailWord_5658335, baseEnd_5658335] using wordTrace_append hprefix tailTrace_5658335
  have hstable : (prefixWord ++ tailWord_5658335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658335).length < 2 ^ (prefixWord ++ tailWord_5658335).sum := by decide
  have hdescent : baseEnd_5658335 < baseStart_5658335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658368 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 3]
def baseStart_5658368 : Nat := 118140960795 + 5658368 * 2 ^ 59
def prefixEnd_5658368 : Nat := 4983230072969 + 3 ^ 40 * 5658368 * 2
def baseEnd_5658368 : Nat := 2905462504019822842877645

theorem tailTrace_5658368 : CollatzResearch.WordTrace tailWord_5658368 prefixEnd_5658368 2905462504019822842877645 := by
  unfold tailWord_5658368
  simp only [CollatzResearch.WordTrace]
  refine ⟨103188817782353291581339879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137585090376471055441786505 103188817782353291581339879)
  ·
    refine ⟨154783226673529937372009819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103188817782353291581339879 154783226673529937372009819)
    ·
      refine ⟨232174840010294906058014729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154783226673529937372009819 232174840010294906058014729)
      ·
        refine ⟨174131130007721179543511047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232174840010294906058014729 174131130007721179543511047)
        ·
          refine ⟨261196695011581769315266571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174131130007721179543511047 261196695011581769315266571)
          ·
            refine ⟨391795042517372653972899857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261196695011581769315266571 391795042517372653972899857)
            ·
              refine ⟨293846281888029490479674893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391795042517372653972899857 293846281888029490479674893)
              ·
                refine ⟨110192355708011058929878085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293846281888029490479674893 110192355708011058929878085)
                ·
                  refine ⟨20661066695252073549352141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110192355708011058929878085 20661066695252073549352141)
                  ·
                    refine ⟨7747900010719527581007053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20661066695252073549352141 7747900010719527581007053)
                    ·
                      refine ⟨2905462504019822842877645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7747900010719527581007053 2905462504019822842877645)
                      ·
                        rfl

theorem cell23_5658368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_5658368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658368 prefixEnd_5658368 := by exact prefixLift 5658368
  have htrace : WordTrace (prefixWord ++ tailWord_5658368) baseStart_5658368 baseEnd_5658368 := by
    simpa [prefixWord, tailWord_5658368, baseEnd_5658368] using wordTrace_append hprefix tailTrace_5658368
  have hstable : (prefixWord ++ tailWord_5658368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658368).length < 2 ^ (prefixWord ++ tailWord_5658368).sum := by decide
  have hdescent : baseEnd_5658368 < baseStart_5658368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658386 : List Nat := [3, 2, 4, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_5658386 : Nat := 118140960795 + 5658386 * 2 ^ 59
def prefixEnd_5658386 : Nat := 4983230072969 + 3 ^ 40 * 5658386 * 2
def baseEnd_5658386 : Nat := 2905471746671603772452563

theorem tailTrace_5658386 : CollatzResearch.WordTrace tailWord_5658386 prefixEnd_5658386 2905471746671603772452563 := by
  unfold tailWord_5658386
  simp only [CollatzResearch.WordTrace]
  refine ⟨51594573019660343059208753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137585528052427581491223341 51594573019660343059208753)
  ·
    refine ⟨38695929764745257294406565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51594573019660343059208753 38695929764745257294406565)
    ·
      refine ⟨7255486830889735742701231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38695929764745257294406565 7255486830889735742701231)
      ·
        refine ⟨10883230246334603614051847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7255486830889735742701231 10883230246334603614051847)
        ·
          refine ⟨16324845369501905421077771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10883230246334603614051847 16324845369501905421077771)
          ·
            refine ⟨24487268054252858131616657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16324845369501905421077771 24487268054252858131616657)
            ·
              refine ⟨18365451040689643598712493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24487268054252858131616657 18365451040689643598712493)
              ·
                refine ⟨6887044140258616349517185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18365451040689643598712493 6887044140258616349517185)
                ·
                  refine ⟨5165283105193962262137889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6887044140258616349517185 5165283105193962262137889)
                  ·
                    refine ⟨3873962328895471696603417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5165283105193962262137889 3873962328895471696603417)
                    ·
                      refine ⟨2905471746671603772452563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3873962328895471696603417 2905471746671603772452563)
                      ·
                        rfl

theorem cell23_5658386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_5658386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658386 prefixEnd_5658386 := by exact prefixLift 5658386
  have htrace : WordTrace (prefixWord ++ tailWord_5658386) baseStart_5658386 baseEnd_5658386 := by
    simpa [prefixWord, tailWord_5658386, baseEnd_5658386] using wordTrace_append hprefix tailTrace_5658386
  have hstable : (prefixWord ++ tailWord_5658386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658386).length < 2 ^ (prefixWord ++ tailWord_5658386).sum := by decide
  have hdescent : baseEnd_5658386 < baseStart_5658386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658405 : List Nat := [1, 3, 1, 2, 3, 2, 3, 1, 2, 5]
def baseStart_5658405 : Nat := 118140960795 + 5658405 * 2 ^ 59
def prefixEnd_5658405 : Nat := 4983230072969 + 3 ^ 40 * 5658405 * 2
def baseEnd_5658405 : Nat := 968493834268013066038325

theorem tailTrace_5658405 : CollatzResearch.WordTrace tailWord_5658405 prefixEnd_5658405 968493834268013066038325 := by
  unfold tailWord_5658405
  simp only [CollatzResearch.WordTrace]
  refine ⟨206378985065572538481776669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137585990043715025654517779 206378985065572538481776669)
  ·
    refine ⟨77392119399589701930666251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206378985065572538481776669 77392119399589701930666251)
    ·
      refine ⟨116088179099384552895999377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77392119399589701930666251 116088179099384552895999377)
      ·
        refine ⟨87066134324538414671999533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116088179099384552895999377 87066134324538414671999533)
        ·
          refine ⟨32649800371701905501999825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87066134324538414671999533 32649800371701905501999825)
          ·
            refine ⟨24487350278776429126499869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32649800371701905501999825 24487350278776429126499869)
            ·
              refine ⟨9182756354541160922437451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24487350278776429126499869 9182756354541160922437451)
              ·
                refine ⟨13774134531811741383656177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9182756354541160922437451 13774134531811741383656177)
                ·
                  refine ⟨10330600898858806037742133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13774134531811741383656177 10330600898858806037742133)
                  ·
                    refine ⟨968493834268013066038325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10330600898858806037742133 968493834268013066038325)
                    ·
                      rfl

theorem cell23_5658405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_5658405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658405 prefixEnd_5658405 := by exact prefixLift 5658405
  have htrace : WordTrace (prefixWord ++ tailWord_5658405) baseStart_5658405 baseEnd_5658405 := by
    simpa [prefixWord, tailWord_5658405, baseEnd_5658405] using wordTrace_append hprefix tailTrace_5658405
  have hstable : (prefixWord ++ tailWord_5658405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658405).length < 2 ^ (prefixWord ++ tailWord_5658405).sum := by decide
  have hdescent : baseEnd_5658405 < baseStart_5658405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658428 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_5658428 : Nat := 118140960795 + 5658428 * 2 ^ 59
def prefixEnd_5658428 : Nat := 4983230072969 + 3 ^ 40 * 5658428 * 2
def baseEnd_5658428 : Nat := 2905493312859092608127369

theorem tailTrace_5658428 : CollatzResearch.WordTrace tailWord_5658428 prefixEnd_5658428 2905493312859092608127369 := by
  unfold tailWord_5658428
  simp only [CollatzResearch.WordTrace]
  refine ⟨103189911972244606704931969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137586549296326142273242625 103189911972244606704931969)
  ·
    refine ⟨77392433979183455028698977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103189911972244606704931969 77392433979183455028698977)
    ·
      refine ⟨58044325484387591271524233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77392433979183455028698977 58044325484387591271524233)
      ·
        refine ⟨43533244113290693453643175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58044325484387591271524233 43533244113290693453643175)
        ·
          refine ⟨65299866169936040180464763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43533244113290693453643175 65299866169936040180464763)
          ·
            refine ⟨97949799254904060270697145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65299866169936040180464763 97949799254904060270697145)
            ·
              refine ⟨73462349441178045203022859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97949799254904060270697145 73462349441178045203022859)
              ·
                refine ⟨110193524161767067804534289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73462349441178045203022859 110193524161767067804534289)
                ·
                  refine ⟨82645143121325300853400717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110193524161767067804534289 82645143121325300853400717)
                  ·
                    refine ⟨30991928670496987820025269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82645143121325300853400717 30991928670496987820025269)
                    ·
                      refine ⟨2905493312859092608127369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30991928670496987820025269 2905493312859092608127369)
                      ·
                        rfl

theorem cell23_5658428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_5658428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658428 prefixEnd_5658428 := by exact prefixLift 5658428
  have htrace : WordTrace (prefixWord ++ tailWord_5658428) baseStart_5658428 baseEnd_5658428 := by
    simpa [prefixWord, tailWord_5658428, baseEnd_5658428] using wordTrace_append hprefix tailTrace_5658428
  have hstable : (prefixWord ++ tailWord_5658428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658428).length < 2 ^ (prefixWord ++ tailWord_5658428).sum := by decide
  have hdescent : baseEnd_5658428 < baseStart_5658428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658435 : List Nat := [1, 1, 1, 3, 1, 5, 1, 3, 3, 4]
def baseStart_5658435 : Nat := 118140960795 + 5658435 * 2 ^ 59
def prefixEnd_5658435 : Nat := 4983230072969 + 3 ^ 40 * 5658435 * 2
def baseEnd_5658435 : Nat := 968498969074558026913279

theorem tailTrace_5658435 : CollatzResearch.WordTrace tailWord_5658435 prefixEnd_5658435 968498969074558026913279 := by
  unfold tailWord_5658435
  simp only [CollatzResearch.WordTrace]
  refine ⟨206380079255463853605368759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137586719503642569070245839 206380079255463853605368759)
  ·
    refine ⟨309570118883195780408053139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206380079255463853605368759 309570118883195780408053139)
    ·
      refine ⟨464355178324793670612079709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309570118883195780408053139 464355178324793670612079709)
      ·
        refine ⟨174133191871797626479529891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 464355178324793670612079709 174133191871797626479529891)
        ·
          refine ⟨261199787807696439719294837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174133191871797626479529891 261199787807696439719294837)
          ·
            refine ⟨24487480106971541223683891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 261199787807696439719294837 24487480106971541223683891)
            ·
              refine ⟨36731220160457311835525837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24487480106971541223683891 36731220160457311835525837)
              ·
                refine ⟨13774207560171491938322189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36731220160457311835525837 13774207560171491938322189)
                ·
                  refine ⟨5165327835064309476870821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13774207560171491938322189 5165327835064309476870821)
                  ·
                    refine ⟨968498969074558026913279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5165327835064309476870821 968498969074558026913279)
                    ·
                      rfl

theorem cell23_5658435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 4].length) (baseStart_5658435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658435 prefixEnd_5658435 := by exact prefixLift 5658435
  have htrace : WordTrace (prefixWord ++ tailWord_5658435) baseStart_5658435 baseEnd_5658435 := by
    simpa [prefixWord, tailWord_5658435, baseEnd_5658435] using wordTrace_append hprefix tailTrace_5658435
  have hstable : (prefixWord ++ tailWord_5658435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658435).length < 2 ^ (prefixWord ++ tailWord_5658435).sum := by decide
  have hdescent : baseEnd_5658435 < baseStart_5658435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658452 : List Nat := [2, 4, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_5658452 : Nat := 118140960795 + 5658452 * 2 ^ 59
def prefixEnd_5658452 : Nat := 4983230072969 + 3 ^ 40 * 5658452 * 2
def baseEnd_5658452 : Nat := 968501878798266838075753

theorem tailTrace_5658452 : CollatzResearch.WordTrace tailWord_5658452 prefixEnd_5658452 968501878798266838075753 := by
  unfold tailWord_5658452
  simp only [CollatzResearch.WordTrace]
  refine ⟨103190349648201132754368805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137587132864268177005825073 103190349648201132754368805)
  ·
    refine ⟨19348190559037712391444151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103190349648201132754368805 19348190559037712391444151)
    ·
      refine ⟨29022285838556568587166227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19348190559037712391444151 29022285838556568587166227)
      ·
        refine ⟨43533428757834852880749341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29022285838556568587166227 43533428757834852880749341)
        ·
          refine ⟨16325035784188069830281003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43533428757834852880749341 16325035784188069830281003)
          ·
            refine ⟨24487553676282104745421505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16325035784188069830281003 24487553676282104745421505)
            ·
              refine ⟨18365665257211578559066129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24487553676282104745421505 18365665257211578559066129)
              ·
                refine ⟨13774248942908683919299597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18365665257211578559066129 13774248942908683919299597)
                ·
                  refine ⟨5165343353590756469737349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13774248942908683919299597 5165343353590756469737349)
                  ·
                    refine ⟨968501878798266838075753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5165343353590756469737349 968501878798266838075753)
                    ·
                      rfl

theorem cell23_5658452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_5658452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658452 prefixEnd_5658452 := by exact prefixLift 5658452
  have htrace : WordTrace (prefixWord ++ tailWord_5658452) baseStart_5658452 baseEnd_5658452 := by
    simpa [prefixWord, tailWord_5658452, baseEnd_5658452] using wordTrace_append hprefix tailTrace_5658452
  have hstable : (prefixWord ++ tailWord_5658452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658452).length < 2 ^ (prefixWord ++ tailWord_5658452).sum := by decide
  have hdescent : baseEnd_5658452 < baseStart_5658452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658486 : List Nat := [5, 1, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_5658486 : Nat := 118140960795 + 5658486 * 2 ^ 59
def prefixEnd_5658486 : Nat := 4983230072969 + 3 ^ 40 * 5658486 * 2
def baseEnd_5658486 : Nat := 968507698245684460400701

theorem tailTrace_5658486 : CollatzResearch.WordTrace tailWord_5658486 prefixEnd_5658486 968507698245684460400701 := by
  unfold tailWord_5658486
  simp only [CollatzResearch.WordTrace]
  refine ⟨12898871211142443082217207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137587959585519392876983541 12898871211142443082217207)
  ·
    refine ⟨19348306816713664623325811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12898871211142443082217207 19348306816713664623325811)
    ·
      refine ⟨29022460225070496934988717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19348306816713664623325811 29022460225070496934988717)
      ·
        refine ⟨10883422584401436350620769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29022460225070496934988717 10883422584401436350620769)
        ·
          refine ⟨8162566938301077262965577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10883422584401436350620769 8162566938301077262965577)
          ·
            refine ⟨6121925203725807947224183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8162566938301077262965577 6121925203725807947224183)
            ·
              refine ⟨9182887805588711920836275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6121925203725807947224183 9182887805588711920836275)
              ·
                refine ⟨13774331708383067881254413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9182887805588711920836275 13774331708383067881254413)
                ·
                  refine ⟨5165374390643650455470405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13774331708383067881254413 5165374390643650455470405)
                  ·
                    refine ⟨968507698245684460400701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5165374390643650455470405 968507698245684460400701)
                    ·
                      rfl

theorem cell23_5658486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_5658486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658486 prefixEnd_5658486 := by exact prefixLift 5658486
  have htrace : WordTrace (prefixWord ++ tailWord_5658486) baseStart_5658486 baseEnd_5658486 := by
    simpa [prefixWord, tailWord_5658486, baseEnd_5658486] using wordTrace_append hprefix tailTrace_5658486
  have hstable : (prefixWord ++ tailWord_5658486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658486).length < 2 ^ (prefixWord ++ tailWord_5658486).sum := by decide
  have hdescent : baseEnd_5658486 < baseStart_5658486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658519 : List Nat := [1, 1, 3, 3, 1, 4, 2, 1, 2, 3, 2]
def baseStart_5658519 : Nat := 118140960795 + 5658519 * 2 ^ 59
def prefixEnd_5658519 : Nat := 4983230072969 + 3 ^ 40 * 5658519 * 2
def baseEnd_5658519 : Nat := 2905540039598651752089451

theorem tailTrace_5658519 : CollatzResearch.WordTrace tailWord_5658519 prefixEnd_5658519 2905540039598651752089451 := by
  unfold tailWord_5658519
  simp only [CollatzResearch.WordTrace]
  refine ⟨206383142987159535951426611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137588761991439690634284407 206383142987159535951426611)
  ·
    refine ⟨309574714480739303927139917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206383142987159535951426611 309574714480739303927139917)
    ·
      refine ⟨116090517930277238972677469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309574714480739303927139917 116090517930277238972677469)
      ·
        refine ⟨43533944223853964614754051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116090517930277238972677469 43533944223853964614754051)
        ·
          refine ⟨65300916335780946922131077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43533944223853964614754051 65300916335780946922131077)
          ·
            refine ⟨12243921812958927547899577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65300916335780946922131077 12243921812958927547899577)
            ·
              refine ⟨9182941359719195660924683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12243921812958927547899577 9182941359719195660924683)
              ·
                refine ⟨13774412039578793491387025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9182941359719195660924683 13774412039578793491387025)
                ·
                  refine ⟨10330809029684095118540269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13774412039578793491387025 10330809029684095118540269)
                  ·
                    refine ⟨3874053386131535669452601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10330809029684095118540269 3874053386131535669452601)
                    ·
                      refine ⟨2905540039598651752089451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3874053386131535669452601 2905540039598651752089451)
                      ·
                        rfl

theorem cell23_5658519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_5658519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658519 prefixEnd_5658519 := by exact prefixLift 5658519
  have htrace : WordTrace (prefixWord ++ tailWord_5658519) baseStart_5658519 baseEnd_5658519 := by
    simpa [prefixWord, tailWord_5658519, baseEnd_5658519] using wordTrace_append hprefix tailTrace_5658519
  have hstable : (prefixWord ++ tailWord_5658519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658519).length < 2 ^ (prefixWord ++ tailWord_5658519).sum := by decide
  have hdescent : baseEnd_5658519 < baseStart_5658519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658525 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 3, 6]
def baseStart_5658525 : Nat := 118140960795 + 5658525 * 2 ^ 59
def prefixEnd_5658525 : Nat := 4983230072969 + 3 ^ 40 * 5658525 * 2
def baseEnd_5658525 : Nat := 968514373494192909538141

theorem tailTrace_5658525 : CollatzResearch.WordTrace tailWord_5658525 prefixEnd_5658525 968514373494192909538141 := by
  unfold tailWord_5658525
  simp only [CollatzResearch.WordTrace]
  refine ⟨206383361825137798976145029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137588907883425199317430019 206383361825137798976145029)
  ·
    refine ⟨38696880342213337308027193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206383361825137798976145029 38696880342213337308027193)
    ·
      refine ⟨29022660256660002981020395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38696880342213337308027193 29022660256660002981020395)
      ·
        refine ⟨43533990384990004471530593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29022660256660002981020395 43533990384990004471530593)
        ·
          refine ⟨32650492788742503353647945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43533990384990004471530593 32650492788742503353647945)
          ·
            refine ⟨24487869591556877515235959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32650492788742503353647945 24487869591556877515235959)
            ·
              refine ⟨36731804387335316272853939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24487869591556877515235959 36731804387335316272853939)
              ·
                refine ⟨55097706581002974409280909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36731804387335316272853939 55097706581002974409280909)
                ·
                  refine ⟨20661639967876115403480341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55097706581002974409280909 20661639967876115403480341)
                  ·
                    refine ⟨968514373494192909538141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20661639967876115403480341 968514373494192909538141)
                    ·
                      rfl

theorem cell23_5658525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_5658525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658525 prefixEnd_5658525 := by exact prefixLift 5658525
  have htrace : WordTrace (prefixWord ++ tailWord_5658525) baseStart_5658525 baseEnd_5658525 := by
    simpa [prefixWord, tailWord_5658525, baseEnd_5658525] using wordTrace_append hprefix tailTrace_5658525
  have hstable : (prefixWord ++ tailWord_5658525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658525).length < 2 ^ (prefixWord ++ tailWord_5658525).sum := by decide
  have hdescent : baseEnd_5658525 < baseStart_5658525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658538 : List Nat := [3, 1, 19]
def baseStart_5658538 : Nat := 118140960795 + 5658538 * 2 ^ 59
def prefixEnd_5658538 : Nat := 4983230072969 + 3 ^ 40 * 5658538 * 2
def baseEnd_5658538 : Nat := 442851668302253799383

theorem tailTrace_5658538 : CollatzResearch.WordTrace tailWord_5658538 prefixEnd_5658538 442851668302253799383 := by
  unfold tailWord_5658538
  simp only [CollatzResearch.WordTrace]
  refine ⟨51595958993522675549092067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137589223982727134797578845 51595958993522675549092067)
  ·
    refine ⟨77393938490284013323638101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51595958993522675549092067 77393938490284013323638101)
    ·
      refine ⟨442851668302253799383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 19 77393938490284013323638101 442851668302253799383)
      ·
        rfl

theorem cell23_5658538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 19].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 19].length) (baseStart_5658538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658538 prefixEnd_5658538 := by exact prefixLift 5658538
  have htrace : WordTrace (prefixWord ++ tailWord_5658538) baseStart_5658538 baseEnd_5658538 := by
    simpa [prefixWord, tailWord_5658538, baseEnd_5658538] using wordTrace_append hprefix tailTrace_5658538
  have hstable : (prefixWord ++ tailWord_5658538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658538).length < 2 ^ (prefixWord ++ tailWord_5658538).sum := by decide
  have hdescent : baseEnd_5658538 < baseStart_5658538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658572 : List Nat := [2, 2, 1, 4, 1, 3, 3, 7]
def baseStart_5658572 : Nat := 118140960795 + 5658572 * 2 ^ 59
def prefixEnd_5658572 : Nat := 4983230072969 + 3 ^ 40 * 5658572 * 2
def baseEnd_5658572 : Nat := 107613602002716297952841

theorem tailTrace_5658572 : CollatzResearch.WordTrace tailWord_5658572 prefixEnd_5658572 107613602002716297952841 := by
  unfold tailWord_5658572
  simp only [CollatzResearch.WordTrace]
  refine ⟨103192538027983763001552985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137590050703978350668737313 103192538027983763001552985)
  ·
    refine ⟨77394403520987822251164739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103192538027983763001552985 77394403520987822251164739)
    ·
      refine ⟨116091605281481733376747109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77394403520987822251164739 116091605281481733376747109)
      ·
        refine ⟨21767175990277825008140083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116091605281481733376747109 21767175990277825008140083)
        ·
          refine ⟨32650763985416737512210125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21767175990277825008140083 32650763985416737512210125)
          ·
            refine ⟨12244036494531276567078797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32650763985416737512210125 12244036494531276567078797)
            ·
              refine ⟨4591513685449228712654549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12244036494531276567078797 4591513685449228712654549)
              ·
                refine ⟨107613602002716297952841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4591513685449228712654549 107613602002716297952841)
                ·
                  rfl

theorem cell23_5658572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 7].length) (baseStart_5658572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658572 prefixEnd_5658572 := by exact prefixLift 5658572
  have htrace : WordTrace (prefixWord ++ tailWord_5658572) baseStart_5658572 baseEnd_5658572 := by
    simpa [prefixWord, tailWord_5658572, baseEnd_5658572] using wordTrace_append hprefix tailTrace_5658572
  have hstable : (prefixWord ++ tailWord_5658572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658572).length < 2 ^ (prefixWord ++ tailWord_5658572).sum := by decide
  have hdescent : baseEnd_5658572 < baseStart_5658572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658655 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 7]
def baseStart_5658655 : Nat := 118140960795 + 5658655 * 2 ^ 59
def prefixEnd_5658655 : Nat := 4983230072969 + 3 ^ 40 * 5658655 * 2
def baseEnd_5658655 : Nat := 2905609872967663219988825

theorem tailTrace_5658655 : CollatzResearch.WordTrace tailWord_5658655 prefixEnd_5658655 2905609872967663219988825 := by
  unfold tailWord_5658655
  simp only [CollatzResearch.WordTrace]
  refine ⟨206388103314666831178377419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137592068876444554118918279 206388103314666831178377419)
  ·
    refine ⟨309582154972000246767566129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206388103314666831178377419 309582154972000246767566129)
    ·
      refine ⟨232186616229000185075674597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309582154972000246767566129 232186616229000185075674597)
      ·
        refine ⟨43534990542937534701688987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232186616229000185075674597 43534990542937534701688987)
        ·
          refine ⟨65302485814406302052533481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43534990542937534701688987 65302485814406302052533481)
          ·
            refine ⟨48976864360804726539400111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65302485814406302052533481 48976864360804726539400111)
            ·
              refine ⟨73465296541207089809100167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48976864360804726539400111 73465296541207089809100167)
              ·
                refine ⟨110197944811810634713650251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73465296541207089809100167 110197944811810634713650251)
                ·
                  refine ⟨165296917217715952070475377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110197944811810634713650251 165296917217715952070475377)
                  ·
                    refine ⟨123972687913286964052856533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 165296917217715952070475377 123972687913286964052856533)
                    ·
                      refine ⟨2905609872967663219988825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123972687913286964052856533 2905609872967663219988825)
                      ·
                        rfl

theorem cell23_5658655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_5658655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658655 prefixEnd_5658655 := by exact prefixLift 5658655
  have htrace : WordTrace (prefixWord ++ tailWord_5658655) baseStart_5658655 baseEnd_5658655 := by
    simpa [prefixWord, tailWord_5658655, baseEnd_5658655] using wordTrace_append hprefix tailTrace_5658655
  have hstable : (prefixWord ++ tailWord_5658655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658655).length < 2 ^ (prefixWord ++ tailWord_5658655).sum := by decide
  have hdescent : baseEnd_5658655 < baseStart_5658655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658673 : List Nat := [1, 2, 2, 3, 1, 3, 4, 1, 2, 2, 2]
def baseStart_5658673 : Nat := 118140960795 + 5658673 * 2 ^ 59
def prefixEnd_5658673 : Nat := 4983230072969 + 3 ^ 40 * 5658673 * 2
def baseEnd_5658673 : Nat := 2905619115619444149563743

theorem tailTrace_5658673 : CollatzResearch.WordTrace tailWord_5658673 prefixEnd_5658673 2905619115619444149563743 := by
  unfold tailWord_5658673
  simp only [CollatzResearch.WordTrace]
  refine ⟨206388759828601620252532673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137592506552401080168355115 206388759828601620252532673)
  ·
    refine ⟨154791569871451215189399505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206388759828601620252532673 154791569871451215189399505)
    ·
      refine ⟨116093677403588411392049629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154791569871451215189399505 116093677403588411392049629)
      ·
        refine ⟨43535129026345654272018611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116093677403588411392049629 43535129026345654272018611)
        ·
          refine ⟨65302693539518481408027917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43535129026345654272018611 65302693539518481408027917)
          ·
            refine ⟨24488510077319430528010469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65302693539518481408027917 24488510077319430528010469)
            ·
              refine ⟨4591595639497393224001963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24488510077319430528010469 4591595639497393224001963)
              ·
                refine ⟨6887393459246089836002945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4591595639497393224001963 6887393459246089836002945)
                ·
                  refine ⟨5165545094434567377002209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6887393459246089836002945 5165545094434567377002209)
                  ·
                    refine ⟨3874158820825925532751657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5165545094434567377002209 3874158820825925532751657)
                    ·
                      refine ⟨2905619115619444149563743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3874158820825925532751657 2905619115619444149563743)
                      ·
                        rfl

theorem cell23_5658673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_5658673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658673 prefixEnd_5658673 := by exact prefixLift 5658673
  have htrace : WordTrace (prefixWord ++ tailWord_5658673) baseStart_5658673 baseEnd_5658673 := by
    simpa [prefixWord, tailWord_5658673, baseEnd_5658673] using wordTrace_append hprefix tailTrace_5658673
  have hstable : (prefixWord ++ tailWord_5658673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658673).length < 2 ^ (prefixWord ++ tailWord_5658673).sum := by decide
  have hdescent : baseEnd_5658673 < baseStart_5658673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658675 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 3, 7]
def baseStart_5658675 : Nat := 118140960795 + 5658675 * 2 ^ 59
def prefixEnd_5658675 : Nat := 4983230072969 + 3 ^ 40 * 5658675 * 2
def baseEnd_5658675 : Nat := 968540047526917713912911

theorem tailTrace_5658675 : CollatzResearch.WordTrace tailWord_5658675 prefixEnd_5658675 968540047526917713912911 := by
  unfold tailWord_5658675
  simp only [CollatzResearch.WordTrace]
  refine ⟨206388832774594374594105479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137592555183062916396070319 206388832774594374594105479)
  ·
    refine ⟨309583249161891561891158219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206388832774594374594105479 309583249161891561891158219)
    ·
      refine ⟨464374873742837342836737329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309583249161891561891158219 464374873742837342836737329)
      ·
        refine ⟨348281155307128007127552997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 464374873742837342836737329 348281155307128007127552997)
        ·
          refine ⟨65302716620086501336416187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 348281155307128007127552997 65302716620086501336416187)
          ·
            refine ⟨97954074930129752004624281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65302716620086501336416187 97954074930129752004624281)
            ·
              refine ⟨73465556197597314003468211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97954074930129752004624281 73465556197597314003468211)
              ·
                refine ⟨110198334296395971005202317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73465556197597314003468211 110198334296395971005202317)
                ·
                  refine ⟨41324375361148489126950869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110198334296395971005202317 41324375361148489126950869)
                  ·
                    refine ⟨968540047526917713912911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41324375361148489126950869 968540047526917713912911)
                    ·
                      rfl

theorem cell23_5658675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 7].length) (baseStart_5658675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658675 prefixEnd_5658675 := by exact prefixLift 5658675
  have htrace : WordTrace (prefixWord ++ tailWord_5658675) baseStart_5658675 baseEnd_5658675 := by
    simpa [prefixWord, tailWord_5658675, baseEnd_5658675] using wordTrace_append hprefix tailTrace_5658675
  have hstable : (prefixWord ++ tailWord_5658675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658675).length < 2 ^ (prefixWord ++ tailWord_5658675).sum := by decide
  have hdescent : baseEnd_5658675 < baseStart_5658675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658702 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_5658702 : Nat := 118140960795 + 5658702 * 2 ^ 59
def prefixEnd_5658702 : Nat := 4983230072969 + 3 ^ 40 * 5658702 * 2
def baseEnd_5658702 : Nat := 2905634006558424536101109

theorem tailTrace_5658702 : CollatzResearch.WordTrace tailWord_5658702 prefixEnd_5658702 2905634006558424536101109 := by
  unfold tailWord_5658702
  simp only [CollatzResearch.WordTrace]
  refine ⟨25798727193187069775667295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137593211696997705470225573 25798727193187069775667295)
  ·
    refine ⟨38698090789780604663500943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25798727193187069775667295 38698090789780604663500943)
    ·
      refine ⟨58047136184670906995251415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38698090789780604663500943 58047136184670906995251415)
      ·
        refine ⟨87070704277006360492877123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58047136184670906995251415 87070704277006360492877123)
        ·
          refine ⟨130606056415509540739315685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87070704277006360492877123 130606056415509540739315685)
          ·
            refine ⟨24488635577908038888621691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130606056415509540739315685 24488635577908038888621691)
            ·
              refine ⟨36732953366862058332932537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24488635577908038888621691 36732953366862058332932537)
              ·
                refine ⟨27549715025146543749699403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36732953366862058332932537 27549715025146543749699403)
                ·
                  refine ⟨41324572537719815624549105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27549715025146543749699403 41324572537719815624549105)
                  ·
                    refine ⟨30993429403289861718411829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41324572537719815624549105 30993429403289861718411829)
                    ·
                      refine ⟨2905634006558424536101109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30993429403289861718411829 2905634006558424536101109)
                      ·
                        rfl

theorem cell23_5658702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_5658702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658702 prefixEnd_5658702 := by exact prefixLift 5658702
  have htrace : WordTrace (prefixWord ++ tailWord_5658702) baseStart_5658702 baseEnd_5658702 := by
    simpa [prefixWord, tailWord_5658702, baseEnd_5658702] using wordTrace_append hprefix tailTrace_5658702
  have hstable : (prefixWord ++ tailWord_5658702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658702).length < 2 ^ (prefixWord ++ tailWord_5658702).sum := by decide
  have hdescent : baseEnd_5658702 < baseStart_5658702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658729 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 2, 4, 2]
def baseStart_5658729 : Nat := 118140960795 + 5658729 * 2 ^ 59
def prefixEnd_5658729 : Nat := 4983230072969 + 3 ^ 40 * 5658729 * 2
def baseEnd_5658729 : Nat := 2905647870536095930463485

theorem tailTrace_5658729 : CollatzResearch.WordTrace tailWord_5658729 prefixEnd_5658729 2905647870536095930463485 := by
  unfold tailWord_5658729
  simp only [CollatzResearch.WordTrace]
  refine ⟨206390802316398741816571241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137593868210932494544380827 206390802316398741816571241)
  ·
    refine ⟨154793101737299056362428431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206390802316398741816571241 154793101737299056362428431)
    ·
      refine ⟨232189652605948584543642647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154793101737299056362428431 232189652605948584543642647)
      ·
        refine ⟨348284478908922876815463971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232189652605948584543642647 348284478908922876815463971)
        ·
          refine ⟨522426718363384315223195957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348284478908922876815463971 522426718363384315223195957)
          ·
            refine ⟨48977504846567279552174621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 522426718363384315223195957 48977504846567279552174621)
            ·
              refine ⟨18366564317462729832065483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48977504846567279552174621 18366564317462729832065483)
              ·
                refine ⟨27549846476194094748098225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18366564317462729832065483 27549846476194094748098225)
                ·
                  refine ⟨20662384857145571061073669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27549846476194094748098225 20662384857145571061073669)
                  ·
                    refine ⟨3874197160714794573951313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20662384857145571061073669 3874197160714794573951313)
                    ·
                      refine ⟨2905647870536095930463485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3874197160714794573951313 2905647870536095930463485)
                      ·
                        rfl

theorem cell23_5658729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 4, 2].length) (baseStart_5658729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658729 prefixEnd_5658729 := by exact prefixLift 5658729
  have htrace : WordTrace (prefixWord ++ tailWord_5658729) baseStart_5658729 baseEnd_5658729 := by
    simpa [prefixWord, tailWord_5658729, baseEnd_5658729] using wordTrace_append hprefix tailTrace_5658729
  have hstable : (prefixWord ++ tailWord_5658729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658729).length < 2 ^ (prefixWord ++ tailWord_5658729).sum := by decide
  have hdescent : baseEnd_5658729 < baseStart_5658729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658749 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 1, 4, 3]
def baseStart_5658749 : Nat := 118140960795 + 5658749 * 2 ^ 59
def prefixEnd_5658749 : Nat := 4983230072969 + 3 ^ 40 * 5658749 * 2
def baseEnd_5658749 : Nat := 2905658140149185852213393

theorem tailTrace_5658749 : CollatzResearch.WordTrace tailWord_5658749 prefixEnd_5658749 2905658140149185852213393 := by
  unfold tailWord_5658749
  simp only [CollatzResearch.WordTrace]
  refine ⟨206391531776326285232299301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137594354517550856821532867 206391531776326285232299301)
  ·
    refine ⟨38698412208061178481056119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206391531776326285232299301 38698412208061178481056119)
    ·
      refine ⟨58047618312091767721584179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38698412208061178481056119 58047618312091767721584179)
      ·
        refine ⟨87071427468137651582376269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58047618312091767721584179 87071427468137651582376269)
        ·
          refine ⟨32651785300551619343391101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87071427468137651582376269 32651785300551619343391101)
          ·
            refine ⟨12244419487706857253771663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32651785300551619343391101 12244419487706857253771663)
            ·
              refine ⟨18366629231560285880657495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12244419487706857253771663 18366629231560285880657495)
              ·
                refine ⟨27549943847340428820986243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18366629231560285880657495 27549943847340428820986243)
                ·
                  refine ⟨41324915771010643231479365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27549943847340428820986243 41324915771010643231479365)
                  ·
                    refine ⟨7748421707064495605902381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41324915771010643231479365 7748421707064495605902381)
                    ·
                      refine ⟨2905658140149185852213393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7748421707064495605902381 2905658140149185852213393)
                      ·
                        rfl

theorem cell23_5658749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_5658749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658749 prefixEnd_5658749 := by exact prefixLift 5658749
  have htrace : WordTrace (prefixWord ++ tailWord_5658749) baseStart_5658749 baseEnd_5658749 := by
    simpa [prefixWord, tailWord_5658749, baseEnd_5658749] using wordTrace_append hprefix tailTrace_5658749
  have hstable : (prefixWord ++ tailWord_5658749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658749).length < 2 ^ (prefixWord ++ tailWord_5658749).sum := by decide
  have hdescent : baseEnd_5658749 < baseStart_5658749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658789 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 3, 5, 2]
def baseStart_5658789 : Nat := 118140960795 + 5658789 * 2 ^ 59
def prefixEnd_5658789 : Nat := 4983230072969 + 3 ^ 40 * 5658789 * 2
def baseEnd_5658789 : Nat := 2905678679375365695713209

theorem tailTrace_5658789 : CollatzResearch.WordTrace tailWord_5658789 prefixEnd_5658789 2905678679375365695713209 := by
  unfold tailWord_5658789
  simp only [CollatzResearch.WordTrace]
  refine ⟨206392990696181372063755421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137595327130787581375836947 206392990696181372063755421)
  ·
    refine ⟨77397371511068014523908283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206392990696181372063755421 77397371511068014523908283)
    ·
      refine ⟨116096057266602021785862425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77397371511068014523908283 116096057266602021785862425)
      ·
        refine ⟨87072042949951516339396819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116096057266602021785862425 87072042949951516339396819)
        ·
          refine ⟨130608064424927274509095229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87072042949951516339396819 130608064424927274509095229)
          ·
            refine ⟨48978024159347727940910711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130608064424927274509095229 48978024159347727940910711)
            ·
              refine ⟨73467036239021591911366067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48978024159347727940910711 73467036239021591911366067)
              ·
                refine ⟨110200554358532387867049101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73467036239021591911366067 110200554358532387867049101)
                ·
                  refine ⟨41325207884449645450143413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110200554358532387867049101 41325207884449645450143413)
                  ·
                    refine ⟨3874238239167154260950945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41325207884449645450143413 3874238239167154260950945)
                    ·
                      refine ⟨2905678679375365695713209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3874238239167154260950945 2905678679375365695713209)
                      ·
                        rfl

theorem cell23_5658789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_5658789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658789 prefixEnd_5658789 := by exact prefixLift 5658789
  have htrace : WordTrace (prefixWord ++ tailWord_5658789) baseStart_5658789 baseEnd_5658789 := by
    simpa [prefixWord, tailWord_5658789, baseEnd_5658789] using wordTrace_append hprefix tailTrace_5658789
  have hstable : (prefixWord ++ tailWord_5658789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658789).length < 2 ^ (prefixWord ++ tailWord_5658789).sum := by decide
  have hdescent : baseEnd_5658789 < baseStart_5658789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658839 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 3]
def baseStart_5658839 : Nat := 118140960795 + 5658839 * 2 ^ 59
def prefixEnd_5658839 : Nat := 4983230072969 + 3 ^ 40 * 5658839 * 2
def baseEnd_5658839 : Nat := 2905704353408090500087979

theorem tailTrace_5658839 : CollatzResearch.WordTrace tailWord_5658839 prefixEnd_5658839 2905704353408090500087979 := by
  unfold tailWord_5658839
  simp only [CollatzResearch.WordTrace]
  refine ⟨206394814346000230603075571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137596542897333487068717047 206394814346000230603075571)
  ·
    refine ⟨309592221519000345904613357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206394814346000230603075571 309592221519000345904613357)
    ·
      refine ⟨116097083069625129714230009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309592221519000345904613357 116097083069625129714230009)
      ·
        refine ⟨87072812302218847285672507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116097083069625129714230009 87072812302218847285672507)
        ·
          refine ⟨130609218453328270928508761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87072812302218847285672507 130609218453328270928508761)
          ·
            refine ⟨97956913839996203196381571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130609218453328270928508761 97956913839996203196381571)
            ·
              refine ⟨146935370759994304794572357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97956913839996203196381571 146935370759994304794572357)
              ·
                refine ⟨27550382017498932148982317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146935370759994304794572357 27550382017498932148982317)
                ·
                  refine ⟨10331393256562099555868369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27550382017498932148982317 10331393256562099555868369)
                  ·
                    refine ⟨7748544942421574666901277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10331393256562099555868369 7748544942421574666901277)
                    ·
                      refine ⟨2905704353408090500087979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7748544942421574666901277 2905704353408090500087979)
                      ·
                        rfl

theorem cell23_5658839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_5658839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658839 prefixEnd_5658839 := by exact prefixLift 5658839
  have htrace : WordTrace (prefixWord ++ tailWord_5658839) baseStart_5658839 baseEnd_5658839 := by
    simpa [prefixWord, tailWord_5658839, baseEnd_5658839] using wordTrace_append hprefix tailTrace_5658839
  have hstable : (prefixWord ++ tailWord_5658839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658839).length < 2 ^ (prefixWord ++ tailWord_5658839).sum := by decide
  have hdescent : baseEnd_5658839 < baseStart_5658839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658842 : List Nat := [3, 1, 1, 2, 2, 1, 3, 10]
def baseStart_5658842 : Nat := 118140960795 + 5658842 * 2 ^ 59
def prefixEnd_5658842 : Nat := 4983230072969 + 3 ^ 40 * 5658842 * 2
def baseEnd_5658842 : Nat := 107618736809261258827795

theorem tailTrace_5658842 : CollatzResearch.WordTrace tailWord_5658842 prefixEnd_5658842 107618736809261258827795 := by
  unfold tailWord_5658842
  simp only [CollatzResearch.WordTrace]
  refine ⟨51598730941247340528858695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137596615843326241410289853 51598730941247340528858695)
  ·
    refine ⟨77398096411871010793288043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51598730941247340528858695 77398096411871010793288043)
    ·
      refine ⟨116097144617806516189932065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77398096411871010793288043 116097144617806516189932065)
      ·
        refine ⟨87072858463354887142449049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116097144617806516189932065 87072858463354887142449049)
        ·
          refine ⟨65304643847516165356836787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87072858463354887142449049 65304643847516165356836787)
          ·
            refine ⟨97956965771274248035255181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65304643847516165356836787 97956965771274248035255181)
            ·
              refine ⟨36733862164227843013220693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97956965771274248035255181 36733862164227843013220693)
              ·
                refine ⟨107618736809261258827795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36733862164227843013220693 107618736809261258827795)
                ·
                  rfl

theorem cell23_5658842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 10].length) (baseStart_5658842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658842 prefixEnd_5658842 := by exact prefixLift 5658842
  have htrace : WordTrace (prefixWord ++ tailWord_5658842) baseStart_5658842 baseEnd_5658842 := by
    simpa [prefixWord, tailWord_5658842, baseEnd_5658842] using wordTrace_append hprefix tailTrace_5658842
  have hstable : (prefixWord ++ tailWord_5658842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658842).length < 2 ^ (prefixWord ++ tailWord_5658842).sum := by decide
  have hdescent : baseEnd_5658842 < baseStart_5658842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658849 : List Nat := [1, 2, 3, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_5658849 : Nat := 118140960795 + 5658849 * 2 ^ 59
def prefixEnd_5658849 : Nat := 4983230072969 + 3 ^ 40 * 5658849 * 2
def baseEnd_5658849 : Nat := 2905709488214635460962933

theorem tailTrace_5658849 : CollatzResearch.WordTrace tailWord_5658849 prefixEnd_5658849 2905709488214635460962933 := by
  unfold tailWord_5658849
  simp only [CollatzResearch.WordTrace]
  refine ⟨206395179075964002310939601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137596786050642668207293067 206395179075964002310939601)
  ·
    refine ⟨154796384306973001733204701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206395179075964002310939601 154796384306973001733204701)
    ·
      refine ⟨58048644115114875649951763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154796384306973001733204701 58048644115114875649951763)
      ·
        refine ⟨87072966172672313474927645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58048644115114875649951763 87072966172672313474927645)
        ·
          refine ⟨32652362314752117553097867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87072966172672313474927645 32652362314752117553097867)
          ·
            refine ⟨48978543472128176329646801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32652362314752117553097867 48978543472128176329646801)
            ·
              refine ⟨36733907604096132247235101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48978543472128176329646801 36733907604096132247235101)
              ·
                refine ⟨13775215351536049592713163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36733907604096132247235101 13775215351536049592713163)
                ·
                  refine ⟨20662823027304074389069745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13775215351536049592713163 20662823027304074389069745)
                  ·
                    refine ⟨15497117270478055791802309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20662823027304074389069745 15497117270478055791802309)
                    ·
                      refine ⟨2905709488214635460962933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15497117270478055791802309 2905709488214635460962933)
                      ·
                        rfl

theorem cell23_5658849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_5658849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658849 prefixEnd_5658849 := by exact prefixLift 5658849
  have htrace : WordTrace (prefixWord ++ tailWord_5658849) baseStart_5658849 baseEnd_5658849 := by
    simpa [prefixWord, tailWord_5658849, baseEnd_5658849] using wordTrace_append hprefix tailTrace_5658849
  have hstable : (prefixWord ++ tailWord_5658849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658849).length < 2 ^ (prefixWord ++ tailWord_5658849).sum := by decide
  have hdescent : baseEnd_5658849 < baseStart_5658849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658850 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_5658850 : Nat := 118140960795 + 5658850 * 2 ^ 59
def prefixEnd_5658850 : Nat := 4983230072969 + 3 ^ 40 * 5658850 * 2
def baseEnd_5658850 : Nat := 968570000565096652350143

theorem tailTrace_5658850 : CollatzResearch.WordTrace tailWord_5658850 prefixEnd_5658850 968570000565096652350143 := by
  unfold tailWord_5658850
  simp only [CollatzResearch.WordTrace]
  refine ⟨51598803887240094870431501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137596810365973586321150669 51598803887240094870431501)
  ·
    refine ⟨19349551457715035576411813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51598803887240094870431501 19349551457715035576411813)
    ·
      refine ⟨3628040898321569170577215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19349551457715035576411813 3628040898321569170577215)
      ·
        refine ⟨5442061347482353755865823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3628040898321569170577215 5442061347482353755865823)
        ·
          refine ⟨8163092021223530633798735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5442061347482353755865823 8163092021223530633798735)
          ·
            refine ⟨12244638031835295950698103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8163092021223530633798735 12244638031835295950698103)
            ·
              refine ⟨18366957047752943926047155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12244638031835295950698103 18366957047752943926047155)
              ·
                refine ⟨27550435571629415889070733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18366957047752943926047155 27550435571629415889070733)
                ·
                  refine ⟨10331413339361030958401525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27550435571629415889070733 10331413339361030958401525)
                  ·
                    refine ⟨968570000565096652350143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10331413339361030958401525 968570000565096652350143)
                    ·
                      rfl

theorem cell23_5658850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_5658850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658850 prefixEnd_5658850 := by exact prefixLift 5658850
  have htrace : WordTrace (prefixWord ++ tailWord_5658850) baseStart_5658850 baseEnd_5658850 := by
    simpa [prefixWord, tailWord_5658850, baseEnd_5658850] using wordTrace_append hprefix tailTrace_5658850
  have hstable : (prefixWord ++ tailWord_5658850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658850).length < 2 ^ (prefixWord ++ tailWord_5658850).sum := by decide
  have hdescent : baseEnd_5658850 < baseStart_5658850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658853 : List Nat := [1, 3, 1, 4, 2, 3, 1, 2, 1, 1, 4]
def baseStart_5658853 : Nat := 118140960795 + 5658853 * 2 ^ 59
def prefixEnd_5658853 : Nat := 4983230072969 + 3 ^ 40 * 5658853 * 2
def baseEnd_5658853 : Nat := 2905711542137253445312915

theorem tailTrace_5658853 : CollatzResearch.WordTrace tailWord_5658853 prefixEnd_5658853 2905711542137253445312915 := by
  unfold tailWord_5658853
  simp only [CollatzResearch.WordTrace]
  refine ⟨206395324967949510994085213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137596883311966340662723475 206395324967949510994085213)
  ·
    refine ⟨77398246862981066622781955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206395324967949510994085213 77398246862981066622781955)
    ·
      refine ⟨116097370294471599934172933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77398246862981066622781955 116097370294471599934172933)
      ·
        refine ⟨21768256930213424987657425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116097370294471599934172933 21768256930213424987657425)
        ·
          refine ⟨16326192697660068740743069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21768256930213424987657425 16326192697660068740743069)
          ·
            refine ⟨6122322261622525777778651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16326192697660068740743069 6122322261622525777778651)
            ·
              refine ⟨9183483392433788666667977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6122322261622525777778651 9183483392433788666667977)
              ·
                refine ⟨6887612544325341500000983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9183483392433788666667977 6887612544325341500000983)
                ·
                  refine ⟨10331418816488012250001475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6887612544325341500000983 10331418816488012250001475)
                  ·
                    refine ⟨15497128224732018375002213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10331418816488012250001475 15497128224732018375002213)
                    ·
                      refine ⟨2905711542137253445312915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15497128224732018375002213 2905711542137253445312915)
                      ·
                        rfl

theorem cell23_5658853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_5658853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658853 prefixEnd_5658853 := by exact prefixLift 5658853
  have htrace : WordTrace (prefixWord ++ tailWord_5658853) baseStart_5658853 baseEnd_5658853 := by
    simpa [prefixWord, tailWord_5658853, baseEnd_5658853] using wordTrace_append hprefix tailTrace_5658853
  have hstable : (prefixWord ++ tailWord_5658853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658853).length < 2 ^ (prefixWord ++ tailWord_5658853).sum := by decide
  have hdescent : baseEnd_5658853 < baseStart_5658853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658856 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_5658856 : Nat := 118140960795 + 5658856 * 2 ^ 59
def prefixEnd_5658856 : Nat := 4983230072969 + 3 ^ 40 * 5658856 * 2
def baseEnd_5658856 : Nat := 2905713082579216933575401

theorem tailTrace_5658856 : CollatzResearch.WordTrace tailWord_5658856 prefixEnd_5658856 2905713082579216933575401 := by
  unfold tailWord_5658856
  simp only [CollatzResearch.WordTrace]
  refine ⟨103197717193469321253222211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137596956257959095004296281 103197717193469321253222211)
  ·
    refine ⟨154796575790203981879833317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103197717193469321253222211 154796575790203981879833317)
    ·
      refine ⟨29024357960663246602468747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154796575790203981879833317 29024357960663246602468747)
      ·
        refine ⟨43536536940994869903703121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29024357960663246602468747 43536536940994869903703121)
        ·
          refine ⟨32652402705746152427777341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43536536940994869903703121 32652402705746152427777341)
          ·
            refine ⟨12244651014654807160416503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32652402705746152427777341 12244651014654807160416503)
            ·
              refine ⟨18366976521982210740624755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12244651014654807160416503 18366976521982210740624755)
              ·
                refine ⟨27550464782973316110937133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18366976521982210740624755 27550464782973316110937133)
                ·
                  refine ⟨10331424293614993541601425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27550464782973316110937133 10331424293614993541601425)
                  ·
                    refine ⟨7748568220211245156201069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10331424293614993541601425 7748568220211245156201069)
                    ·
                      refine ⟨2905713082579216933575401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7748568220211245156201069 2905713082579216933575401)
                      ·
                        rfl

theorem cell23_5658856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_5658856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658856 prefixEnd_5658856 := by exact prefixLift 5658856
  have htrace : WordTrace (prefixWord ++ tailWord_5658856) baseStart_5658856 baseEnd_5658856 := by
    simpa [prefixWord, tailWord_5658856, baseEnd_5658856] using wordTrace_append hprefix tailTrace_5658856
  have hstable : (prefixWord ++ tailWord_5658856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658856).length < 2 ^ (prefixWord ++ tailWord_5658856).sum := by decide
  have hdescent : baseEnd_5658856 < baseStart_5658856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658866 : List Nat := [3, 2, 1, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_5658866 : Nat := 118140960795 + 5658866 * 2 ^ 59
def prefixEnd_5658866 : Nat := 4983230072969 + 3 ^ 40 * 5658866 * 2
def baseEnd_5658866 : Nat := 2905718217385761894450355

theorem tailTrace_5658866 : CollatzResearch.WordTrace tailWord_5658866 prefixEnd_5658866 2905718217385761894450355 := by
  unfold tailWord_5658866
  simp only [CollatzResearch.WordTrace]
  refine ⟨51598949779225603553577113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137597199411268276142872301 51598949779225603553577113)
  ·
    refine ⟨38699212334419202665182835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51598949779225603553577113 38699212334419202665182835)
    ·
      refine ⟨58048818501628803997774253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38699212334419202665182835 58048818501628803997774253)
      ·
        refine ⟨21768306938110801499165345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58048818501628803997774253 21768306938110801499165345)
        ·
          refine ⟨16326230203583101124374009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21768306938110801499165345 16326230203583101124374009)
          ·
            refine ⟨12244672652687325843280507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16326230203583101124374009 12244672652687325843280507)
            ·
              refine ⟨18367008979030988764920761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12244672652687325843280507 18367008979030988764920761)
              ·
                refine ⟨13775256734273241573690571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18367008979030988764920761 13775256734273241573690571)
                ·
                  refine ⟨20662885101409862360535857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13775256734273241573690571 20662885101409862360535857)
                  ·
                    refine ⟨15497163826057396770401893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20662885101409862360535857 15497163826057396770401893)
                    ·
                      refine ⟨2905718217385761894450355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15497163826057396770401893 2905718217385761894450355)
                      ·
                        rfl

theorem cell23_5658866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_5658866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658866 prefixEnd_5658866 := by exact prefixLift 5658866
  have htrace : WordTrace (prefixWord ++ tailWord_5658866) baseStart_5658866 baseEnd_5658866 := by
    simpa [prefixWord, tailWord_5658866, baseEnd_5658866] using wordTrace_append hprefix tailTrace_5658866
  have hstable : (prefixWord ++ tailWord_5658866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658866).length < 2 ^ (prefixWord ++ tailWord_5658866).sum := by decide
  have hdescent : baseEnd_5658866 < baseStart_5658866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658872 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 4, 7]
def baseStart_5658872 : Nat := 118140960795 + 5658872 * 2 ^ 59
def prefixEnd_5658872 : Nat := 4983230072969 + 3 ^ 40 * 5658872 * 2
def baseEnd_5658872 : Nat := 968573766089896290325109

theorem tailTrace_5658872 : CollatzResearch.WordTrace tailWord_5658872 prefixEnd_5658872 968573766089896290325109 := by
  unfold tailWord_5658872
  simp only [CollatzResearch.WordTrace]
  refine ⟨103198008977440338619513435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137597345303253784826017913 103198008977440338619513435)
  ·
    refine ⟨154797013466160507929270153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103198008977440338619513435 154797013466160507929270153)
    ·
      refine ⟨116097760099620380946952615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154797013466160507929270153 116097760099620380946952615)
      ·
        refine ⟨174146640149430571420428923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116097760099620380946952615 174146640149430571420428923)
        ·
          refine ⟨261219960224145857130643385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174146640149430571420428923 261219960224145857130643385)
          ·
            refine ⟨195914970168109392847982539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261219960224145857130643385 195914970168109392847982539)
            ·
              refine ⟨293872455252164089271973809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195914970168109392847982539 293872455252164089271973809)
              ·
                refine ⟨220404341439123066953980357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293872455252164089271973809 220404341439123066953980357)
                ·
                  refine ⟨41325814019835575053871317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220404341439123066953980357 41325814019835575053871317)
                  ·
                    refine ⟨968573766089896290325109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41325814019835575053871317 968573766089896290325109)
                    ·
                      rfl

theorem cell23_5658872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_5658872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658872 prefixEnd_5658872 := by exact prefixLift 5658872
  have htrace : WordTrace (prefixWord ++ tailWord_5658872) baseStart_5658872 baseEnd_5658872 := by
    simpa [prefixWord, tailWord_5658872, baseEnd_5658872] using wordTrace_append hprefix tailTrace_5658872
  have hstable : (prefixWord ++ tailWord_5658872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658872).length < 2 ^ (prefixWord ++ tailWord_5658872).sum := by decide
  have hdescent : baseEnd_5658872 < baseStart_5658872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658903 : List Nat := [1, 1, 3, 4, 1, 2, 2, 3, 2, 1, 3]
def baseStart_5658903 : Nat := 118140960795 + 5658903 * 2 ^ 59
def prefixEnd_5658903 : Nat := 4983230072969 + 3 ^ 40 * 5658903 * 2
def baseEnd_5658903 : Nat := 2905737216169978249687685

theorem tailTrace_5658903 : CollatzResearch.WordTrace tailWord_5658903 prefixEnd_5658903 2905737216169978249687685 := by
  unfold tailWord_5658903
  simp only [CollatzResearch.WordTrace]
  refine ⟨206397148617768369533405363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137598099078512246355603575 206397148617768369533405363)
  ·
    refine ⟨309595722926652554300108045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206397148617768369533405363 309595722926652554300108045)
    ·
      refine ⟨116098396097494707862540517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309595722926652554300108045 116098396097494707862540517)
      ·
        refine ⟨21768449268280257724226347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116098396097494707862540517 21768449268280257724226347)
        ·
          refine ⟨32652673902420386586339521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21768449268280257724226347 32652673902420386586339521)
          ·
            refine ⟨24489505426815289939754641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32652673902420386586339521 24489505426815289939754641)
            ·
              refine ⟨18367129070111467454815981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24489505426815289939754641 18367129070111467454815981)
              ·
                refine ⟨6887673401291800295555993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18367129070111467454815981 6887673401291800295555993)
                ·
                  refine ⟨5165755050968850221666995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6887673401291800295555993 5165755050968850221666995)
                  ·
                    refine ⟨7748632576453275332500493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5165755050968850221666995 7748632576453275332500493)
                    ·
                      refine ⟨2905737216169978249687685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7748632576453275332500493 2905737216169978249687685)
                      ·
                        rfl

theorem cell23_5658903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_5658903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658903 prefixEnd_5658903 := by exact prefixLift 5658903
  have htrace : WordTrace (prefixWord ++ tailWord_5658903) baseStart_5658903 baseEnd_5658903 := by
    simpa [prefixWord, tailWord_5658903, baseEnd_5658903] using wordTrace_append hprefix tailTrace_5658903
  have hstable : (prefixWord ++ tailWord_5658903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658903).length < 2 ^ (prefixWord ++ tailWord_5658903).sum := by decide
  have hdescent : baseEnd_5658903 < baseStart_5658903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658930 : List Nat := [3, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2]
def baseStart_5658930 : Nat := 118140960795 + 5658930 * 2 ^ 59
def prefixEnd_5658930 : Nat := 4983230072969 + 3 ^ 40 * 5658930 * 2
def baseEnd_5658930 : Nat := 2905751080147649644050061

theorem tailTrace_5658930 : CollatzResearch.WordTrace tailWord_5658930 prefixEnd_5658930 2905751080147649644050061 := by
  unfold tailWord_5658930
  simp only [CollatzResearch.WordTrace]
  refine ⟨51599533347167638286159561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137598755592447035429758829 51599533347167638286159561)
  ·
    refine ⟨38699650010375728714619671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51599533347167638286159561 38699650010375728714619671)
    ·
      refine ⟨58049475015563593071929507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38699650010375728714619671 58049475015563593071929507)
      ·
        refine ⟨87074212523345389607894261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58049475015563593071929507 87074212523345389607894261)
        ·
          refine ⟨8163207424063630275740087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87074212523345389607894261 8163207424063630275740087)
          ·
            refine ⟨12244811136095445413610131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8163207424063630275740087 12244811136095445413610131)
            ·
              refine ⟨18367216704143168120415197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12244811136095445413610131 18367216704143168120415197)
              ·
                refine ⟨6887706264053688045155699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18367216704143168120415197 6887706264053688045155699)
                ·
                  refine ⟨10331559396080532067733549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6887706264053688045155699 10331559396080532067733549)
                  ·
                    refine ⟨3874334773530199525400081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10331559396080532067733549 3874334773530199525400081)
                    ·
                      refine ⟨2905751080147649644050061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3874334773530199525400081 2905751080147649644050061)
                      ·
                        rfl

theorem cell23_5658930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_5658930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658930 prefixEnd_5658930 := by exact prefixLift 5658930
  have htrace : WordTrace (prefixWord ++ tailWord_5658930) baseStart_5658930 baseEnd_5658930 := by
    simpa [prefixWord, tailWord_5658930, baseEnd_5658930] using wordTrace_append hprefix tailTrace_5658930
  have hstable : (prefixWord ++ tailWord_5658930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658930).length < 2 ^ (prefixWord ++ tailWord_5658930).sum := by decide
  have hdescent : baseEnd_5658930 < baseStart_5658930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658943 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 4, 2, 2]
def baseStart_5658943 : Nat := 118140960795 + 5658943 * 2 ^ 59
def prefixEnd_5658943 : Nat := 4983230072969 + 3 ^ 40 * 5658943 * 2
def baseEnd_5658943 : Nat := 2905757755396158093187501

theorem tailTrace_5658943 : CollatzResearch.WordTrace tailWord_5658943 prefixEnd_5658943 2905757755396158093187501 := by
  unfold tailWord_5658943
  simp only [CollatzResearch.WordTrace]
  refine ⟨206398607537623456364861483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137599071691748970909907655 206398607537623456364861483)
  ·
    refine ⟨309597911306435184547292225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206398607537623456364861483 309597911306435184547292225)
    ·
      refine ⟨232198433479826388410469169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309597911306435184547292225 232198433479826388410469169)
      ·
        refine ⟨174148825109869791307851877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232198433479826388410469169 174148825109869791307851877)
        ·
          refine ⟨32652904708100585870222227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174148825109869791307851877 32652904708100585870222227)
          ·
            refine ⟨48979357062150878805333341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32652904708100585870222227 48979357062150878805333341)
            ·
              refine ⟨18367258898306579552000003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48979357062150878805333341 18367258898306579552000003)
              ·
                refine ⟨27550888347459869328000005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18367258898306579552000003 27550888347459869328000005)
                ·
                  refine ⟨5165791565148725499000001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27550888347459869328000005 5165791565148725499000001)
                  ·
                    refine ⟨3874343673861544124250001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5165791565148725499000001 3874343673861544124250001)
                    ·
                      refine ⟨2905757755396158093187501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3874343673861544124250001 2905757755396158093187501)
                      ·
                        rfl

theorem cell23_5658943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 2, 2].length) (baseStart_5658943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658943 prefixEnd_5658943 := by exact prefixLift 5658943
  have htrace : WordTrace (prefixWord ++ tailWord_5658943) baseStart_5658943 baseEnd_5658943 := by
    simpa [prefixWord, tailWord_5658943, baseEnd_5658943] using wordTrace_append hprefix tailTrace_5658943
  have hstable : (prefixWord ++ tailWord_5658943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658943).length < 2 ^ (prefixWord ++ tailWord_5658943).sum := by decide
  have hdescent : baseEnd_5658943 < baseStart_5658943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658959 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 3]
def baseStart_5658959 : Nat := 118140960795 + 5658959 * 2 ^ 59
def prefixEnd_5658959 : Nat := 4983230072969 + 3 ^ 40 * 5658959 * 2
def baseEnd_5658959 : Nat := 2905765971086630030587427

theorem tailTrace_5658959 : CollatzResearch.WordTrace tailWord_5658959 prefixEnd_5658959 2905765971086630030587427 := by
  unfold tailWord_5658959
  simp only [CollatzResearch.WordTrace]
  refine ⟨206399191105565491097443931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137599460737043660731629287 206399191105565491097443931)
  ·
    refine ⟨309598786658348236646165897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206399191105565491097443931 309598786658348236646165897)
    ·
      refine ⟨232199089993761177484624423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309598786658348236646165897 232199089993761177484624423)
      ·
        refine ⟨348298634990641766226936635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232199089993761177484624423 348298634990641766226936635)
        ·
          refine ⟨522447952485962649340404953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348298634990641766226936635 522447952485962649340404953)
          ·
            refine ⟨391835964364471987005303715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522447952485962649340404953 391835964364471987005303715)
            ·
              refine ⟨587753946546707980507955573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391835964364471987005303715 587753946546707980507955573)
              ·
                refine ⟨55101932488753873172620835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 587753946546707980507955573 55101932488753873172620835)
                ·
                  refine ⟨82652898733130809758931253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55101932488753873172620835 82652898733130809758931253)
                  ·
                    refine ⟨7748709256231013414899805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82652898733130809758931253 7748709256231013414899805)
                    ·
                      refine ⟨2905765971086630030587427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7748709256231013414899805 2905765971086630030587427)
                      ·
                        rfl

theorem cell23_5658959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 3].length) (baseStart_5658959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658959 prefixEnd_5658959 := by exact prefixLift 5658959
  have htrace : WordTrace (prefixWord ++ tailWord_5658959) baseStart_5658959 baseEnd_5658959 := by
    simpa [prefixWord, tailWord_5658959, baseEnd_5658959] using wordTrace_append hprefix tailTrace_5658959
  have hstable : (prefixWord ++ tailWord_5658959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658959).length < 2 ^ (prefixWord ++ tailWord_5658959).sum := by decide
  have hdescent : baseEnd_5658959 < baseStart_5658959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658979 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 1, 7]
def baseStart_5658979 : Nat := 118140960795 + 5658979 * 2 ^ 59
def prefixEnd_5658979 : Nat := 4983230072969 + 3 ^ 40 * 5658979 * 2
def baseEnd_5658979 : Nat := 968592080233239984112445

theorem tailTrace_5658979 : CollatzResearch.WordTrace tailWord_5658979 prefixEnd_5658979 968592080233239984112445 := by
  unfold tailWord_5658979
  simp only [CollatzResearch.WordTrace]
  refine ⟨206399920565493034513171991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137599947043662023008781327 206399920565493034513171991)
  ·
    refine ⟨309599880848239551769757987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206399920565493034513171991 309599880848239551769757987)
    ·
      refine ⟨464399821272359327654636981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309599880848239551769757987 464399821272359327654636981)
      ·
        refine ⟨43537483244283686967622217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 464399821272359327654636981 43537483244283686967622217)
        ·
          refine ⟨32653112433212765225716663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43537483244283686967622217 32653112433212765225716663)
          ·
            refine ⟨48979668649819147838574995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32653112433212765225716663 48979668649819147838574995)
            ·
              refine ⟨73469502974728721757862493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48979668649819147838574995 73469502974728721757862493)
              ·
                refine ⟨27551063615523270659198435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73469502974728721757862493 27551063615523270659198435)
                ·
                  refine ⟨41326595423284905988797653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27551063615523270659198435 41326595423284905988797653)
                  ·
                    refine ⟨968592080233239984112445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41326595423284905988797653 968592080233239984112445)
                    ·
                      rfl

theorem cell23_5658979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 7].length) (baseStart_5658979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658979 prefixEnd_5658979 := by exact prefixLift 5658979
  have htrace : WordTrace (prefixWord ++ tailWord_5658979) baseStart_5658979 baseEnd_5658979 := by
    simpa [prefixWord, tailWord_5658979, baseEnd_5658979] using wordTrace_append hprefix tailTrace_5658979
  have hstable : (prefixWord ++ tailWord_5658979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658979).length < 2 ^ (prefixWord ++ tailWord_5658979).sum := by decide
  have hdescent : baseEnd_5658979 < baseStart_5658979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658983 : List Nat := [1, 1, 5, 1, 3, 1, 3, 3, 5]
def baseStart_5658983 : Nat := 118140960795 + 5658983 * 2 ^ 59
def prefixEnd_5658983 : Nat := 4983230072969 + 3 ^ 40 * 5658983 * 2
def baseEnd_5658983 : Nat := 322864254958037548520813

theorem tailTrace_5658983 : CollatzResearch.WordTrace tailWord_5658983 prefixEnd_5658983 322864254958037548520813 := by
  unfold tailWord_5658983
  simp only [CollatzResearch.WordTrace]
  refine ⟨206400066457478543196317603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137600044304985695464211735 206400066457478543196317603)
  ·
    refine ⟨309600099686217814794476405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206400066457478543196317603 309600099686217814794476405)
    ·
      refine ⟨29025009345582920136982163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 309600099686217814794476405 29025009345582920136982163)
      ·
        refine ⟨43537514018374380205473245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29025009345582920136982163 43537514018374380205473245)
        ·
          refine ⟨16326567756890392577052467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43537514018374380205473245 16326567756890392577052467)
          ·
            refine ⟨24489851635335588865578701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16326567756890392577052467 24489851635335588865578701)
            ·
              refine ⟨9183694363250845824592013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24489851635335588865578701 9183694363250845824592013)
              ·
                refine ⟨3443885386219067184222005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9183694363250845824592013 3443885386219067184222005)
                ·
                  refine ⟨322864254958037548520813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3443885386219067184222005 322864254958037548520813)
                  ·
                    rfl

theorem cell23_5658983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 5].length) (baseStart_5658983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658983 prefixEnd_5658983 := by exact prefixLift 5658983
  have htrace : WordTrace (prefixWord ++ tailWord_5658983) baseStart_5658983 baseEnd_5658983 := by
    simpa [prefixWord, tailWord_5658983, baseEnd_5658983] using wordTrace_append hprefix tailTrace_5658983
  have hstable : (prefixWord ++ tailWord_5658983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658983).length < 2 ^ (prefixWord ++ tailWord_5658983).sum := by decide
  have hdescent : baseEnd_5658983 < baseStart_5658983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5658999 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 4]
def baseStart_5658999 : Nat := 118140960795 + 5658999 * 2 ^ 59
def prefixEnd_5658999 : Nat := 4983230072969 + 3 ^ 40 * 5658999 * 2
def baseEnd_5658999 : Nat := 2905786510312809874087243

theorem tailTrace_5658999 : CollatzResearch.WordTrace tailWord_5658999 prefixEnd_5658999 2905786510312809874087243 := by
  unfold tailWord_5658999
  simp only [CollatzResearch.WordTrace]
  refine ⟨206400650025420577928900051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137600433350280385285933367 206400650025420577928900051)
  ·
    refine ⟨309600975038130866893350077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206400650025420577928900051 309600975038130866893350077)
    ·
      refine ⟨116100365639299075085006279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309600975038130866893350077 116100365639299075085006279)
      ·
        refine ⟨174150548458948612627509419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116100365639299075085006279 174150548458948612627509419)
        ·
          refine ⟨261225822688422918941264129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174150548458948612627509419 261225822688422918941264129)
          ·
            refine ⟨195919367016317189205948097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261225822688422918941264129 195919367016317189205948097)
            ·
              refine ⟨146939525262237891904461073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195919367016317189205948097 146939525262237891904461073)
              ·
                refine ⟨110204643946678418928345805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146939525262237891904461073 110204643946678418928345805)
                ·
                  refine ⟨41326741480004407098129677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110204643946678418928345805 41326741480004407098129677)
                  ·
                    refine ⟨15497528055001652661798629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41326741480004407098129677 15497528055001652661798629)
                    ·
                      refine ⟨2905786510312809874087243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15497528055001652661798629 2905786510312809874087243)
                      ·
                        rfl

theorem cell23_5658999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_5658999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5658999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5658999 prefixEnd_5658999 := by exact prefixLift 5658999
  have htrace : WordTrace (prefixWord ++ tailWord_5658999) baseStart_5658999 baseEnd_5658999 := by
    simpa [prefixWord, tailWord_5658999, baseEnd_5658999] using wordTrace_append hprefix tailTrace_5658999
  have hstable : (prefixWord ++ tailWord_5658999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5658999).length < 2 ^ (prefixWord ++ tailWord_5658999).sum := by decide
  have hdescent : baseEnd_5658999 < baseStart_5658999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5658999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659016 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_5659016 : Nat := 118140960795 + 5659016 * 2 ^ 59
def prefixEnd_5659016 : Nat := 4983230072969 + 3 ^ 40 * 5659016 * 2
def baseEnd_5659016 : Nat := 2905795239483936307574665

theorem tailTrace_5659016 : CollatzResearch.WordTrace tailWord_5659016 prefixEnd_5659016 2905795239483936307574665 := by
  unfold tailWord_5659016
  simp only [CollatzResearch.WordTrace]
  refine ⟨103200635033179494916134451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137600846710905993221512601 103200635033179494916134451)
  ·
    refine ⟨154800952549769242374201677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103200635033179494916134451 154800952549769242374201677)
    ·
      refine ⟨58050357206163465890325629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154800952549769242374201677 58050357206163465890325629)
      ·
        refine ⟨21768883952311299708872111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58050357206163465890325629 21768883952311299708872111)
        ·
          refine ⟨32653325928466949563308167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21768883952311299708872111 32653325928466949563308167)
          ·
            refine ⟨48979988892700424344962251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32653325928466949563308167 48979988892700424344962251)
            ·
              refine ⟨73469983339050636517443377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48979988892700424344962251 73469983339050636517443377)
              ·
                refine ⟨55102487504287977388082533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73469983339050636517443377 55102487504287977388082533)
                ·
                  refine ⟨10331716407053995760265475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55102487504287977388082533 10331716407053995760265475)
                  ·
                    refine ⟨15497574610580993640398213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10331716407053995760265475 15497574610580993640398213)
                    ·
                      refine ⟨2905795239483936307574665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15497574610580993640398213 2905795239483936307574665)
                      ·
                        rfl

theorem cell23_5659016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_5659016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659016 prefixEnd_5659016 := by exact prefixLift 5659016
  have htrace : WordTrace (prefixWord ++ tailWord_5659016) baseStart_5659016 baseEnd_5659016 := by
    simpa [prefixWord, tailWord_5659016, baseEnd_5659016] using wordTrace_append hprefix tailTrace_5659016
  have hstable : (prefixWord ++ tailWord_5659016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659016).length < 2 ^ (prefixWord ++ tailWord_5659016).sum := by decide
  have hdescent : baseEnd_5659016 < baseStart_5659016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659029 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_5659029 : Nat := 118140960795 + 5659029 * 2 ^ 59
def prefixEnd_5659029 : Nat := 4983230072969 + 3 ^ 40 * 5659029 * 2
def baseEnd_5659029 : Nat := 2905801914732444756712105

theorem tailTrace_5659029 : CollatzResearch.WordTrace tailWord_5659029 prefixEnd_5659029 2905801914732444756712105 := by
  unfold tailWord_5659029
  simp only [CollatzResearch.WordTrace]
  refine ⟨206401744215311893052492141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137601162810207928701661427 206401744215311893052492141)
  ·
    refine ⟨77400654080741959894684553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206401744215311893052492141 77400654080741959894684553)
    ·
      refine ⟨58050490560556469921013415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77400654080741959894684553 58050490560556469921013415)
      ·
        refine ⟨87075735840834704881520123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58050490560556469921013415 87075735840834704881520123)
        ·
          refine ⟨130613603761252057322280185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87075735840834704881520123 130613603761252057322280185)
          ·
            refine ⟨97960202820939042991710139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130613603761252057322280185 97960202820939042991710139)
            ·
              refine ⟨146940304231408564487565209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97960202820939042991710139 146940304231408564487565209)
              ·
                refine ⟨110205228173556423365673907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146940304231408564487565209 110205228173556423365673907)
                ·
                  refine ⟨165307842260334635048510861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110205228173556423365673907 165307842260334635048510861)
                  ·
                    refine ⟨61990440847625488143191573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165307842260334635048510861 61990440847625488143191573)
                    ·
                      refine ⟨2905801914732444756712105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61990440847625488143191573 2905801914732444756712105)
                      ·
                        rfl

theorem cell23_5659029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_5659029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659029 prefixEnd_5659029 := by exact prefixLift 5659029
  have htrace : WordTrace (prefixWord ++ tailWord_5659029) baseStart_5659029 baseEnd_5659029 := by
    simpa [prefixWord, tailWord_5659029, baseEnd_5659029] using wordTrace_append hprefix tailTrace_5659029
  have hstable : (prefixWord ++ tailWord_5659029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659029).length < 2 ^ (prefixWord ++ tailWord_5659029).sum := by decide
  have hdescent : baseEnd_5659029 < baseStart_5659029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659103 : List Nat := [1, 1, 2, 3, 3, 3, 1, 3, 1, 5]
def baseStart_5659103 : Nat := 118140960795 + 5659103 * 2 ^ 59
def prefixEnd_5659103 : Nat := 4983230072969 + 3 ^ 40 * 5659103 * 2
def baseEnd_5659103 : Nat := 968613304100292489062255

theorem tailTrace_5659103 : CollatzResearch.WordTrace tailWord_5659103 prefixEnd_5659103 968613304100292489062255 := by
  unfold tailWord_5659103
  simp only [CollatzResearch.WordTrace]
  refine ⟨206404443217043803690685963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137602962144695869127123975 206404443217043803690685963)
  ·
    refine ⟨309606664825565705536028945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206404443217043803690685963 309606664825565705536028945)
    ·
      refine ⟨232204998619174279152021709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309606664825565705536028945 232204998619174279152021709)
      ·
        refine ⟨87076874482190354682008141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232204998619174279152021709 87076874482190354682008141)
        ·
          refine ⟨32653827930821383005753053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87076874482190354682008141 32653827930821383005753053)
          ·
            refine ⟨12245185474058018627157395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32653827930821383005753053 12245185474058018627157395)
            ·
              refine ⟨18367778211087027940736093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12245185474058018627157395 18367778211087027940736093)
              ·
                refine ⟨6887916829157635477776035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18367778211087027940736093 6887916829157635477776035)
                ·
                  refine ⟨10331875243736453216664053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6887916829157635477776035 10331875243736453216664053)
                  ·
                    refine ⟨968613304100292489062255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10331875243736453216664053 968613304100292489062255)
                    ·
                      rfl

theorem cell23_5659103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 5].length) (baseStart_5659103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659103 prefixEnd_5659103 := by exact prefixLift 5659103
  have htrace : WordTrace (prefixWord ++ tailWord_5659103) baseStart_5659103 baseEnd_5659103 := by
    simpa [prefixWord, tailWord_5659103, baseEnd_5659103] using wordTrace_append hprefix tailTrace_5659103
  have hstable : (prefixWord ++ tailWord_5659103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659103).length < 2 ^ (prefixWord ++ tailWord_5659103).sum := by decide
  have hdescent : baseEnd_5659103 < baseStart_5659103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659117 : List Nat := [1, 5, 1, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_5659117 : Nat := 118140960795 + 5659117 * 2 ^ 59
def prefixEnd_5659117 : Nat := 4983230072969 + 3 ^ 40 * 5659117 * 2
def baseEnd_5659117 : Nat := 2905847101030040412411701

theorem tailTrace_5659117 : CollatzResearch.WordTrace tailWord_5659117 prefixEnd_5659117 2905847101030040412411701 := by
  unfold tailWord_5659117
  simp only [CollatzResearch.WordTrace]
  refine ⟨206404953838993084081695605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137603302559328722721130403 206404953838993084081695605)
  ·
    refine ⟨19350464422405601632658963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206404953838993084081695605 19350464422405601632658963)
    ·
      refine ⟨29025696633608402448988445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19350464422405601632658963 29025696633608402448988445)
      ·
        refine ⟨10884636237603150918370667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29025696633608402448988445 10884636237603150918370667)
        ·
          refine ⟨16326954356404726377556001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10884636237603150918370667 16326954356404726377556001)
          ·
            refine ⟨12245215767303544783167001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16326954356404726377556001 12245215767303544783167001)
            ·
              refine ⟨9183911825477658587375251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12245215767303544783167001 9183911825477658587375251)
              ·
                refine ⟨13775867738216487881062877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9183911825477658587375251 13775867738216487881062877)
                ·
                  refine ⟨5165950401831182955398579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13775867738216487881062877 5165950401831182955398579)
                  ·
                    refine ⟨7748925602746774433097869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5165950401831182955398579 7748925602746774433097869)
                    ·
                      refine ⟨2905847101030040412411701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7748925602746774433097869 2905847101030040412411701)
                      ·
                        rfl

theorem cell23_5659117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_5659117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659117 prefixEnd_5659117 := by exact prefixLift 5659117
  have htrace : WordTrace (prefixWord ++ tailWord_5659117) baseStart_5659117 baseEnd_5659117 := by
    simpa [prefixWord, tailWord_5659117, baseEnd_5659117] using wordTrace_append hprefix tailTrace_5659117
  have hstable : (prefixWord ++ tailWord_5659117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659117).length < 2 ^ (prefixWord ++ tailWord_5659117).sum := by decide
  have hdescent : baseEnd_5659117 < baseStart_5659117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659140 : List Nat := [2, 3, 2, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_5659140 : Nat := 118140960795 + 5659140 * 2 ^ 59
def prefixEnd_5659140 : Nat := 4983230072969 + 3 ^ 40 * 5659140 * 2
def baseEnd_5659140 : Nat := 2905858911085093822424095

theorem tailTrace_5659140 : CollatzResearch.WordTrace tailWord_5659140 prefixEnd_5659140 2905858911085093822424095 := by
  unfold tailWord_5659140
  simp only [CollatzResearch.WordTrace]
  refine ⟨103202896358954879504891437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137603861811939839339855249 103202896358954879504891437)
  ·
    refine ⟨38701086134608079814334289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103202896358954879504891437 38701086134608079814334289)
    ·
      refine ⟨29025814600956059860750717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38701086134608079814334289 29025814600956059860750717)
      ·
        refine ⟨10884680475358522447781519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29025814600956059860750717 10884680475358522447781519)
        ·
          refine ⟨16327020713037783671672279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10884680475358522447781519 16327020713037783671672279)
          ·
            refine ⟨24490531069556675507508419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16327020713037783671672279 24490531069556675507508419)
            ·
              refine ⟨36735796604335013261262629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24490531069556675507508419 36735796604335013261262629)
              ·
                refine ⟨6887961863312814986486743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36735796604335013261262629 6887961863312814986486743)
                ·
                  refine ⟨10331942794969222479730115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6887961863312814986486743 10331942794969222479730115)
                  ·
                    refine ⟨15497914192453833719595173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10331942794969222479730115 15497914192453833719595173)
                    ·
                      refine ⟨2905858911085093822424095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15497914192453833719595173 2905858911085093822424095)
                      ·
                        rfl

theorem cell23_5659140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_5659140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659140 prefixEnd_5659140 := by exact prefixLift 5659140
  have htrace : WordTrace (prefixWord ++ tailWord_5659140) baseStart_5659140 baseEnd_5659140 := by
    simpa [prefixWord, tailWord_5659140, baseEnd_5659140] using wordTrace_append hprefix tailTrace_5659140
  have hstable : (prefixWord ++ tailWord_5659140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659140).length < 2 ^ (prefixWord ++ tailWord_5659140).sum := by decide
  have hdescent : baseEnd_5659140 < baseStart_5659140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659146 : List Nat := [3, 1, 2, 2, 2, 1, 3, 9]
def baseStart_5659146 : Nat := 118140960795 + 5659146 * 2 ^ 59
def prefixEnd_5659146 : Nat := 4983230072969 + 3 ^ 40 * 5659146 * 2
def baseEnd_5659146 : Nat := 107624518221074844405521

theorem tailTrace_5659146 : CollatzResearch.WordTrace tailWord_5659146 prefixEnd_5659146 107624518221074844405521 := by
  unfold tailWord_5659146
  simp only [CollatzResearch.WordTrace]
  refine ⟨51601502888972005508625323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137604007703925348023000861 51601502888972005508625323)
  ·
    refine ⟨77402254333458008262937985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51601502888972005508625323 77402254333458008262937985)
    ·
      refine ⟨58051690750093506197203489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77402254333458008262937985 58051690750093506197203489)
      ·
        refine ⟨43538768062570129647902617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58051690750093506197203489 43538768062570129647902617)
        ·
          refine ⟨32654076046927597235926963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43538768062570129647902617 32654076046927597235926963)
          ·
            refine ⟨48981114070391395853890445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32654076046927597235926963 48981114070391395853890445)
            ·
              refine ⟨18367917776396773445208917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48981114070391395853890445 18367917776396773445208917)
              ·
                refine ⟨107624518221074844405521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18367917776396773445208917 107624518221074844405521)
                ·
                  rfl

theorem cell23_5659146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 9].length) (baseStart_5659146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659146 prefixEnd_5659146 := by exact prefixLift 5659146
  have htrace : WordTrace (prefixWord ++ tailWord_5659146) baseStart_5659146 baseEnd_5659146 := by
    simpa [prefixWord, tailWord_5659146, baseEnd_5659146] using wordTrace_append hprefix tailTrace_5659146
  have hstable : (prefixWord ++ tailWord_5659146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659146).length < 2 ^ (prefixWord ++ tailWord_5659146).sum := by decide
  have hdescent : baseEnd_5659146 < baseStart_5659146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659160 : List Nat := [2, 1, 2, 3, 3, 1, 2, 3, 1, 2, 3]
def baseStart_5659160 : Nat := 118140960795 + 5659160 * 2 ^ 59
def prefixEnd_5659160 : Nat := 4983230072969 + 3 ^ 40 * 5659160 * 2
def baseEnd_5659160 : Nat := 2905869180698183744174003

theorem tailTrace_5659160 : CollatzResearch.WordTrace tailWord_5659160 prefixEnd_5659160 2905869180698183744174003 := by
  unfold tailWord_5659160
  simp only [CollatzResearch.WordTrace]
  refine ⟨103203261088918651212755467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137604348118558201617007289 103203261088918651212755467)
  ·
    refine ⟨154804891633377976819133201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103203261088918651212755467 154804891633377976819133201)
    ·
      refine ⟨116103668725033482614349901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154804891633377976819133201 116103668725033482614349901)
      ·
        refine ⟨43538875771887555980381213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116103668725033482614349901 43538875771887555980381213)
        ·
          refine ⟨16327078414457833492642955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43538875771887555980381213 16327078414457833492642955)
          ·
            refine ⟨24490617621686750238964433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16327078414457833492642955 24490617621686750238964433)
            ·
              refine ⟨18367963216265062679223325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24490617621686750238964433 18367963216265062679223325)
              ·
                refine ⟨6887986206099398504708747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18367963216265062679223325 6887986206099398504708747)
                ·
                  refine ⟨10331979309149097757063121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6887986206099398504708747 10331979309149097757063121)
                  ·
                    refine ⟨7748984481861823317797341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10331979309149097757063121 7748984481861823317797341)
                    ·
                      refine ⟨2905869180698183744174003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7748984481861823317797341 2905869180698183744174003)
                      ·
                        rfl

theorem cell23_5659160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_5659160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659160 prefixEnd_5659160 := by exact prefixLift 5659160
  have htrace : WordTrace (prefixWord ++ tailWord_5659160) baseStart_5659160 baseEnd_5659160 := by
    simpa [prefixWord, tailWord_5659160, baseEnd_5659160] using wordTrace_append hprefix tailTrace_5659160
  have hstable : (prefixWord ++ tailWord_5659160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659160).length < 2 ^ (prefixWord ++ tailWord_5659160).sum := by decide
  have hdescent : baseEnd_5659160 < baseStart_5659160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659204 : List Nat := [2, 3, 5, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_5659204 : Nat := 118140960795 + 5659204 * 2 ^ 59
def prefixEnd_5659204 : Nat := 4983230072969 + 3 ^ 40 * 5659204 * 2
def baseEnd_5659204 : Nat := 2905891773846981572023801

theorem tailTrace_5659204 : CollatzResearch.WordTrace tailWord_5659204 prefixEnd_5659204 2905891773846981572023801 := by
  unfold tailWord_5659204
  simp only [CollatzResearch.WordTrace]
  refine ⟨103204063494838948970056333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137605417993118598626741777 103204063494838948970056333)
  ·
    refine ⟨38701523810564605863771125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103204063494838948970056333 38701523810564605863771125)
    ·
      refine ⟨3628267857240431799728543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38701523810564605863771125 3628267857240431799728543)
      ·
        refine ⟨5442401785860647699592815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3628267857240431799728543 5442401785860647699592815)
        ·
          refine ⟨8163602678790971549389223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5442401785860647699592815 8163602678790971549389223)
          ·
            refine ⟨12245404018186457324083835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8163602678790971549389223 12245404018186457324083835)
            ·
              refine ⟨18368106027279685986125753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12245404018186457324083835 18368106027279685986125753)
              ·
                refine ⟨13776079520459764489594315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18368106027279685986125753 13776079520459764489594315)
                ·
                  refine ⟨20664119280689646734391473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13776079520459764489594315 20664119280689646734391473)
                  ·
                    refine ⟨15498089460517235050793605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20664119280689646734391473 15498089460517235050793605)
                    ·
                      refine ⟨2905891773846981572023801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15498089460517235050793605 2905891773846981572023801)
                      ·
                        rfl

theorem cell23_5659204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_5659204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659204 prefixEnd_5659204 := by exact prefixLift 5659204
  have htrace : WordTrace (prefixWord ++ tailWord_5659204) baseStart_5659204 baseEnd_5659204 := by
    simpa [prefixWord, tailWord_5659204, baseEnd_5659204] using wordTrace_append hprefix tailTrace_5659204
  have hstable : (prefixWord ++ tailWord_5659204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659204).length < 2 ^ (prefixWord ++ tailWord_5659204).sum := by decide
  have hdescent : baseEnd_5659204 < baseStart_5659204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659216 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 5]
def baseStart_5659216 : Nat := 118140960795 + 5659216 * 2 ^ 59
def prefixEnd_5659216 : Nat := 4983230072969 + 3 ^ 40 * 5659216 * 2
def baseEnd_5659216 : Nat := 2905897935614835525073745

theorem tailTrace_5659216 : CollatzResearch.WordTrace tailWord_5659216 prefixEnd_5659216 2905897935614835525073745 := by
  unfold tailWord_5659216
  simp only [CollatzResearch.WordTrace]
  refine ⟨103204282332817211994774751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137605709777089615993033001 103204282332817211994774751)
  ·
    refine ⟨154806423499225817992162127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103204282332817211994774751 154806423499225817992162127)
    ·
      refine ⟨232209635248838726988243191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154806423499225817992162127 232209635248838726988243191)
      ·
        refine ⟨348314452873258090482364787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232209635248838726988243191 348314452873258090482364787)
        ·
          refine ⟨522471679309887135723547181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348314452873258090482364787 522471679309887135723547181)
          ·
            refine ⟨195926879741207675896330193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 522471679309887135723547181 195926879741207675896330193)
            ·
              refine ⟨146945159805905756922247645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195926879741207675896330193 146945159805905756922247645)
              ·
                refine ⟨55104434927214658845842867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146945159805905756922247645 55104434927214658845842867)
                ·
                  refine ⟨82656652390821988268764301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55104434927214658845842867 82656652390821988268764301)
                  ·
                    refine ⟨30996244646558245600786613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82656652390821988268764301 30996244646558245600786613)
                    ·
                      refine ⟨2905897935614835525073745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30996244646558245600786613 2905897935614835525073745)
                      ·
                        rfl

theorem cell23_5659216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_5659216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659216 prefixEnd_5659216 := by exact prefixLift 5659216
  have htrace : WordTrace (prefixWord ++ tailWord_5659216) baseStart_5659216 baseEnd_5659216 := by
    simpa [prefixWord, tailWord_5659216, baseEnd_5659216] using wordTrace_append hprefix tailTrace_5659216
  have hstable : (prefixWord ++ tailWord_5659216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659216).length < 2 ^ (prefixWord ++ tailWord_5659216).sum := by decide
  have hdescent : baseEnd_5659216 < baseStart_5659216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659226 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6]
def baseStart_5659226 : Nat := 118140960795 + 5659226 * 2 ^ 59
def prefixEnd_5659226 : Nat := 4983230072969 + 3 ^ 40 * 5659226 * 2
def baseEnd_5659226 : Nat := 2905903070421380485948699

theorem tailTrace_5659226 : CollatzResearch.WordTrace tailWord_5659226 prefixEnd_5659226 2905903070421380485948699 := by
  unfold tailWord_5659226
  simp only [CollatzResearch.WordTrace]
  refine ⟨51602232348899548924353383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137605952930398797131609021 51602232348899548924353383)
  ·
    refine ⟨77403348523349323386530075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51602232348899548924353383 77403348523349323386530075)
    ·
      refine ⟨116105022785023985079795113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77403348523349323386530075 116105022785023985079795113)
      ·
        refine ⟨87078767088767988809846335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116105022785023985079795113 87078767088767988809846335)
        ·
          refine ⟨130618150633151983214769503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87078767088767988809846335 130618150633151983214769503)
          ·
            refine ⟨195927225949727974822154255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130618150633151983214769503 195927225949727974822154255)
            ·
              refine ⟨293890838924591962233231383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195927225949727974822154255 293890838924591962233231383)
              ·
                refine ⟨440836258386887943349847075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293890838924591962233231383 440836258386887943349847075)
                ·
                  refine ⟨661254387580331915024770613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440836258386887943349847075 661254387580331915024770613)
                  ·
                    refine ⟨61992598835656117033572245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 661254387580331915024770613 61992598835656117033572245)
                    ·
                      refine ⟨2905903070421380485948699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61992598835656117033572245 2905903070421380485948699)
                      ·
                        rfl

theorem cell23_5659226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_5659226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659226 prefixEnd_5659226 := by exact prefixLift 5659226
  have htrace : WordTrace (prefixWord ++ tailWord_5659226) baseStart_5659226 baseEnd_5659226 := by
    simpa [prefixWord, tailWord_5659226, baseEnd_5659226] using wordTrace_append hprefix tailTrace_5659226
  have hstable : (prefixWord ++ tailWord_5659226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659226).length < 2 ^ (prefixWord ++ tailWord_5659226).sum := by decide
  have hdescent : baseEnd_5659226 < baseStart_5659226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659233 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 2, 4, 3]
def baseStart_5659233 : Nat := 118140960795 + 5659233 * 2 ^ 59
def prefixEnd_5659233 : Nat := 4983230072969 + 3 ^ 40 * 5659233 * 2
def baseEnd_5659233 : Nat := 2905906664785961958561167

theorem tailTrace_5659233 : CollatzResearch.WordTrace tailWord_5659233 prefixEnd_5659233 2905906664785961958561167 := by
  unfold tailWord_5659233
  simp only [CollatzResearch.WordTrace]
  refine ⟨206409184706572835892918353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137606123137715223928612235 206409184706572835892918353)
  ·
    refine ⟨154806888529929626919688765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206409184706572835892918353 154806888529929626919688765)
    ·
      refine ⟨58052583198723610094883287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154806888529929626919688765 58052583198723610094883287)
      ·
        refine ⟨87078874798085415142324931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58052583198723610094883287 87078874798085415142324931)
        ·
          refine ⟨130618312197128122713487397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87078874798085415142324931 130618312197128122713487397)
          ·
            refine ⟨24490933536961523008778887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130618312197128122713487397 24490933536961523008778887)
            ·
              refine ⟨36736400305442284513168331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24490933536961523008778887 36736400305442284513168331)
              ·
                refine ⟨55104600458163426769752497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36736400305442284513168331 55104600458163426769752497)
                ·
                  refine ⟨41328450343622570077314373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55104600458163426769752497 41328450343622570077314373)
                  ·
                    refine ⟨7749084439429231889496445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41328450343622570077314373 7749084439429231889496445)
                    ·
                      refine ⟨2905906664785961958561167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7749084439429231889496445 2905906664785961958561167)
                      ·
                        rfl

theorem cell23_5659233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_5659233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659233 prefixEnd_5659233 := by exact prefixLift 5659233
  have htrace : WordTrace (prefixWord ++ tailWord_5659233) baseStart_5659233 baseEnd_5659233 := by
    simpa [prefixWord, tailWord_5659233, baseEnd_5659233] using wordTrace_append hprefix tailTrace_5659233
  have hstable : (prefixWord ++ tailWord_5659233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659233).length < 2 ^ (prefixWord ++ tailWord_5659233).sum := by decide
  have hdescent : baseEnd_5659233 < baseStart_5659233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659240 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 2, 6]
def baseStart_5659240 : Nat := 118140960795 + 5659240 * 2 ^ 59
def prefixEnd_5659240 : Nat := 4983230072969 + 3 ^ 40 * 5659240 * 2
def baseEnd_5659240 : Nat := 968636753050181143724545

theorem tailTrace_5659240 : CollatzResearch.WordTrace tailWord_5659240 prefixEnd_5659240 968636753050181143724545 := by
  unfold tailWord_5659240
  simp only [CollatzResearch.WordTrace]
  refine ⟨103204720008773738044211587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137606293345031650725615449 103204720008773738044211587)
  ·
    refine ⟨154807080013160607066317381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103204720008773738044211587 154807080013160607066317381)
    ·
      refine ⟨29026327502467613824934509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154807080013160607066317381 29026327502467613824934509)
      ·
        refine ⟨10884872813425355184350441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29026327502467613824934509 10884872813425355184350441)
        ·
          refine ⟨8163654610069016388262831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10884872813425355184350441 8163654610069016388262831)
          ·
            refine ⟨12245481915103524582394247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8163654610069016388262831 12245481915103524582394247)
            ·
              refine ⟨18368222872655286873591371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12245481915103524582394247 18368222872655286873591371)
              ·
                refine ⟨27552334308982930310387057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18368222872655286873591371 27552334308982930310387057)
                ·
                  refine ⟨20664250731737197732790293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27552334308982930310387057 20664250731737197732790293)
                  ·
                    refine ⟨968636753050181143724545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20664250731737197732790293 968636753050181143724545)
                    ·
                      rfl

theorem cell23_5659240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_5659240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659240 prefixEnd_5659240 := by exact prefixLift 5659240
  have htrace : WordTrace (prefixWord ++ tailWord_5659240) baseStart_5659240 baseEnd_5659240 := by
    simpa [prefixWord, tailWord_5659240, baseEnd_5659240] using wordTrace_append hprefix tailTrace_5659240
  have hstable : (prefixWord ++ tailWord_5659240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659240).length < 2 ^ (prefixWord ++ tailWord_5659240).sum := by decide
  have hdescent : baseEnd_5659240 < baseStart_5659240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659247 : List Nat := [1, 1, 2, 1, 3, 2, 4, 3, 2, 2, 2]
def baseStart_5659247 : Nat := 118140960795 + 5659247 * 2 ^ 59
def prefixEnd_5659247 : Nat := 4983230072969 + 3 ^ 40 * 5659247 * 2
def baseEnd_5659247 : Nat := 2905913853515124903786103

theorem tailTrace_5659247 : CollatzResearch.WordTrace tailWord_5659247 prefixEnd_5659247 2905913853515124903786103 := by
  unfold tailWord_5659247
  simp only [CollatzResearch.WordTrace]
  refine ⟨206409695328522116283927995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137606463552348077522618663 206409695328522116283927995)
  ·
    refine ⟨309614542992783174425891993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206409695328522116283927995 309614542992783174425891993)
    ·
      refine ⟨232210907244587380819418995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309614542992783174425891993 232210907244587380819418995)
      ·
        refine ⟨348316360866881071229128493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232210907244587380819418995 348316360866881071229128493)
        ·
          refine ⟨130618635325080401710923185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348316360866881071229128493 130618635325080401710923185)
          ·
            refine ⟨97963976493810301283192389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130618635325080401710923185 97963976493810301283192389)
            ·
              refine ⟨18368245592589431490598573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97963976493810301283192389 18368245592589431490598573)
              ·
                refine ⟨6888092097221036808974465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18368245592589431490598573 6888092097221036808974465)
                ·
                  refine ⟨5166069072915777606730849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6888092097221036808974465 5166069072915777606730849)
                  ·
                    refine ⟨3874551804686833205048137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5166069072915777606730849 3874551804686833205048137)
                    ·
                      refine ⟨2905913853515124903786103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3874551804686833205048137 2905913853515124903786103)
                      ·
                        rfl

theorem cell23_5659247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 2, 2].length) (baseStart_5659247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659247 prefixEnd_5659247 := by exact prefixLift 5659247
  have htrace : WordTrace (prefixWord ++ tailWord_5659247) baseStart_5659247 baseEnd_5659247 := by
    simpa [prefixWord, tailWord_5659247, baseEnd_5659247] using wordTrace_append hprefix tailTrace_5659247
  have hstable : (prefixWord ++ tailWord_5659247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659247).length < 2 ^ (prefixWord ++ tailWord_5659247).sum := by decide
  have hdescent : baseEnd_5659247 < baseStart_5659247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659256 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 2, 1, 8]
def baseStart_5659256 : Nat := 118140960795 + 5659256 * 2 ^ 59
def prefixEnd_5659256 : Nat := 4983230072969 + 3 ^ 40 * 5659256 * 2
def baseEnd_5659256 : Nat := 2905918474841015368573561

theorem tailTrace_5659256 : CollatzResearch.WordTrace tailWord_5659256 prefixEnd_5659256 2905918474841015368573561 := by
  unfold tailWord_5659256
  simp only [CollatzResearch.WordTrace]
  refine ⟨103205011792744755410502811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137606682390326340547337081 103205011792744755410502811)
  ·
    refine ⟨154807517689117133115754217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103205011792744755410502811 154807517689117133115754217)
    ·
      refine ⟨116105638266837849836815663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154807517689117133115754217 116105638266837849836815663)
      ·
        refine ⟨174158457400256774755223495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116105638266837849836815663 174158457400256774755223495)
        ·
          refine ⟨261237686100385162132835243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174158457400256774755223495 261237686100385162132835243)
          ·
            refine ⟨391856529150577743199252865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261237686100385162132835243 391856529150577743199252865)
            ·
              refine ⟨293892396862933307399439649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391856529150577743199252865 293892396862933307399439649)
              ·
                refine ⟨220419297647199980549579737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293892396862933307399439649 220419297647199980549579737)
                ·
                  refine ⟨165314473235399985412184803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220419297647199980549579737 165314473235399985412184803)
                  ·
                    refine ⟨247971709853099978118277205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 165314473235399985412184803 247971709853099978118277205)
                    ·
                      refine ⟨2905918474841015368573561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 247971709853099978118277205 2905918474841015368573561)
                      ·
                        rfl

theorem cell23_5659256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_5659256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659256 prefixEnd_5659256 := by exact prefixLift 5659256
  have htrace : WordTrace (prefixWord ++ tailWord_5659256) baseStart_5659256 baseEnd_5659256 := by
    simpa [prefixWord, tailWord_5659256, baseEnd_5659256] using wordTrace_append hprefix tailTrace_5659256
  have hstable : (prefixWord ++ tailWord_5659256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659256).length < 2 ^ (prefixWord ++ tailWord_5659256).sum := by decide
  have hdescent : baseEnd_5659256 < baseStart_5659256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659293 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_5659293 : Nat := 118140960795 + 5659293 * 2 ^ 59
def prefixEnd_5659293 : Nat := 4983230072969 + 3 ^ 40 * 5659293 * 2
def baseEnd_5659293 : Nat := 2905937473625231723810891

theorem tailTrace_5659293 : CollatzResearch.WordTrace tailWord_5659293 prefixEnd_5659293 2905937473625231723810891 := by
  unfold tailWord_5659293
  simp only [CollatzResearch.WordTrace]
  refine ⟨206411373086355466140102533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137607582057570310760068355 206411373086355466140102533)
  ·
    refine ⟨38702132453691649901269225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206411373086355466140102533 38702132453691649901269225)
    ·
      refine ⟨29026599340268737425951919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38702132453691649901269225 29026599340268737425951919)
      ·
        refine ⟨43539899010403106138927879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29026599340268737425951919 43539899010403106138927879)
        ·
          refine ⟨65309848515604659208391819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43539899010403106138927879 65309848515604659208391819)
          ·
            refine ⟨97964772773406988812587729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65309848515604659208391819 97964772773406988812587729)
            ·
              refine ⟨73473579580055241609440797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97964772773406988812587729 73473579580055241609440797)
              ·
                refine ⟨27552592342520715603540299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73473579580055241609440797 27552592342520715603540299)
                ·
                  refine ⟨41328888513781073405310449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27552592342520715603540299 41328888513781073405310449)
                  ·
                    refine ⟨30996666385335805053982837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41328888513781073405310449 30996666385335805053982837)
                    ·
                      refine ⟨2905937473625231723810891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30996666385335805053982837 2905937473625231723810891)
                      ·
                        rfl

theorem cell23_5659293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_5659293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659293 prefixEnd_5659293 := by exact prefixLift 5659293
  have htrace : WordTrace (prefixWord ++ tailWord_5659293) baseStart_5659293 baseEnd_5659293 := by
    simpa [prefixWord, tailWord_5659293, baseEnd_5659293] using wordTrace_append hprefix tailTrace_5659293
  have hstable : (prefixWord ++ tailWord_5659293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659293).length < 2 ^ (prefixWord ++ tailWord_5659293).sum := by decide
  have hdescent : baseEnd_5659293 < baseStart_5659293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659403 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 5, 6]
def baseStart_5659403 : Nat := 118140960795 + 5659403 * 2 ^ 59
def prefixEnd_5659403 : Nat := 4983230072969 + 3 ^ 40 * 5659403 * 2
def baseEnd_5659403 : Nat := 968664652165742097811795

theorem tailTrace_5659403 : CollatzResearch.WordTrace tailWord_5659403 prefixEnd_5659403 968664652165742097811795 := by
  unfold tailWord_5659403
  simp only [CollatzResearch.WordTrace]
  refine ⟨206415385115956954926606863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137610256743971303284404575 206415385115956954926606863)
  ·
    refine ⟨309623077673935432389910295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206415385115956954926606863 309623077673935432389910295)
    ·
      refine ⟨464434616510903148584865443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309623077673935432389910295 464434616510903148584865443)
      ·
        refine ⟨696651924766354722877298165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464434616510903148584865443 696651924766354722877298165)
        ·
          refine ⟨65311117946845755269746703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 696651924766354722877298165 65311117946845755269746703)
          ·
            refine ⟨97966676920268632904620055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65311117946845755269746703 97966676920268632904620055)
            ·
              refine ⟨146950015380402949356930083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97966676920268632904620055 146950015380402949356930083)
              ·
                refine ⟨220425023070604424035395125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146950015380402949356930083 220425023070604424035395125)
                ·
                  refine ⟨20664845912869164753318293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 220425023070604424035395125 20664845912869164753318293)
                  ·
                    refine ⟨968664652165742097811795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20664845912869164753318293 968664652165742097811795)
                    ·
                      rfl

theorem cell23_5659403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 6].length) (baseStart_5659403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659403 prefixEnd_5659403 := by exact prefixLift 5659403
  have htrace : WordTrace (prefixWord ++ tailWord_5659403) baseStart_5659403 baseEnd_5659403 := by
    simpa [prefixWord, tailWord_5659403, baseEnd_5659403] using wordTrace_append hprefix tailTrace_5659403
  have hstable : (prefixWord ++ tailWord_5659403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659403).length < 2 ^ (prefixWord ++ tailWord_5659403).sum := by decide
  have hdescent : baseEnd_5659403 < baseStart_5659403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659420 : List Nat := [2, 2, 3, 1, 1, 3, 1, 3, 1, 6]
def baseStart_5659420 : Nat := 118140960795 + 5659420 * 2 ^ 59
def prefixEnd_5659420 : Nat := 4983230072969 + 3 ^ 40 * 5659420 * 2
def baseEnd_5659420 : Nat := 968667561889450908974269

theorem tailTrace_5659420 : CollatzResearch.WordTrace tailWord_5659420 prefixEnd_5659420 968667561889450908974269 := by
  unfold tailWord_5659420
  simp only [CollatzResearch.WordTrace]
  refine ⟨103208002578447683414987857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137610670104596911219983809 103208002578447683414987857)
  ·
    refine ⟨77406001933835762561240893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103208002578447683414987857 77406001933835762561240893)
    ·
      refine ⟨29027250725188410960465335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77406001933835762561240893 29027250725188410960465335)
      ·
        refine ⟨43540876087782616440698003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29027250725188410960465335 43540876087782616440698003)
        ·
          refine ⟨65311314131673924661047005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43540876087782616440698003 65311314131673924661047005)
          ·
            refine ⟨24491742799377721747892627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65311314131673924661047005 24491742799377721747892627)
            ·
              refine ⟨36737614199066582621838941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24491742799377721747892627 36737614199066582621838941)
              ·
                refine ⟨13776605324649968483189603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36737614199066582621838941 13776605324649968483189603)
                ·
                  refine ⟨20664907986974952724784405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13776605324649968483189603 20664907986974952724784405)
                  ·
                    refine ⟨968667561889450908974269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20664907986974952724784405 968667561889450908974269)
                    ·
                      rfl

theorem cell23_5659420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_5659420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659420 prefixEnd_5659420 := by exact prefixLift 5659420
  have htrace : WordTrace (prefixWord ++ tailWord_5659420) baseStart_5659420 baseEnd_5659420 := by
    simpa [prefixWord, tailWord_5659420, baseEnd_5659420] using wordTrace_append hprefix tailTrace_5659420
  have hstable : (prefixWord ++ tailWord_5659420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659420).length < 2 ^ (prefixWord ++ tailWord_5659420).sum := by decide
  have hdescent : baseEnd_5659420 < baseStart_5659420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659421 : List Nat := [1, 4, 2, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_5659421 : Nat := 118140960795 + 5659421 * 2 ^ 59
def prefixEnd_5659421 : Nat := 4983230072969 + 3 ^ 40 * 5659421 * 2
def baseEnd_5659421 : Nat := 2906003199149007223010303

theorem tailTrace_5659421 : CollatzResearch.WordTrace tailWord_5659421 prefixEnd_5659421 2906003199149007223010303 := by
  unfold tailWord_5659421
  simp only [CollatzResearch.WordTrace]
  refine ⟨206416041629891744000762117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137610694419927829333841411 206416041629891744000762117)
  ·
    refine ⟨38703007805604702000142897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206416041629891744000762117 38703007805604702000142897)
    ·
      refine ⟨29027255854203526500107173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38703007805604702000142897 29027255854203526500107173)
      ·
        refine ⟨5442610472663161218770095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29027255854203526500107173 5442610472663161218770095)
        ·
          refine ⟨8163915708994741828155143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5442610472663161218770095 8163915708994741828155143)
          ·
            refine ⟨12245873563492112742232715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8163915708994741828155143 12245873563492112742232715)
            ·
              refine ⟨18368810345238169113349073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12245873563492112742232715 18368810345238169113349073)
              ·
                refine ⟨13776607758928626835011805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18368810345238169113349073 13776607758928626835011805)
                ·
                  refine ⟨5166227909598235063129427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13776607758928626835011805 5166227909598235063129427)
                  ·
                    refine ⟨7749341864397352594694141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5166227909598235063129427 7749341864397352594694141)
                    ·
                      refine ⟨2906003199149007223010303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7749341864397352594694141 2906003199149007223010303)
                      ·
                        rfl

theorem cell23_5659421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_5659421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659421 prefixEnd_5659421 := by exact prefixLift 5659421
  have htrace : WordTrace (prefixWord ++ tailWord_5659421) baseStart_5659421 baseEnd_5659421 := by
    simpa [prefixWord, tailWord_5659421, baseEnd_5659421] using wordTrace_append hprefix tailTrace_5659421
  have hstable : (prefixWord ++ tailWord_5659421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659421).length < 2 ^ (prefixWord ++ tailWord_5659421).sum := by decide
  have hdescent : baseEnd_5659421 < baseStart_5659421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659438 : List Nat := [4, 1, 3, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_5659438 : Nat := 118140960795 + 5659438 * 2 ^ 59
def prefixEnd_5659438 : Nat := 4983230072969 + 3 ^ 40 * 5659438 * 2
def baseEnd_5659438 : Nat := 2906011928320133656497725

theorem tailTrace_5659438 : CollatzResearch.WordTrace tailWord_5659438 prefixEnd_5659438 2906011928320133656497725 := by
  unfold tailWord_5659438
  simp only [CollatzResearch.WordTrace]
  refine ⟨25802082708853769488016371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137611107780553437269420645 25802082708853769488016371)
  ·
    refine ⟨38703124063280654232024557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25802082708853769488016371 38703124063280654232024557)
    ·
      refine ⟨14513671523730245337009209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38703124063280654232024557 14513671523730245337009209)
      ·
        refine ⟨10885253642797684002756907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14513671523730245337009209 10885253642797684002756907)
        ·
          refine ⟨16327880464196526004135361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10885253642797684002756907 16327880464196526004135361)
          ·
            refine ⟨12245910348147394503101521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16327880464196526004135361 12245910348147394503101521)
            ·
              refine ⟨9184432761110545877326141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12245910348147394503101521 9184432761110545877326141)
              ·
                refine ⟨3444162285416454703997303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9184432761110545877326141 3444162285416454703997303)
                ·
                  refine ⟨5166243428124682055995955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3444162285416454703997303 5166243428124682055995955)
                  ·
                    refine ⟨7749365142187023083993933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5166243428124682055995955 7749365142187023083993933)
                    ·
                      refine ⟨2906011928320133656497725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7749365142187023083993933 2906011928320133656497725)
                      ·
                        rfl

theorem cell23_5659438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_5659438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659438 prefixEnd_5659438 := by exact prefixLift 5659438
  have htrace : WordTrace (prefixWord ++ tailWord_5659438) baseStart_5659438 baseEnd_5659438 := by
    simpa [prefixWord, tailWord_5659438, baseEnd_5659438] using wordTrace_append hprefix tailTrace_5659438
  have hstable : (prefixWord ++ tailWord_5659438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659438).length < 2 ^ (prefixWord ++ tailWord_5659438).sum := by decide
  have hdescent : baseEnd_5659438 < baseStart_5659438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659447 : List Nat := [1, 1, 3, 1, 2, 1, 5, 3, 1, 2, 3]
def baseStart_5659447 : Nat := 118140960795 + 5659447 * 2 ^ 59
def prefixEnd_5659447 : Nat := 4983230072969 + 3 ^ 40 * 5659447 * 2
def baseEnd_5659447 : Nat := 2906016549646024121285183

theorem tailTrace_5659447 : CollatzResearch.WordTrace tailWord_5659447 prefixEnd_5659447 2906016549646024121285183 := by
  unfold tailWord_5659447
  simp only [CollatzResearch.WordTrace]
  refine ⟨206416989927797550441208595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137611326618531700294139063 206416989927797550441208595)
  ·
    refine ⟨309625484891696325661812893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206416989927797550441208595 309625484891696325661812893)
    ·
      refine ⟨116109556834386122123179835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309625484891696325661812893 116109556834386122123179835)
      ·
        refine ⟨174164335251579183184769753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116109556834386122123179835 174164335251579183184769753)
        ·
          refine ⟨130623251438684387388577315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174164335251579183184769753 130623251438684387388577315)
          ·
            refine ⟨195934877158026581082865973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130623251438684387388577315 195934877158026581082865973)
            ·
              refine ⟨18368894733564991976518685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 195934877158026581082865973 18368894733564991976518685)
              ·
                refine ⟨6888335525086871991194507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18368894733564991976518685 6888335525086871991194507)
                ·
                  refine ⟨10332503287630307986791761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6888335525086871991194507 10332503287630307986791761)
                  ·
                    refine ⟨7749377465722730990093821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10332503287630307986791761 7749377465722730990093821)
                    ·
                      refine ⟨2906016549646024121285183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7749377465722730990093821 2906016549646024121285183)
                      ·
                        rfl

theorem cell23_5659447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 2, 3].length) (baseStart_5659447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659447 prefixEnd_5659447 := by exact prefixLift 5659447
  have htrace : WordTrace (prefixWord ++ tailWord_5659447) baseStart_5659447 baseEnd_5659447 := by
    simpa [prefixWord, tailWord_5659447, baseEnd_5659447] using wordTrace_append hprefix tailTrace_5659447
  have hstable : (prefixWord ++ tailWord_5659447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659447).length < 2 ^ (prefixWord ++ tailWord_5659447).sum := by decide
  have hdescent : baseEnd_5659447 < baseStart_5659447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659450 : List Nat := [3, 1, 1, 1, 6, 1, 10]
def baseStart_5659450 : Nat := 118140960795 + 5659450 * 2 ^ 59
def prefixEnd_5659450 : Nat := 4983230072969 + 3 ^ 40 * 5659450 * 2
def baseEnd_5659450 : Nat := 35876766544296143327749

theorem tailTrace_5659450 : CollatzResearch.WordTrace tailWord_5659450 prefixEnd_5659450 35876766544296143327749 := by
  unfold tailWord_5659450
  simp only [CollatzResearch.WordTrace]
  refine ⟨51604274836696670488391951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137611399564524454635711869 51604274836696670488391951)
  ·
    refine ⟨77406412255045005732587927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51604274836696670488391951 77406412255045005732587927)
    ·
      refine ⟨116109618382567508598881891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77406412255045005732587927 116109618382567508598881891)
      ·
        refine ⟨174164427573851262898322837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116109618382567508598881891 174164427573851262898322837)
        ·
          refine ⟨8163957542524277948358883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 174164427573851262898322837 8163957542524277948358883)
          ·
            refine ⟨12245936313786416922538325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8163957542524277948358883 12245936313786416922538325)
            ·
              refine ⟨35876766544296143327749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12245936313786416922538325 35876766544296143327749)
              ·
                rfl

theorem cell23_5659450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 10].length) (baseStart_5659450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659450 prefixEnd_5659450 := by exact prefixLift 5659450
  have htrace : WordTrace (prefixWord ++ tailWord_5659450) baseStart_5659450 baseEnd_5659450 := by
    simpa [prefixWord, tailWord_5659450, baseEnd_5659450] using wordTrace_append hprefix tailTrace_5659450
  have hstable : (prefixWord ++ tailWord_5659450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659450).length < 2 ^ (prefixWord ++ tailWord_5659450).sum := by decide
  have hdescent : baseEnd_5659450 < baseStart_5659450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659454 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_5659454 : Nat := 118140960795 + 5659454 * 2 ^ 59
def prefixEnd_5659454 : Nat := 4983230072969 + 3 ^ 40 * 5659454 * 2
def baseEnd_5659454 : Nat := 968673381336868531299217

theorem tailTrace_5659454 : CollatzResearch.WordTrace tailWord_5659454 prefixEnd_5659454 968673381336868531299217 := by
  unfold tailWord_5659454
  simp only [CollatzResearch.WordTrace]
  refine ⟨25802155654846523829589177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137611496825848127091142277 25802155654846523829589177)
  ·
    refine ⟨19351616741134892872191883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25802155654846523829589177 19351616741134892872191883)
    ·
      refine ⟨29027425111702339308287825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19351616741134892872191883 29027425111702339308287825)
      ·
        refine ⟨21770568833776754481215869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29027425111702339308287825 21770568833776754481215869)
        ·
          refine ⟨8163963312666282930455951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21770568833776754481215869 8163963312666282930455951)
          ·
            refine ⟨12245944968999424395683927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8163963312666282930455951 12245944968999424395683927)
            ·
              refine ⟨18368917453499136593525891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12245944968999424395683927 18368917453499136593525891)
              ·
                refine ⟨27553376180248704890288837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18368917453499136593525891 27553376180248704890288837)
                ·
                  refine ⟨5166258033796632166929157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27553376180248704890288837 5166258033796632166929157)
                  ·
                    refine ⟨968673381336868531299217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5166258033796632166929157 968673381336868531299217)
                    ·
                      rfl

theorem cell23_5659454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_5659454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659454 prefixEnd_5659454 := by exact prefixLift 5659454
  have htrace : WordTrace (prefixWord ++ tailWord_5659454) baseStart_5659454 baseEnd_5659454 := by
    simpa [prefixWord, tailWord_5659454, baseEnd_5659454] using wordTrace_append hprefix tailTrace_5659454
  have hstable : (prefixWord ++ tailWord_5659454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659454).length < 2 ^ (prefixWord ++ tailWord_5659454).sum := by decide
  have hdescent : baseEnd_5659454 < baseStart_5659454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659484 : List Nat := [2, 2, 4, 2, 1, 3, 2, 7]
def baseStart_5659484 : Nat := 118140960795 + 5659484 * 2 ^ 59
def prefixEnd_5659484 : Nat := 4983230072969 + 3 ^ 40 * 5659484 * 2
def baseEnd_5659484 : Nat := 107630946238157054686019

theorem tailTrace_5659484 : CollatzResearch.WordTrace tailWord_5659484 prefixEnd_5659484 107630946238157054686019 := by
  unfold tailWord_5659484
  simp only [CollatzResearch.WordTrace]
  refine ⟨103209169714331752880152753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137612226285775670506870337 103209169714331752880152753)
  ·
    refine ⟨77406877285748814660114565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103209169714331752880152753 77406877285748814660114565)
    ·
      refine ⟨14513789491077902748771481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77406877285748814660114565 14513789491077902748771481)
      ·
        refine ⟨10885342118308427061578611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14513789491077902748771481 10885342118308427061578611)
        ·
          refine ⟨16328013177462640592367917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10885342118308427061578611 16328013177462640592367917)
          ·
            refine ⟨6123004941548490222137969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16328013177462640592367917 6123004941548490222137969)
            ·
              refine ⟨4592253706161367666603477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6123004941548490222137969 4592253706161367666603477)
              ·
                refine ⟨107630946238157054686019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4592253706161367666603477 107630946238157054686019)
                ·
                  rfl

theorem cell23_5659484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 7].length) (baseStart_5659484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659484 prefixEnd_5659484 := by exact prefixLift 5659484
  have htrace : WordTrace (prefixWord ++ tailWord_5659484) baseStart_5659484 baseEnd_5659484 := by
    simpa [prefixWord, tailWord_5659484, baseEnd_5659484] using wordTrace_append hprefix tailTrace_5659484
  have hstable : (prefixWord ++ tailWord_5659484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659484).length < 2 ^ (prefixWord ++ tailWord_5659484).sum := by decide
  have hdescent : baseEnd_5659484 < baseStart_5659484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659504 : List Nat := [2, 1, 1, 1, 4, 1, 4, 3, 1, 3, 2]
def baseStart_5659504 : Nat := 118140960795 + 5659504 * 2 ^ 59
def prefixEnd_5659504 : Nat := 4983230072969 + 3 ^ 40 * 5659504 * 2
def baseEnd_5659504 : Nat := 2906045818043330398272421

theorem tailTrace_5659504 : CollatzResearch.WordTrace tailWord_5659504 prefixEnd_5659504 2906045818043330398272421 := by
  unfold tailWord_5659504
  simp only [CollatzResearch.WordTrace]
  refine ⟨103209534444295524588016783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137612712592394032784022377 103209534444295524588016783)
  ·
    refine ⟨154814301666443286882025175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103209534444295524588016783 154814301666443286882025175)
    ·
      refine ⟨232221452499664930323037763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154814301666443286882025175 232221452499664930323037763)
      ·
        refine ⟨348332178749497395484556645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232221452499664930323037763 348332178749497395484556645)
        ·
          refine ⟨65312283515530761653354371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 348332178749497395484556645 65312283515530761653354371)
          ·
            refine ⟨97968425273296142480031557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65312283515530761653354371 97968425273296142480031557)
            ·
              refine ⟨18369079738743026715005917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97968425273296142480031557 18369079738743026715005917)
              ·
                refine ⟨6888404902028635018127219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18369079738743026715005917 6888404902028635018127219)
                ·
                  refine ⟨10332607353042952527190829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6888404902028635018127219 10332607353042952527190829)
                  ·
                    refine ⟨3874727757391107197696561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10332607353042952527190829 3874727757391107197696561)
                    ·
                      refine ⟨2906045818043330398272421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3874727757391107197696561 2906045818043330398272421)
                      ·
                        rfl

theorem cell23_5659504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 1, 3, 2].length) (baseStart_5659504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659504 prefixEnd_5659504 := by exact prefixLift 5659504
  have htrace : WordTrace (prefixWord ++ tailWord_5659504) baseStart_5659504 baseEnd_5659504 := by
    simpa [prefixWord, tailWord_5659504, baseEnd_5659504] using wordTrace_append hprefix tailTrace_5659504
  have hstable : (prefixWord ++ tailWord_5659504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659504).length < 2 ^ (prefixWord ++ tailWord_5659504).sum := by decide
  have hdescent : baseEnd_5659504 < baseStart_5659504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659522 : List Nat := [3, 4, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_5659522 : Nat := 118140960795 + 5659522 * 2 ^ 59
def prefixEnd_5659522 : Nat := 4983230072969 + 3 ^ 40 * 5659522 * 2
def baseEnd_5659522 : Nat := 968685020231703775949113

theorem tailTrace_5659522 : CollatzResearch.WordTrace tailWord_5659522 prefixEnd_5659522 968685020231703775949113 := by
  unfold tailWord_5659522
  simp only [CollatzResearch.WordTrace]
  refine ⟨51604931350631459562547205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137613150268350558833459213 51604931350631459562547205)
  ·
    refine ⟨9675924628243398667977601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51604931350631459562547205 9675924628243398667977601)
    ·
      refine ⟨7256943471182549000983201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9675924628243398667977601 7256943471182549000983201)
      ·
        refine ⟨5442707603386911750737401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7256943471182549000983201 5442707603386911750737401)
        ·
          refine ⟨4082030702540183813053051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5442707603386911750737401 4082030702540183813053051)
          ·
            refine ⟨6123046053810275719579577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4082030702540183813053051 6123046053810275719579577)
            ·
              refine ⟨4592284540357706789684683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6123046053810275719579577 4592284540357706789684683)
              ·
                refine ⟨6888426810536560184527025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4592284540357706789684683 6888426810536560184527025)
                ·
                  refine ⟨5166320107902420138395269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6888426810536560184527025 5166320107902420138395269)
                  ·
                    refine ⟨968685020231703775949113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5166320107902420138395269 968685020231703775949113)
                    ·
                      rfl

theorem cell23_5659522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_5659522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659522 prefixEnd_5659522 := by exact prefixLift 5659522
  have htrace : WordTrace (prefixWord ++ tailWord_5659522) baseStart_5659522 baseEnd_5659522 := by
    simpa [prefixWord, tailWord_5659522, baseEnd_5659522] using wordTrace_append hprefix tailTrace_5659522
  have hstable : (prefixWord ++ tailWord_5659522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659522).length < 2 ^ (prefixWord ++ tailWord_5659522).sum := by decide
  have hdescent : baseEnd_5659522 < baseStart_5659522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659528 : List Nat := [2, 1, 3, 3, 2, 3, 2, 1, 2, 1, 3]
def baseStart_5659528 : Nat := 118140960795 + 5659528 * 2 ^ 59
def prefixEnd_5659528 : Nat := 4983230072969 + 3 ^ 40 * 5659528 * 2
def baseEnd_5659528 : Nat := 2906058141579038304372311

theorem tailTrace_5659528 : CollatzResearch.WordTrace tailWord_5659528 prefixEnd_5659528 2906058141579038304372311 := by
  unfold tailWord_5659528
  simp only [CollatzResearch.WordTrace]
  refine ⟨103209972120252050637453619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137613296160336067516604825 103209972120252050637453619)
  ·
    refine ⟨154814958180378075956180429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103209972120252050637453619 154814958180378075956180429)
    ·
      refine ⟨58055609317641778483567661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154814958180378075956180429 58055609317641778483567661)
      ·
        refine ⟨21770853494115666931337873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58055609317641778483567661 21770853494115666931337873)
        ·
          refine ⟨16328140120586750198503405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21770853494115666931337873 16328140120586750198503405)
          ·
            refine ⟨6123052545220031324438777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16328140120586750198503405 6123052545220031324438777)
            ·
              refine ⟨4592289408915023493329083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6123052545220031324438777 4592289408915023493329083)
              ·
                refine ⟨6888434113372535239993625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4592289408915023493329083 6888434113372535239993625)
                ·
                  refine ⟨5166325585029401429995219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6888434113372535239993625 5166325585029401429995219)
                  ·
                    refine ⟨7749488377544102144992829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5166325585029401429995219 7749488377544102144992829)
                    ·
                      refine ⟨2906058141579038304372311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7749488377544102144992829 2906058141579038304372311)
                      ·
                        rfl

theorem cell23_5659528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_5659528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659528 prefixEnd_5659528 := by exact prefixLift 5659528
  have htrace : WordTrace (prefixWord ++ tailWord_5659528) baseStart_5659528 baseEnd_5659528 := by
    simpa [prefixWord, tailWord_5659528, baseEnd_5659528] using wordTrace_append hprefix tailTrace_5659528
  have hstable : (prefixWord ++ tailWord_5659528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659528).length < 2 ^ (prefixWord ++ tailWord_5659528).sum := by decide
  have hdescent : baseEnd_5659528 < baseStart_5659528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659570 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 5, 7]
def baseStart_5659570 : Nat := 118140960795 + 5659570 * 2 ^ 59
def prefixEnd_5659570 : Nat := 4983230072969 + 3 ^ 40 * 5659570 * 2
def baseEnd_5659570 : Nat := 968693235922175713349039

theorem tailTrace_5659570 : CollatzResearch.WordTrace tailWord_5659570 prefixEnd_5659570 968693235922175713349039 := by
  unfold tailWord_5659570
  simp only [CollatzResearch.WordTrace]
  refine ⟨51605369026587985611984041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137614317404234628298624109 51605369026587985611984041)
  ·
    refine ⟨38704026769940989208988031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51605369026587985611984041 38704026769940989208988031)
    ·
      refine ⟨58056040154911483813482047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38704026769940989208988031 58056040154911483813482047)
      ·
        refine ⟨87084060232367225720223071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58056040154911483813482047 87084060232367225720223071)
        ·
          refine ⟨130626090348550838580334607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87084060232367225720223071 130626090348550838580334607)
          ·
            refine ⟨195939135522826257870501911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130626090348550838580334607 195939135522826257870501911)
            ·
              refine ⟨293908703284239386805752867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195939135522826257870501911 293908703284239386805752867)
              ·
                refine ⟨440863054926359080208629301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293908703284239386805752867 440863054926359080208629301)
                ·
                  refine ⟨41330911399346163769558997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 440863054926359080208629301 41330911399346163769558997)
                  ·
                    refine ⟨968693235922175713349039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41330911399346163769558997 968693235922175713349039)
                    ·
                      rfl

theorem cell23_5659570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_5659570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659570 prefixEnd_5659570 := by exact prefixLift 5659570
  have htrace : WordTrace (prefixWord ++ tailWord_5659570) baseStart_5659570 baseEnd_5659570 := by
    simpa [prefixWord, tailWord_5659570, baseEnd_5659570] using wordTrace_append hprefix tailTrace_5659570
  have hstable : (prefixWord ++ tailWord_5659570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659570).length < 2 ^ (prefixWord ++ tailWord_5659570).sum := by decide
  have hdescent : baseEnd_5659570 < baseStart_5659570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659604 : List Nat := [2, 4, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_5659604 : Nat := 118140960795 + 5659604 * 2 ^ 59
def prefixEnd_5659604 : Nat := 4983230072969 + 3 ^ 40 * 5659604 * 2
def baseEnd_5659604 : Nat := 968699055369593335673987

theorem tailTrace_5659604 : CollatzResearch.WordTrace tailWord_5659604 prefixEnd_5659604 968699055369593335673987 := by
  unfold tailWord_5659604
  simp only [CollatzResearch.WordTrace]
  refine ⟨103211358094114383127336933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137615144125485844169782577 103211358094114383127336933)
  ·
    refine ⟨19352129642646446836375675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103211358094114383127336933 19352129642646446836375675)
    ·
      refine ⟨29028194463969670254563513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19352129642646446836375675 29028194463969670254563513)
      ·
        refine ⟨21771145847977252690922635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29028194463969670254563513 21771145847977252690922635)
        ·
          refine ⟨32656718771965879036383953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21771145847977252690922635 32656718771965879036383953)
          ·
            refine ⟨24492539078974409277287965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32656718771965879036383953 24492539078974409277287965)
            ·
              refine ⟨9184702154615403478982987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24492539078974409277287965 9184702154615403478982987)
              ·
                refine ⟨13777053231923105218474481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9184702154615403478982987 13777053231923105218474481)
                ·
                  refine ⟨10332789923942328913855861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13777053231923105218474481 10332789923942328913855861)
                  ·
                    refine ⟨968699055369593335673987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10332789923942328913855861 968699055369593335673987)
                    ·
                      rfl

theorem cell23_5659604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_5659604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659604 prefixEnd_5659604 := by exact prefixLift 5659604
  have htrace : WordTrace (prefixWord ++ tailWord_5659604) baseStart_5659604 baseEnd_5659604 := by
    simpa [prefixWord, tailWord_5659604, baseEnd_5659604] using wordTrace_append hprefix tailTrace_5659604
  have hstable : (prefixWord ++ tailWord_5659604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659604).length < 2 ^ (prefixWord ++ tailWord_5659604).sum := by decide
  have hdescent : baseEnd_5659604 < baseStart_5659604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659607 : List Nat := [1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 4]
def baseStart_5659607 : Nat := 118140960795 + 5659607 * 2 ^ 59
def prefixEnd_5659607 : Nat := 4983230072969 + 3 ^ 40 * 5659607 * 2
def baseEnd_5659607 : Nat := 2906098706550743495284447

theorem tailTrace_5659607 : CollatzResearch.WordTrace tailWord_5659607 prefixEnd_5659607 2906098706550743495284447 := by
  unfold tailWord_5659607
  simp only [CollatzResearch.WordTrace]
  refine ⟨206422825607217897767033075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137615217071478598511355383 206422825607217897767033075)
  ·
    refine ⟨309634238410826846650549613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206422825607217897767033075 309634238410826846650549613)
    ·
      refine ⟨116112839404060067493956105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309634238410826846650549613 116112839404060067493956105)
      ·
        refine ⟨87084629553045050620467079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116112839404060067493956105 87084629553045050620467079)
        ·
          refine ⟨130626944329567575930700619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87084629553045050620467079 130626944329567575930700619)
          ·
            refine ⟨195940416494351363896050929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130626944329567575930700619 195940416494351363896050929)
            ·
              refine ⟨146955312370763522922038197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195940416494351363896050929 146955312370763522922038197)
              ·
                refine ⟨13777060534759080273941081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146955312370763522922038197 13777060534759080273941081)
                ·
                  refine ⟨10332795401069310205455811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13777060534759080273941081 10332795401069310205455811)
                  ·
                    refine ⟨15499193101603965308183717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10332795401069310205455811 15499193101603965308183717)
                    ·
                      refine ⟨2906098706550743495284447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15499193101603965308183717 2906098706550743495284447)
                      ·
                        rfl

theorem cell23_5659607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_5659607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659607 prefixEnd_5659607 := by exact prefixLift 5659607
  have htrace : WordTrace (prefixWord ++ tailWord_5659607) baseStart_5659607 baseEnd_5659607 := by
    simpa [prefixWord, tailWord_5659607, baseEnd_5659607] using wordTrace_append hprefix tailTrace_5659607
  have hstable : (prefixWord ++ tailWord_5659607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659607).length < 2 ^ (prefixWord ++ tailWord_5659607).sum := by decide
  have hdescent : baseEnd_5659607 < baseStart_5659607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659617 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 7, 4]
def baseStart_5659617 : Nat := 118140960795 + 5659617 * 2 ^ 59
def prefixEnd_5659617 : Nat := 4983230072969 + 3 ^ 40 * 5659617 * 2
def baseEnd_5659617 : Nat := 968701280452429485386467

theorem tailTrace_5659617 : CollatzResearch.WordTrace tailWord_5659617 prefixEnd_5659617 968701280452429485386467 := by
  unfold tailWord_5659617
  simp only [CollatzResearch.WordTrace]
  refine ⟨206423190337181669474897105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137615460224787779649931403 206423190337181669474897105)
  ·
    refine ⟨154817392752886252106172829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206423190337181669474897105 154817392752886252106172829)
    ·
      refine ⟨58056522282332344539814811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154817392752886252106172829 58056522282332344539814811)
      ·
        refine ⟨87084783423498516809722217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58056522282332344539814811 87084783423498516809722217)
        ·
          refine ⟨65313587567623887607291663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87084783423498516809722217 65313587567623887607291663)
          ·
            refine ⟨97970381351435831410937495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65313587567623887607291663 97970381351435831410937495)
            ·
              refine ⟨146955572027153747116406243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97970381351435831410937495 146955572027153747116406243)
              ·
                refine ⟨220433358040730620674609365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146955572027153747116406243 220433358040730620674609365)
                ·
                  refine ⟨5166406829079623922061157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 220433358040730620674609365 5166406829079623922061157)
                  ·
                    refine ⟨968701280452429485386467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5166406829079623922061157 968701280452429485386467)
                    ·
                      rfl

theorem cell23_5659617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_5659617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659617 prefixEnd_5659617 := by exact prefixLift 5659617
  have htrace : WordTrace (prefixWord ++ tailWord_5659617) baseStart_5659617 baseEnd_5659617 := by
    simpa [prefixWord, tailWord_5659617, baseEnd_5659617] using wordTrace_append hprefix tailTrace_5659617
  have hstable : (prefixWord ++ tailWord_5659617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659617).length < 2 ^ (prefixWord ++ tailWord_5659617).sum := by decide
  have hdescent : baseEnd_5659617 < baseStart_5659617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659624 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 2, 4, 2]
def baseStart_5659624 : Nat := 118140960795 + 5659624 * 2 ^ 59
def prefixEnd_5659624 : Nat := 4983230072969 + 3 ^ 40 * 5659624 * 2
def baseEnd_5659624 : Nat := 2906107435721869928771869

theorem tailTrace_5659624 : CollatzResearch.WordTrace tailWord_5659624 prefixEnd_5659624 2906107435721869928771869 := by
  unfold tailWord_5659624
  simp only [CollatzResearch.WordTrace]
  refine ⟨103211722824078154835200963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137615630432104206446934617 103211722824078154835200963)
  ·
    refine ⟨154817584236117232252801445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103211722824078154835200963 154817584236117232252801445)
    ·
      refine ⟨29028297044271981047400271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154817584236117232252801445 29028297044271981047400271)
      ·
        refine ⟨43542445566407971571100407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29028297044271981047400271 43542445566407971571100407)
        ·
          refine ⟨65313668349611957356650611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43542445566407971571100407 65313668349611957356650611)
          ·
            refine ⟨97970502524417936034975917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65313668349611957356650611 97970502524417936034975917)
            ·
              refine ⟨36738938446656726013115969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97970502524417936034975917 36738938446656726013115969)
              ·
                refine ⟨27554203834992544509836977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36738938446656726013115969 27554203834992544509836977)
                ·
                  refine ⟨20665652876244408382377733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27554203834992544509836977 20665652876244408382377733)
                  ·
                    refine ⟨3874809914295826571695825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20665652876244408382377733 3874809914295826571695825)
                    ·
                      refine ⟨2906107435721869928771869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3874809914295826571695825 2906107435721869928771869)
                      ·
                        rfl

theorem cell23_5659624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_5659624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659624 prefixEnd_5659624 := by exact prefixLift 5659624
  have htrace : WordTrace (prefixWord ++ tailWord_5659624) baseStart_5659624 baseEnd_5659624 := by
    simpa [prefixWord, tailWord_5659624, baseEnd_5659624] using wordTrace_append hprefix tailTrace_5659624
  have hstable : (prefixWord ++ tailWord_5659624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659624).length < 2 ^ (prefixWord ++ tailWord_5659624).sum := by decide
  have hdescent : baseEnd_5659624 < baseStart_5659624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659636 : List Nat := [2, 6, 2, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_5659636 : Nat := 118140960795 + 5659636 * 2 ^ 59
def prefixEnd_5659636 : Nat := 4983230072969 + 3 ^ 40 * 5659636 * 2
def baseEnd_5659636 : Nat := 2906113597489723881821815

theorem tailTrace_5659636 : CollatzResearch.WordTrace tailWord_5659636 prefixEnd_5659636 2906113597489723881821815 := by
  unfold tailWord_5659636
  simp only [CollatzResearch.WordTrace]
  refine ⟨103211941662056417859919381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137615922216075223813225841 103211941662056417859919381)
  ·
    refine ⟨4838059765408894587183721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 103211941662056417859919381 4838059765408894587183721)
    ·
      refine ⟨3628544824056670940387791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4838059765408894587183721 3628544824056670940387791)
      ·
        refine ⟨5442817236085006410581687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3628544824056670940387791 5442817236085006410581687)
        ·
          refine ⟨8164225854127509615872531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5442817236085006410581687 8164225854127509615872531)
          ·
            refine ⟨12246338781191264423808797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8164225854127509615872531 12246338781191264423808797)
            ·
              refine ⟨4592377042946724158928299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12246338781191264423808797 4592377042946724158928299)
              ·
                refine ⟨6888565564420086238392449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4592377042946724158928299 6888565564420086238392449)
                ·
                  refine ⟨5166424173315064678794337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6888565564420086238392449 5166424173315064678794337)
                  ·
                    refine ⟨3874818129986298509095753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5166424173315064678794337 3874818129986298509095753)
                    ·
                      refine ⟨2906113597489723881821815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3874818129986298509095753 2906113597489723881821815)
                      ·
                        rfl

theorem cell23_5659636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_5659636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659636 prefixEnd_5659636 := by exact prefixLift 5659636
  have htrace : WordTrace (prefixWord ++ tailWord_5659636) baseStart_5659636 baseEnd_5659636 := by
    simpa [prefixWord, tailWord_5659636, baseEnd_5659636] using wordTrace_append hprefix tailTrace_5659636
  have hstable : (prefixWord ++ tailWord_5659636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659636).length < 2 ^ (prefixWord ++ tailWord_5659636).sum := by decide
  have hdescent : baseEnd_5659636 < baseStart_5659636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659694 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 3, 5]
def baseStart_5659694 : Nat := 118140960795 + 5659694 * 2 ^ 59
def prefixEnd_5659694 : Nat := 4983230072969 + 3 ^ 40 * 5659694 * 2
def baseEnd_5659694 : Nat := 968714459789228218298849

theorem tailTrace_5659694 : CollatzResearch.WordTrace tailWord_5659694 prefixEnd_5659694 968714459789228218298849 := by
  unfold tailWord_5659694
  simp only [CollatzResearch.WordTrace]
  refine ⟨25803249844737838953181267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137617332505268474416966757 25803249844737838953181267)
  ·
    refine ⟨38704874767106758429771901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25803249844737838953181267 38704874767106758429771901)
    ·
      refine ⟨14514328037665034411164463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38704874767106758429771901 14514328037665034411164463)
      ·
        refine ⟨21771492056497551616746695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14514328037665034411164463 21771492056497551616746695)
        ·
          refine ⟨32657238084746327425120043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21771492056497551616746695 32657238084746327425120043)
          ·
            refine ⟨48985857127119491137680065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32657238084746327425120043 48985857127119491137680065)
            ·
              refine ⟨36739392845339618353260049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48985857127119491137680065 36739392845339618353260049)
              ·
                refine ⟨27554544634004713764945037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36739392845339618353260049 27554544634004713764945037)
                ·
                  refine ⟨10332954237751767661854389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27554544634004713764945037 10332954237751767661854389)
                  ·
                    refine ⟨968714459789228218298849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10332954237751767661854389 968714459789228218298849)
                    ·
                      rfl

theorem cell23_5659694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_5659694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659694 prefixEnd_5659694 := by exact prefixLift 5659694
  have htrace : WordTrace (prefixWord ++ tailWord_5659694) baseStart_5659694 baseEnd_5659694 := by
    simpa [prefixWord, tailWord_5659694, baseEnd_5659694] using wordTrace_append hprefix tailTrace_5659694
  have hstable : (prefixWord ++ tailWord_5659694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659694).length < 2 ^ (prefixWord ++ tailWord_5659694).sum := by decide
  have hdescent : baseEnd_5659694 < baseStart_5659694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659717 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 3, 1, 5]
def baseStart_5659717 : Nat := 118140960795 + 5659717 * 2 ^ 59
def prefixEnd_5659717 : Nat := 4983230072969 + 3 ^ 40 * 5659717 * 2
def baseEnd_5659717 : Nat := 2906155189422738064908941

theorem tailTrace_5659717 : CollatzResearch.WordTrace tailWord_5659717 prefixEnd_5659717 2906155189422738064908941 := by
  unfold tailWord_5659717
  simp only [CollatzResearch.WordTrace]
  refine ⟨206426837636819386553537405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137617891757879591035691603 206426837636819386553537405)
  ·
    refine ⟨77410064113807269957576527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206426837636819386553537405 77410064113807269957576527)
    ·
      refine ⟨116115096170710904936364791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77410064113807269957576527 116115096170710904936364791)
      ·
        refine ⟨174172644256066357404547187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116115096170710904936364791 174172644256066357404547187)
        ·
          refine ⟨261258966384099536106820781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174172644256066357404547187 261258966384099536106820781)
          ·
            refine ⟨97972112394037326040057793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261258966384099536106820781 97972112394037326040057793)
            ·
              refine ⟨73479084295527994530043345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97972112394037326040057793 73479084295527994530043345)
              ·
                refine ⟨55109313221645995897532509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73479084295527994530043345 55109313221645995897532509)
                ·
                  refine ⟨20665992458117248461574691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55109313221645995897532509 20665992458117248461574691)
                  ·
                    refine ⟨30998988687175872692362037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20665992458117248461574691 30998988687175872692362037)
                    ·
                      refine ⟨2906155189422738064908941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30998988687175872692362037 2906155189422738064908941)
                      ·
                        rfl

theorem cell23_5659717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_5659717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659717 prefixEnd_5659717 := by exact prefixLift 5659717
  have htrace : WordTrace (prefixWord ++ tailWord_5659717) baseStart_5659717 baseEnd_5659717 := by
    simpa [prefixWord, tailWord_5659717, baseEnd_5659717] using wordTrace_append hprefix tailTrace_5659717
  have hstable : (prefixWord ++ tailWord_5659717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659717).length < 2 ^ (prefixWord ++ tailWord_5659717).sum := by decide
  have hdescent : baseEnd_5659717 < baseStart_5659717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659754 : List Nat := [3, 1, 3, 2, 2, 1, 3, 8]
def baseStart_5659754 : Nat := 118140960795 + 5659754 * 2 ^ 59
def prefixEnd_5659754 : Nat := 4983230072969 + 3 ^ 40 * 5659754 * 2
def baseEnd_5659754 : Nat := 107636081044702015560973

theorem tailTrace_5659754 : CollatzResearch.WordTrace tailWord_5659754 prefixEnd_5659754 107636081044702015560973 := by
  unfold tailWord_5659754
  simp only [CollatzResearch.WordTrace]
  refine ⟨51607046784421335468158579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137618791425123561248422877 51607046784421335468158579)
  ·
    refine ⟨77410570176632003202237869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51607046784421335468158579 77410570176632003202237869)
    ·
      refine ⟨29028963816237001200839201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77410570176632003202237869 29028963816237001200839201)
      ·
        refine ⟨21771722862177750900629401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29028963816237001200839201 21771722862177750900629401)
        ·
          refine ⟨16328792146633313175472051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21771722862177750900629401 16328792146633313175472051)
          ·
            refine ⟨24493188219949969763208077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16328792146633313175472051 24493188219949969763208077)
            ·
              refine ⟨9184945582481238661203029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24493188219949969763208077 9184945582481238661203029)
              ·
                refine ⟨107636081044702015560973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9184945582481238661203029 107636081044702015560973)
                ·
                  rfl

theorem cell23_5659754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 8].length) (baseStart_5659754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659754 prefixEnd_5659754 := by exact prefixLift 5659754
  have htrace : WordTrace (prefixWord ++ tailWord_5659754) baseStart_5659754 baseEnd_5659754 := by
    simpa [prefixWord, tailWord_5659754, baseEnd_5659754] using wordTrace_append hprefix tailTrace_5659754
  have hstable : (prefixWord ++ tailWord_5659754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659754).length < 2 ^ (prefixWord ++ tailWord_5659754).sum := by decide
  have hdescent : baseEnd_5659754 < baseStart_5659754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659767 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 2, 7]
def baseStart_5659767 : Nat := 118140960795 + 5659767 * 2 ^ 59
def prefixEnd_5659767 : Nat := 4983230072969 + 3 ^ 40 * 5659767 * 2
def baseEnd_5659767 : Nat := 968726954485154289761237

theorem tailTrace_5659767 : CollatzResearch.WordTrace tailWord_5659767 prefixEnd_5659767 968726954485154289761237 := by
  unfold tailWord_5659767
  simp only [CollatzResearch.WordTrace]
  refine ⟨206428661286638245092857555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137619107524425496728571703 206428661286638245092857555)
  ·
    refine ⟨309642991929957367639286333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206428661286638245092857555 309642991929957367639286333)
    ·
      refine ⟨116116121973734012864732375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309642991929957367639286333 116116121973734012864732375)
      ·
        refine ⟨174174182960601019297098563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116116121973734012864732375 174174182960601019297098563)
        ·
          refine ⟨261261274440901528945647845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174174182960601019297098563 261261274440901528945647845)
          ·
            refine ⟨48986488957669036677308971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 261261274440901528945647845 48986488957669036677308971)
            ·
              refine ⟨73479733436503555015963457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48986488957669036677308971 73479733436503555015963457)
              ·
                refine ⟨55109800077377666261972593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73479733436503555015963457 55109800077377666261972593)
                ·
                  refine ⟨41332350058033249696479445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55109800077377666261972593 41332350058033249696479445)
                  ·
                    refine ⟨968726954485154289761237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41332350058033249696479445 968726954485154289761237)
                    ·
                      rfl

theorem cell23_5659767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_5659767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659767 prefixEnd_5659767 := by exact prefixLift 5659767
  have htrace : WordTrace (prefixWord ++ tailWord_5659767) baseStart_5659767 baseEnd_5659767 := by
    simpa [prefixWord, tailWord_5659767, baseEnd_5659767] using wordTrace_append hprefix tailTrace_5659767
  have hstable : (prefixWord ++ tailWord_5659767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659767).length < 2 ^ (prefixWord ++ tailWord_5659767).sum := by decide
  have hdescent : baseEnd_5659767 < baseStart_5659767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659817 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 4, 3, 6]
def baseStart_5659817 : Nat := 118140960795 + 5659817 * 2 ^ 59
def prefixEnd_5659817 : Nat := 4983230072969 + 3 ^ 40 * 5659817 * 2
def baseEnd_5659817 : Nat := 2906206537488187673658481

theorem tailTrace_5659817 : CollatzResearch.WordTrace tailWord_5659817 prefixEnd_5659817 2906206537488187673658481 := by
  unfold tailWord_5659817
  simp only [CollatzResearch.WordTrace]
  refine ⟨206430484936457103632177705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137620323290971402421451803 206430484936457103632177705)
  ·
    refine ⟨154822863702342827724133279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206430484936457103632177705 154822863702342827724133279)
    ·
      refine ⟨232234295553514241586199919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154822863702342827724133279 232234295553514241586199919)
      ·
        refine ⟨348351443330271362379299879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232234295553514241586199919 348351443330271362379299879)
        ·
          refine ⟨522527164995407043568949819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348351443330271362379299879 522527164995407043568949819)
          ·
            refine ⟨783790747493110565353424729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522527164995407043568949819 783790747493110565353424729)
            ·
              refine ⟨587843060619832924015068547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 783790747493110565353424729 587843060619832924015068547)
              ·
                refine ⟨881764590929749386022602821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587843060619832924015068547 881764590929749386022602821)
                ·
                  refine ⟨165330860799328009879238029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 881764590929749386022602821 165330860799328009879238029)
                  ·
                    refine ⟨61999072799748003704714261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165330860799328009879238029 61999072799748003704714261)
                    ·
                      refine ⟨2906206537488187673658481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61999072799748003704714261 2906206537488187673658481)
                      ·
                        rfl

theorem cell23_5659817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_5659817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659817 prefixEnd_5659817 := by exact prefixLift 5659817
  have htrace : WordTrace (prefixWord ++ tailWord_5659817) baseStart_5659817 baseEnd_5659817 := by
    simpa [prefixWord, tailWord_5659817, baseEnd_5659817] using wordTrace_append hprefix tailTrace_5659817
  have hstable : (prefixWord ++ tailWord_5659817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659817).length < 2 ^ (prefixWord ++ tailWord_5659817).sum := by decide
  have hdescent : baseEnd_5659817 < baseStart_5659817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659825 : List Nat := [1, 2, 2, 5, 1, 2, 2, 2, 1, 3, 2]
def baseStart_5659825 : Nat := 118140960795 + 5659825 * 2 ^ 59
def prefixEnd_5659825 : Nat := 4983230072969 + 3 ^ 40 * 5659825 * 2
def baseEnd_5659825 : Nat := 2906210645333423642358445

theorem tailTrace_5659825 : CollatzResearch.WordTrace tailWord_5659825 prefixEnd_5659825 2906210645333423642358445 := by
  unfold tailWord_5659825
  simp only [CollatzResearch.WordTrace]
  refine ⟨206430776720428120998468929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137620517813618747332312619 206430776720428120998468929)
  ·
    refine ⟨154823082540321090748851697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206430776720428120998468929 154823082540321090748851697)
    ·
      refine ⟨116117311905240818061638773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154823082540321090748851697 116117311905240818061638773)
      ·
        refine ⟨10885997991116326693278635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116117311905240818061638773 10885997991116326693278635)
        ·
          refine ⟨16328996986674490039917953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10885997991116326693278635 16328996986674490039917953)
          ·
            refine ⟨12246747740005867529938465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16328996986674490039917953 12246747740005867529938465)
            ·
              refine ⟨9185060805004400647453849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12246747740005867529938465 9185060805004400647453849)
              ·
                refine ⟨6888795603753300485590387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9185060805004400647453849 6888795603753300485590387)
                ·
                  refine ⟨10333193405629950728385581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6888795603753300485590387 10333193405629950728385581)
                  ·
                    refine ⟨3874947527111231523144593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10333193405629950728385581 3874947527111231523144593)
                    ·
                      refine ⟨2906210645333423642358445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3874947527111231523144593 2906210645333423642358445)
                      ·
                        rfl

theorem cell23_5659825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_5659825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659825 prefixEnd_5659825 := by exact prefixLift 5659825
  have htrace : WordTrace (prefixWord ++ tailWord_5659825) baseStart_5659825 baseEnd_5659825 := by
    simpa [prefixWord, tailWord_5659825, baseEnd_5659825] using wordTrace_append hprefix tailTrace_5659825
  have hstable : (prefixWord ++ tailWord_5659825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659825).length < 2 ^ (prefixWord ++ tailWord_5659825).sum := by decide
  have hdescent : baseEnd_5659825 < baseStart_5659825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659841 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_5659841 : Nat := 118140960795 + 5659841 * 2 ^ 59
def prefixEnd_5659841 : Nat := 4983230072969 + 3 ^ 40 * 5659841 * 2
def baseEnd_5659841 : Nat := 2906218861023895579758371

theorem tailTrace_5659841 : CollatzResearch.WordTrace tailWord_5659841 prefixEnd_5659841 2906218861023895579758371 := by
  unfold tailWord_5659841
  simp only [CollatzResearch.WordTrace]
  refine ⟨206431360288370155731051377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137620906858913437154034251 206431360288370155731051377)
  ·
    refine ⟨154823520216277616798288533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206431360288370155731051377 154823520216277616798288533)
    ·
      refine ⟨7257352510138013287419775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 154823520216277616798288533 7257352510138013287419775)
      ·
        refine ⟨10886028765207019931129663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7257352510138013287419775 10886028765207019931129663)
        ·
          refine ⟨16329043147810529896694495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10886028765207019931129663 16329043147810529896694495)
          ·
            refine ⟨24493564721715794845041743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16329043147810529896694495 24493564721715794845041743)
            ·
              refine ⟨36740347082573692267562615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24493564721715794845041743 36740347082573692267562615)
              ·
                refine ⟨55110520623860538401343923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36740347082573692267562615 55110520623860538401343923)
                ·
                  refine ⟨82665780935790807602015885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55110520623860538401343923 82665780935790807602015885)
                  ·
                    refine ⟨30999667850921552850755957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82665780935790807602015885 30999667850921552850755957)
                    ·
                      refine ⟨2906218861023895579758371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30999667850921552850755957 2906218861023895579758371)
                      ·
                        rfl

theorem cell23_5659841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_5659841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659841 prefixEnd_5659841 := by exact prefixLift 5659841
  have htrace : WordTrace (prefixWord ++ tailWord_5659841) baseStart_5659841 baseEnd_5659841 := by
    simpa [prefixWord, tailWord_5659841, baseEnd_5659841] using wordTrace_append hprefix tailTrace_5659841
  have hstable : (prefixWord ++ tailWord_5659841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659841).length < 2 ^ (prefixWord ++ tailWord_5659841).sum := by decide
  have hdescent : baseEnd_5659841 < baseStart_5659841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659861 : List Nat := [1, 3, 2, 4, 1, 1, 3, 1, 7]
def baseStart_5659861 : Nat := 118140960795 + 5659861 * 2 ^ 59
def prefixEnd_5659861 : Nat := 4983230072969 + 3 ^ 40 * 5659861 * 2
def baseEnd_5659861 : Nat := 322914347848553944612031

theorem tailTrace_5659861 : CollatzResearch.WordTrace tailWord_5659861 prefixEnd_5659861 322914347848553944612031 := by
  unfold tailWord_5659861
  simp only [CollatzResearch.WordTrace]
  refine ⟨206432089748297699146779437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137621393165531799431186291 206432089748297699146779437)
  ·
    refine ⟨77412033655611637180042289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206432089748297699146779437 77412033655611637180042289)
    ·
      refine ⟨58059025241708727885031717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77412033655611637180042289 58059025241708727885031717)
      ·
        refine ⟨10886067232820386478443447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58059025241708727885031717 10886067232820386478443447)
        ·
          refine ⟨16329100849230579717665171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10886067232820386478443447 16329100849230579717665171)
          ·
            refine ⟨24493651273845869576497757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16329100849230579717665171 24493651273845869576497757)
            ·
              refine ⟨9185119227692201091186659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24493651273845869576497757 9185119227692201091186659)
              ·
                refine ⟨13777678841538301636779989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9185119227692201091186659 13777678841538301636779989)
                ·
                  refine ⟨322914347848553944612031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13777678841538301636779989 322914347848553944612031)
                  ·
                    rfl

theorem cell23_5659861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 7].length) (baseStart_5659861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659861 prefixEnd_5659861 := by exact prefixLift 5659861
  have htrace : WordTrace (prefixWord ++ tailWord_5659861) baseStart_5659861 baseEnd_5659861 := by
    simpa [prefixWord, tailWord_5659861, baseEnd_5659861] using wordTrace_append hprefix tailTrace_5659861
  have hstable : (prefixWord ++ tailWord_5659861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659861).length < 2 ^ (prefixWord ++ tailWord_5659861).sum := by decide
  have hdescent : baseEnd_5659861 < baseStart_5659861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659872 : List Nat := [2, 1, 1, 3, 1, 6, 2, 1, 2, 2, 2]
def baseStart_5659872 : Nat := 118140960795 + 5659872 * 2 ^ 59
def prefixEnd_5659872 : Nat := 4983230072969 + 3 ^ 40 * 5659872 * 2
def baseEnd_5659872 : Nat := 2906234778924184958470729

theorem tailTrace_5659872 : CollatzResearch.WordTrace tailWord_5659872 prefixEnd_5659872 2906234778924184958470729 := by
  unfold tailWord_5659872
  simp only [CollatzResearch.WordTrace]
  refine ⟨103216245475628924012714935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137621660634171898683619913 103216245475628924012714935)
  ·
    refine ⟨154824368213443386019072403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103216245475628924012714935 154824368213443386019072403)
    ·
      refine ⟨232236552320165079028608605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154824368213443386019072403 232236552320165079028608605)
      ·
        refine ⟨87088707120061904635728227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232236552320165079028608605 87088707120061904635728227)
        ·
          refine ⟨130633060680092856953592341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87088707120061904635728227 130633060680092856953592341)
          ·
            refine ⟨6123424719379352669699641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 130633060680092856953592341 6123424719379352669699641)
            ·
              refine ⟨4592568539534514502274731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6123424719379352669699641 4592568539534514502274731)
              ·
                refine ⟨6888852809301771753412097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4592568539534514502274731 6888852809301771753412097)
                ·
                  refine ⟨5166639606976328815059073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6888852809301771753412097 5166639606976328815059073)
                  ·
                    refine ⟨3874979705232246611294305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5166639606976328815059073 3874979705232246611294305)
                    ·
                      refine ⟨2906234778924184958470729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3874979705232246611294305 2906234778924184958470729)
                      ·
                        rfl

theorem cell23_5659872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_5659872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659872 prefixEnd_5659872 := by exact prefixLift 5659872
  have htrace : WordTrace (prefixWord ++ tailWord_5659872) baseStart_5659872 baseEnd_5659872 := by
    simpa [prefixWord, tailWord_5659872, baseEnd_5659872] using wordTrace_append hprefix tailTrace_5659872
  have hstable : (prefixWord ++ tailWord_5659872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659872).length < 2 ^ (prefixWord ++ tailWord_5659872).sum := by decide
  have hdescent : baseEnd_5659872 < baseStart_5659872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659891 : List Nat := [1, 1, 1, 2, 2, 6, 2, 1, 2, 5]
def baseStart_5659891 : Nat := 118140960795 + 5659891 * 2 ^ 59
def prefixEnd_5659891 : Nat := 4983230072969 + 3 ^ 40 * 5659891 * 2
def baseEnd_5659891 : Nat := 968748178352206794711047

theorem tailTrace_5659891 : CollatzResearch.WordTrace tailWord_5659891 prefixEnd_5659891 968748178352206794711047 := by
  unfold tailWord_5659891
  simp only [CollatzResearch.WordTrace]
  refine ⟨206433183938189014270371527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137622122625459342846914351 206433183938189014270371527)
  ·
    refine ⟨309649775907283521405557291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206433183938189014270371527 309649775907283521405557291)
    ·
      refine ⟨464474663860925282108335937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309649775907283521405557291 464474663860925282108335937)
      ·
        refine ⟨348355997895693961581251953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 464474663860925282108335937 348355997895693961581251953)
        ·
          refine ⟨261266998421770471185938965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348355997895693961581251953 261266998421770471185938965)
          ·
            refine ⟨12246890551020490836840889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 261266998421770471185938965 12246890551020490836840889)
            ·
              refine ⟨9185167913265368127630667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12246890551020490836840889 9185167913265368127630667)
              ·
                refine ⟨13777751869898052191446001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9185167913265368127630667 13777751869898052191446001)
                ·
                  refine ⟨10333313902423539143584501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13777751869898052191446001 10333313902423539143584501)
                  ·
                    refine ⟨968748178352206794711047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10333313902423539143584501 968748178352206794711047)
                    ·
                      rfl

theorem cell23_5659891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 5].length) (baseStart_5659891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659891 prefixEnd_5659891 := by exact prefixLift 5659891
  have htrace : WordTrace (prefixWord ++ tailWord_5659891) baseStart_5659891 baseEnd_5659891 := by
    simpa [prefixWord, tailWord_5659891, baseEnd_5659891] using wordTrace_append hprefix tailTrace_5659891
  have hstable : (prefixWord ++ tailWord_5659891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659891).length < 2 ^ (prefixWord ++ tailWord_5659891).sum := by decide
  have hdescent : baseEnd_5659891 < baseStart_5659891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659912 : List Nat := [2, 1, 3, 2, 5, 1, 2, 2, 5]
def baseStart_5659912 : Nat := 118140960795 + 5659912 * 2 ^ 59
def prefixEnd_5659912 : Nat := 4983230072969 + 3 ^ 40 * 5659912 * 2
def baseEnd_5659912 : Nat := 322917257572262755774505

theorem tailTrace_5659912 : CollatzResearch.WordTrace tailWord_5659912 prefixEnd_5659912 322917257572262755774505 := by
  unfold tailWord_5659912
  simp only [CollatzResearch.WordTrace]
  refine ⟨103216974935556467428442995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137622633247408623237923993 103216974935556467428442995)
  ·
    refine ⟨154825462403334701142664493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103216974935556467428442995 154825462403334701142664493)
    ·
      refine ⟨58059548401250512928499185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154825462403334701142664493 58059548401250512928499185)
      ·
        refine ⟨43544661300937884696374389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58059548401250512928499185 43544661300937884696374389)
        ·
          refine ⟨4082311996962926690285099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43544661300937884696374389 4082311996962926690285099)
          ·
            refine ⟨6123467995444390035427649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4082311996962926690285099 6123467995444390035427649)
            ·
              refine ⟨4592600996583292526570737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6123467995444390035427649 4592600996583292526570737)
              ·
                refine ⟨3444450747437469394928053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4592600996583292526570737 3444450747437469394928053)
                ·
                  refine ⟨322917257572262755774505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3444450747437469394928053 322917257572262755774505)
                  ·
                    rfl

theorem cell23_5659912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 5].length) (baseStart_5659912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659912 prefixEnd_5659912 := by exact prefixLift 5659912
  have htrace : WordTrace (prefixWord ++ tailWord_5659912) baseStart_5659912 baseEnd_5659912 := by
    simpa [prefixWord, tailWord_5659912, baseEnd_5659912] using wordTrace_append hprefix tailTrace_5659912
  have hstable : (prefixWord ++ tailWord_5659912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659912).length < 2 ^ (prefixWord ++ tailWord_5659912).sum := by decide
  have hdescent : baseEnd_5659912 < baseStart_5659912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659914 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_5659914 : Nat := 118140960795 + 5659914 * 2 ^ 59
def prefixEnd_5659914 : Nat := 4983230072969 + 3 ^ 40 * 5659914 * 2
def baseEnd_5659914 : Nat := 2906256345111673794145535

theorem tailTrace_5659914 : CollatzResearch.WordTrace tailWord_5659914 prefixEnd_5659914 2906256345111673794145535 := by
  unfold tailWord_5659914
  simp only [CollatzResearch.WordTrace]
  refine ⟨51608505704276422299614699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137622681878070459465639197 51608505704276422299614699)
  ·
    refine ⟨77412758556414633449422049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51608505704276422299614699 77412758556414633449422049)
    ·
      refine ⟨58059568917310975087066537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77412758556414633449422049 58059568917310975087066537)
      ·
        refine ⟨43544676687983231315299903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58059568917310975087066537 43544676687983231315299903)
        ·
          refine ⟨65317015031974846972949855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43544676687983231315299903 65317015031974846972949855)
          ·
            refine ⟨97975522547962270459424783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65317015031974846972949855 97975522547962270459424783)
            ·
              refine ⟨146963283821943405689137175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97975522547962270459424783 146963283821943405689137175)
              ·
                refine ⟨220444925732915108533705763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146963283821943405689137175 220444925732915108533705763)
                ·
                  refine ⟨330667388599372662800558645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220444925732915108533705763 330667388599372662800558645)
                  ·
                    refine ⟨31000067681191187137552373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 330667388599372662800558645 31000067681191187137552373)
                    ·
                      refine ⟨2906256345111673794145535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31000067681191187137552373 2906256345111673794145535)
                      ·
                        rfl

theorem cell23_5659914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_5659914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659914 prefixEnd_5659914 := by exact prefixLift 5659914
  have htrace : WordTrace (prefixWord ++ tailWord_5659914) baseStart_5659914 baseEnd_5659914 := by
    simpa [prefixWord, tailWord_5659914, baseEnd_5659914] using wordTrace_append hprefix tailTrace_5659914
  have hstable : (prefixWord ++ tailWord_5659914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659914).length < 2 ^ (prefixWord ++ tailWord_5659914).sum := by decide
  have hdescent : baseEnd_5659914 < baseStart_5659914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659921 : List Nat := [1, 2, 2, 1, 1, 4, 2, 3, 3, 4]
def baseStart_5659921 : Nat := 118140960795 + 5659921 * 2 ^ 59
def prefixEnd_5659921 : Nat := 4983230072969 + 3 ^ 40 * 5659921 * 2
def baseEnd_5659921 : Nat := 968753313158751755586001

theorem tailTrace_5659921 : CollatzResearch.WordTrace tailWord_5659921 prefixEnd_5659921 968753313158751755586001 := by
  unfold tailWord_5659921
  simp only [CollatzResearch.WordTrace]
  refine ⟨206434278128080329393963617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137622852085386886262642411 206434278128080329393963617)
  ·
    refine ⟨154825708596060247045472713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206434278128080329393963617 154825708596060247045472713)
    ·
      refine ⟨116119281447045185284104535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154825708596060247045472713 116119281447045185284104535)
      ·
        refine ⟨174178922170567777926156803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116119281447045185284104535 174178922170567777926156803)
        ·
          refine ⟨261268383255851666889235205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174178922170567777926156803 261268383255851666889235205)
          ·
            refine ⟨48987821860472187541731601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 261268383255851666889235205 48987821860472187541731601)
            ·
              refine ⟨36740866395354140656298701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48987821860472187541731601 36740866395354140656298701)
              ·
                refine ⟨13777824898257802746112013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36740866395354140656298701 13777824898257802746112013)
                ·
                  refine ⟨5166684336846676029792005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13777824898257802746112013 5166684336846676029792005)
                  ·
                    refine ⟨968753313158751755586001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5166684336846676029792005 968753313158751755586001)
                    ·
                      rfl

theorem cell23_5659921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_5659921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659921 prefixEnd_5659921 := by exact prefixLift 5659921
  have htrace : WordTrace (prefixWord ++ tailWord_5659921) baseStart_5659921 baseEnd_5659921 := by
    simpa [prefixWord, tailWord_5659921, baseEnd_5659921] using wordTrace_append hprefix tailTrace_5659921
  have hstable : (prefixWord ++ tailWord_5659921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659921).length < 2 ^ (prefixWord ++ tailWord_5659921).sum := by decide
  have hdescent : baseEnd_5659921 < baseStart_5659921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659928 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 2, 4, 2]
def baseStart_5659928 : Nat := 118140960795 + 5659928 * 2 ^ 59
def prefixEnd_5659928 : Nat := 4983230072969 + 3 ^ 40 * 5659928 * 2
def baseEnd_5659928 : Nat := 2906263533840836739370471

theorem tailTrace_5659928 : CollatzResearch.WordTrace tailWord_5659928 prefixEnd_5659928 2906263533840836739370471 := by
  unfold tailWord_5659928
  simp only [CollatzResearch.WordTrace]
  refine ⟨103217266719527484794734219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137623022292703313059645625 103217266719527484794734219)
  ·
    refine ⟨154825900079291227192101329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103217266719527484794734219 154825900079291227192101329)
    ·
      refine ⟨116119425059468420394075997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154825900079291227192101329 116119425059468420394075997)
      ·
        refine ⟨43544784397300657647778499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116119425059468420394075997 43544784397300657647778499)
        ·
          refine ⟨65317176595950986471667749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43544784397300657647778499 65317176595950986471667749)
          ·
            refine ⟨12246970611740809963437703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65317176595950986471667749 12246970611740809963437703)
            ·
              refine ⟨18370455917611214945156555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12246970611740809963437703 18370455917611214945156555)
              ·
                refine ⟨27555683876416822417734833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18370455917611214945156555 27555683876416822417734833)
                ·
                  refine ⟨20666762907312616813301125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27555683876416822417734833 20666762907312616813301125)
                  ·
                    refine ⟨3875018045121115652493961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20666762907312616813301125 3875018045121115652493961)
                    ·
                      refine ⟨2906263533840836739370471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3875018045121115652493961 2906263533840836739370471)
                      ·
                        rfl

theorem cell23_5659928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_5659928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659928 prefixEnd_5659928 := by exact prefixLift 5659928
  have htrace : WordTrace (prefixWord ++ tailWord_5659928) baseStart_5659928 baseEnd_5659928 := by
    simpa [prefixWord, tailWord_5659928, baseEnd_5659928] using wordTrace_append hprefix tailTrace_5659928
  have hstable : (prefixWord ++ tailWord_5659928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659928).length < 2 ^ (prefixWord ++ tailWord_5659928).sum := by decide
  have hdescent : baseEnd_5659928 < baseStart_5659928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659955 : List Nat := [1, 1, 1, 2, 5, 3, 2, 3, 1, 4]
def baseStart_5659955 : Nat := 118140960795 + 5659955 * 2 ^ 59
def prefixEnd_5659955 : Nat := 4983230072969 + 3 ^ 40 * 5659955 * 2
def baseEnd_5659955 : Nat := 968759132606169377910949

theorem tailTrace_5659955 : CollatzResearch.WordTrace tailWord_5659955 prefixEnd_5659955 968759132606169377910949 := by
  unfold tailWord_5659955
  simp only [CollatzResearch.WordTrace]
  refine ⟨206435518209957153200701319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137623678806638102133800879 206435518209957153200701319)
  ·
    refine ⟨309653277314935729801051979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206435518209957153200701319 309653277314935729801051979)
    ·
      refine ⟨464479915972403594701577969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309653277314935729801051979 464479915972403594701577969)
      ·
        refine ⟨348359936979302696026183477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 464479915972403594701577969 348359936979302696026183477)
        ·
          refine ⟨32658744091809627752454701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 348359936979302696026183477 32658744091809627752454701)
          ·
            refine ⟨12247029034428610407170513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32658744091809627752454701 12247029034428610407170513)
            ·
              refine ⟨9185271775821457805377885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12247029034428610407170513 9185271775821457805377885)
              ·
                refine ⟨3444476915933046677016707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9185271775821457805377885 3444476915933046677016707)
                ·
                  refine ⟨5166715373899570015525061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3444476915933046677016707 5166715373899570015525061)
                  ·
                    refine ⟨968759132606169377910949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5166715373899570015525061 968759132606169377910949)
                    ·
                      rfl

theorem cell23_5659955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 1, 4].length) (baseStart_5659955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659955 prefixEnd_5659955 := by exact prefixLift 5659955
  have htrace : WordTrace (prefixWord ++ tailWord_5659955) baseStart_5659955 baseEnd_5659955 := by
    simpa [prefixWord, tailWord_5659955, baseEnd_5659955] using wordTrace_append hprefix tailTrace_5659955
  have hstable : (prefixWord ++ tailWord_5659955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659955).length < 2 ^ (prefixWord ++ tailWord_5659955).sum := by decide
  have hdescent : baseEnd_5659955 < baseStart_5659955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659972 : List Nat := [2, 3, 4, 1, 1, 1, 2, 4, 1, 4]
def baseStart_5659972 : Nat := 118140960795 + 5659972 * 2 ^ 59
def prefixEnd_5659972 : Nat := 4983230072969 + 3 ^ 40 * 5659972 * 2
def baseEnd_5659972 : Nat := 968762042329878189073423

theorem tailTrace_5659972 : CollatzResearch.WordTrace tailWord_5659972 prefixEnd_5659972 968762042329878189073423 := by
  unfold tailWord_5659972
  simp only [CollatzResearch.WordTrace]
  refine ⟨103218069125447782552035085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137624092167263710069380113 103218069125447782552035085)
  ·
    refine ⟨38706775922042918457013157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103218069125447782552035085 38706775922042918457013157)
    ·
      refine ⟨7257520485383047210689967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38706775922042918457013157 7257520485383047210689967)
      ·
        refine ⟨10886280728074570816034951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7257520485383047210689967 10886280728074570816034951)
        ·
          refine ⟨16329421092111856224052427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10886280728074570816034951 16329421092111856224052427)
          ·
            refine ⟨24494131638167784336078641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16329421092111856224052427 24494131638167784336078641)
            ·
              refine ⟨18370598728625838252058981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24494131638167784336078641 18370598728625838252058981)
              ·
                refine ⟨3444487261617344672261059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18370598728625838252058981 3444487261617344672261059)
                ·
                  refine ⟨5166730892426017008391589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3444487261617344672261059 5166730892426017008391589)
                  ·
                    refine ⟨968762042329878189073423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5166730892426017008391589 968762042329878189073423)
                    ·
                      rfl

theorem cell23_5659972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_5659972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659972 prefixEnd_5659972 := by exact prefixLift 5659972
  have htrace : WordTrace (prefixWord ++ tailWord_5659972) baseStart_5659972 baseEnd_5659972 := by
    simpa [prefixWord, tailWord_5659972, baseEnd_5659972] using wordTrace_append hprefix tailTrace_5659972
  have hstable : (prefixWord ++ tailWord_5659972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659972).length < 2 ^ (prefixWord ++ tailWord_5659972).sum := by decide
  have hdescent : baseEnd_5659972 < baseStart_5659972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5659988 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 3, 5, 2]
def baseStart_5659988 : Nat := 118140960795 + 5659988 * 2 ^ 59
def prefixEnd_5659988 : Nat := 4983230072969 + 3 ^ 40 * 5659988 * 2
def baseEnd_5659988 : Nat := 2906294342680106504620195

theorem tailTrace_5659988 : CollatzResearch.WordTrace tailWord_5659988 prefixEnd_5659988 2906294342680106504620195 := by
  unfold tailWord_5659988
  simp only [CollatzResearch.WordTrace]
  refine ⟨103218360909418799918326309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137624481212558399891101745 103218360909418799918326309)
  ·
    refine ⟨19353442670516024984686183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103218360909418799918326309 19353442670516024984686183)
    ·
      refine ⟨29030164005774037477029275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19353442670516024984686183 29030164005774037477029275)
      ·
        refine ⟨43545246008661056215543913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29030164005774037477029275 43545246008661056215543913)
        ·
          refine ⟨32658934506495792161657935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43545246008661056215543913 32658934506495792161657935)
          ·
            refine ⟨48988401759743688242486903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32658934506495792161657935 48988401759743688242486903)
            ·
              refine ⟨73482602639615532363730355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48988401759743688242486903 73482602639615532363730355)
              ·
                refine ⟨110223903959423298545595533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73482602639615532363730355 110223903959423298545595533)
                ·
                  refine ⟨41333963984783736954598325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110223903959423298545595533 41333963984783736954598325)
                  ·
                    refine ⟨3875059123573475339493593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41333963984783736954598325 3875059123573475339493593)
                    ·
                      refine ⟨2906294342680106504620195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3875059123573475339493593 2906294342680106504620195)
                      ·
                        rfl

theorem cell23_5659988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_5659988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5659988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5659988 prefixEnd_5659988 := by exact prefixLift 5659988
  have htrace : WordTrace (prefixWord ++ tailWord_5659988) baseStart_5659988 baseEnd_5659988 := by
    simpa [prefixWord, tailWord_5659988, baseEnd_5659988] using wordTrace_append hprefix tailTrace_5659988
  have hstable : (prefixWord ++ tailWord_5659988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5659988).length < 2 ^ (prefixWord ++ tailWord_5659988).sum := by decide
  have hdescent : baseEnd_5659988 < baseStart_5659988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5659988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660001 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_5660001 : Nat := 118140960795 + 5660001 * 2 ^ 59
def prefixEnd_5660001 : Nat := 4983230072969 + 3 ^ 40 * 5660001 * 2
def baseEnd_5660001 : Nat := 2906301017928614953757635

theorem tailTrace_5660001 : CollatzResearch.WordTrace tailWord_5660001 prefixEnd_5660001 2906301017928614953757635 := by
  unfold tailWord_5660001
  simp only [CollatzResearch.WordTrace]
  refine ⟨206437195967790503056875857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137624797311860335371250571 206437195967790503056875857)
  ·
    refine ⟨154827896975842877292656893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206437195967790503056875857 154827896975842877292656893)
    ·
      refine ⟨58060461365941078984746335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154827896975842877292656893 58060461365941078984746335)
      ·
        refine ⟨87090692048911618477119503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58060461365941078984746335 87090692048911618477119503)
        ·
          refine ⟨130636038073367427715679255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87090692048911618477119503 130636038073367427715679255)
          ·
            refine ⟨195954057110051141573518883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130636038073367427715679255 195954057110051141573518883)
            ·
              refine ⟨293931085665076712360278325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195954057110051141573518883 293931085665076712360278325)
              ·
                refine ⟨27556039281100941783776093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 293931085665076712360278325 27556039281100941783776093)
                ·
                  refine ⟨10333514730412853168916035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27556039281100941783776093 10333514730412853168916035)
                  ·
                    refine ⟨15500272095619279753374053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10333514730412853168916035 15500272095619279753374053)
                    ·
                      refine ⟨2906301017928614953757635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15500272095619279753374053 2906301017928614953757635)
                      ·
                        rfl

theorem cell23_5660001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_5660001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660001 prefixEnd_5660001 := by exact prefixLift 5660001
  have htrace : WordTrace (prefixWord ++ tailWord_5660001) baseStart_5660001 baseEnd_5660001 := by
    simpa [prefixWord, tailWord_5660001, baseEnd_5660001] using wordTrace_append hprefix tailTrace_5660001
  have hstable : (prefixWord ++ tailWord_5660001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660001).length < 2 ^ (prefixWord ++ tailWord_5660001).sum := by decide
  have hdescent : baseEnd_5660001 < baseStart_5660001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660012 : List Nat := [2, 2, 1, 1, 5, 1, 3, 3, 1, 1, 3]
def baseStart_5660012 : Nat := 118140960795 + 5660012 * 2 ^ 59
def prefixEnd_5660012 : Nat := 4983230072969 + 3 ^ 40 * 5660012 * 2
def baseEnd_5660012 : Nat := 2906306666215814410720085

theorem tailTrace_5660012 : CollatzResearch.WordTrace tailWord_5660012 prefixEnd_5660012 2906306666215814410720085 := by
  unfold tailWord_5660012
  simp only [CollatzResearch.WordTrace]
  refine ⟨103218798585375325967763145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137625064780500434623684193 103218798585375325967763145)
  ·
    refine ⟨77414098939031494475822359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103218798585375325967763145 77414098939031494475822359)
    ·
      refine ⟨116121148408547241713733539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77414098939031494475822359 116121148408547241713733539)
      ·
        refine ⟨174181722612820862570600309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116121148408547241713733539 174181722612820862570600309)
        ·
          refine ⟨16329536494951955865993779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174181722612820862570600309 16329536494951955865993779)
          ·
            refine ⟨24494304742427933798990669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16329536494951955865993779 24494304742427933798990669)
            ·
              refine ⟨9185364278410475174621501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24494304742427933798990669 9185364278410475174621501)
              ·
                refine ⟨3444511604403928190483063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9185364278410475174621501 3444511604403928190483063)
                ·
                  refine ⟨5166767406605892285724595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3444511604403928190483063 5166767406605892285724595)
                  ·
                    refine ⟨7750151109908838428586893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5166767406605892285724595 7750151109908838428586893)
                    ·
                      refine ⟨2906306666215814410720085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7750151109908838428586893 2906306666215814410720085)
                      ·
                        rfl

theorem cell23_5660012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 1, 1, 3].length) (baseStart_5660012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660012 prefixEnd_5660012 := by exact prefixLift 5660012
  have htrace : WordTrace (prefixWord ++ tailWord_5660012) baseStart_5660012 baseEnd_5660012 := by
    simpa [prefixWord, tailWord_5660012, baseEnd_5660012] using wordTrace_append hprefix tailTrace_5660012
  have hstable : (prefixWord ++ tailWord_5660012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660012).length < 2 ^ (prefixWord ++ tailWord_5660012).sum := by decide
  have hdescent : baseEnd_5660012 < baseStart_5660012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660018 : List Nat := [3, 2, 1, 2, 1, 2, 1, 5, 1, 1, 4]
def baseStart_5660018 : Nat := 118140960795 + 5660018 * 2 ^ 59
def prefixEnd_5660018 : Nat := 4983230072969 + 3 ^ 40 * 5660018 * 2
def baseEnd_5660018 : Nat := 2906309747099741387245057

theorem tailTrace_5660018 : CollatzResearch.WordTrace tailWord_5660018 prefixEnd_5660018 2906309747099741387245057 := by
  unfold tailWord_5660018
  simp only [CollatzResearch.WordTrace]
  refine ⟨51609454002182228740061177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137625210672485943306829805 51609454002182228740061177)
  ·
    refine ⟨38707090501636671555045883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51609454002182228740061177 38707090501636671555045883)
    ·
      refine ⟨58060635752455007332568825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38707090501636671555045883 58060635752455007332568825)
      ·
        refine ⟨43545476814341255499426619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58060635752455007332568825 43545476814341255499426619)
        ·
          refine ⟨65318215221511883249139929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43545476814341255499426619 65318215221511883249139929)
          ·
            refine ⟨48988661416133912436854947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65318215221511883249139929 48988661416133912436854947)
            ·
              refine ⟨73482992124200868655282421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48988661416133912436854947 73482992124200868655282421)
              ·
                refine ⟨6889030511643831436432727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73482992124200868655282421 6889030511643831436432727)
                ·
                  refine ⟨10333545767465747154649091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6889030511643831436432727 10333545767465747154649091)
                  ·
                    refine ⟨15500318651198620731973637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10333545767465747154649091 15500318651198620731973637)
                    ·
                      refine ⟨2906309747099741387245057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15500318651198620731973637 2906309747099741387245057)
                      ·
                        rfl

theorem cell23_5660018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_5660018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660018 prefixEnd_5660018 := by exact prefixLift 5660018
  have htrace : WordTrace (prefixWord ++ tailWord_5660018) baseStart_5660018 baseEnd_5660018 := by
    simpa [prefixWord, tailWord_5660018, baseEnd_5660018] using wordTrace_append hprefix tailTrace_5660018
  have hstable : (prefixWord ++ tailWord_5660018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660018).length < 2 ^ (prefixWord ++ tailWord_5660018).sum := by decide
  have hdescent : baseEnd_5660018 < baseStart_5660018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660028 : List Nat := [2, 2, 2, 1, 1, 1, 4, 4, 2, 4]
def baseStart_5660028 : Nat := 118140960795 + 5660028 * 2 ^ 59
def prefixEnd_5660028 : Nat := 4983230072969 + 3 ^ 40 * 5660028 * 2
def baseEnd_5660028 : Nat := 968771627302095449373337

theorem tailTrace_5660028 : CollatzResearch.WordTrace tailWord_5660028 prefixEnd_5660028 968771627302095449373337 := by
  unfold tailWord_5660028
  simp only [CollatzResearch.WordTrace]
  refine ⟨103219090369346343334054369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137625453825795124445405825 103219090369346343334054369)
  ·
    refine ⟨77414317777009757500540777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103219090369346343334054369 77414317777009757500540777)
    ·
      refine ⟨58060738332757318125405583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77414317777009757500540777 58060738332757318125405583)
      ·
        refine ⟨87091107499135977188108375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58060738332757318125405583 87091107499135977188108375)
        ·
          refine ⟨130636661248703965782162563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87091107499135977188108375 130636661248703965782162563)
          ·
            refine ⟨195954991873055948673243845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130636661248703965782162563 195954991873055948673243845)
            ·
              refine ⟨36741560976197990376233221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195954991873055948673243845 36741560976197990376233221)
              ·
                refine ⟨6889042683037123195543729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36741560976197990376233221 6889042683037123195543729)
                ·
                  refine ⟨5166782012277842396657797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6889042683037123195543729 5166782012277842396657797)
                  ·
                    refine ⟨968771627302095449373337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5166782012277842396657797 968771627302095449373337)
                    ·
                      rfl

theorem cell23_5660028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_5660028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660028 prefixEnd_5660028 := by exact prefixLift 5660028
  have htrace : WordTrace (prefixWord ++ tailWord_5660028) baseStart_5660028 baseEnd_5660028 := by
    simpa [prefixWord, tailWord_5660028, baseEnd_5660028] using wordTrace_append hprefix tailTrace_5660028
  have hstable : (prefixWord ++ tailWord_5660028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660028).length < 2 ^ (prefixWord ++ tailWord_5660028).sum := by decide
  have hdescent : baseEnd_5660028 < baseStart_5660028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660051 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 3]
def baseStart_5660051 : Nat := 118140960795 + 5660051 * 2 ^ 59
def prefixEnd_5660051 : Nat := 4983230072969 + 3 ^ 40 * 5660051 * 2
def baseEnd_5660051 : Nat := 2906326691961339758132405

theorem tailTrace_5660051 : CollatzResearch.WordTrace tailWord_5660051 prefixEnd_5660051 2906326691961339758132405 := by
  unfold tailWord_5660051
  simp only [CollatzResearch.WordTrace]
  refine ⟨206439019617609361596196007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137626013078406241064130671 206439019617609361596196007)
  ·
    refine ⟨309658529426414042394294011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206439019617609361596196007 309658529426414042394294011)
    ·
      refine ⟨464487794139621063591441017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309658529426414042394294011 464487794139621063591441017)
      ·
        refine ⟨348365845604715797693580763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 464487794139621063591441017 348365845604715797693580763)
        ·
          refine ⟨522548768407073696540371145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348365845604715797693580763 522548768407073696540371145)
          ·
            refine ⟨391911576305305272405278359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522548768407073696540371145 391911576305305272405278359)
            ·
              refine ⟨587867364457957908607917539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391911576305305272405278359 587867364457957908607917539)
              ·
                refine ⟨881801046686936862911876309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587867364457957908607917539 881801046686936862911876309)
                ·
                  refine ⟨20667212031725082724497101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 881801046686936862911876309 20667212031725082724497101)
                  ·
                    refine ⟨7750204511896906021686413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20667212031725082724497101 7750204511896906021686413)
                    ·
                      refine ⟨2906326691961339758132405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7750204511896906021686413 2906326691961339758132405)
                      ·
                        rfl

theorem cell23_5660051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 3].length) (baseStart_5660051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660051 prefixEnd_5660051 := by exact prefixLift 5660051
  have htrace : WordTrace (prefixWord ++ tailWord_5660051) baseStart_5660051 baseEnd_5660051 := by
    simpa [prefixWord, tailWord_5660051, baseEnd_5660051] using wordTrace_append hprefix tailTrace_5660051
  have hstable : (prefixWord ++ tailWord_5660051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660051).length < 2 ^ (prefixWord ++ tailWord_5660051).sum := by decide
  have hdescent : baseEnd_5660051 < baseStart_5660051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660052 : List Nat := [2, 4, 2, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_5660052 : Nat := 118140960795 + 5660052 * 2 ^ 59
def prefixEnd_5660052 : Nat := 4983230072969 + 3 ^ 40 * 5660052 * 2
def baseEnd_5660052 : Nat := 2906327205441994254219901

theorem tailTrace_5660052 : CollatzResearch.WordTrace tailWord_5660052 prefixEnd_5660052 2906327205441994254219901 := by
  unfold tailWord_5660052
  simp only [CollatzResearch.WordTrace]
  refine ⟨103219528045302869383491205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137626037393737159177988273 103219528045302869383491205)
  ·
    refine ⟨19353661508494288009404601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103219528045302869383491205 19353661508494288009404601)
    ·
      refine ⟨14515246131370716007053451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19353661508494288009404601 14515246131370716007053451)
      ·
        refine ⟨21772869197056074010580177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14515246131370716007053451 21772869197056074010580177)
        ·
          refine ⟨16329651897792055507935133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21772869197056074010580177 16329651897792055507935133)
          ·
            refine ⟨6123619461672020815475675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16329651897792055507935133 6123619461672020815475675)
            ·
              refine ⟨9185429192508031223213513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6123619461672020815475675 9185429192508031223213513)
              ·
                refine ⟨6889071894381023417410135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9185429192508031223213513 6889071894381023417410135)
                ·
                  refine ⟨10333607841571535126115203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6889071894381023417410135 10333607841571535126115203)
                  ·
                    refine ⟨15500411762357302689172805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10333607841571535126115203 15500411762357302689172805)
                    ·
                      refine ⟨2906327205441994254219901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15500411762357302689172805 2906327205441994254219901)
                      ·
                        rfl

theorem cell23_5660052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_5660052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660052 prefixEnd_5660052 := by exact prefixLift 5660052
  have htrace : WordTrace (prefixWord ++ tailWord_5660052) baseStart_5660052 baseEnd_5660052 := by
    simpa [prefixWord, tailWord_5660052, baseEnd_5660052] using wordTrace_append hprefix tailTrace_5660052
  have hstable : (prefixWord ++ tailWord_5660052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660052).length < 2 ^ (prefixWord ++ tailWord_5660052).sum := by decide
  have hdescent : baseEnd_5660052 < baseStart_5660052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660072 : List Nat := [2, 1, 6, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_5660072 : Nat := 118140960795 + 5660072 * 2 ^ 59
def prefixEnd_5660072 : Nat := 4983230072969 + 3 ^ 40 * 5660072 * 2
def baseEnd_5660072 : Nat := 2906337475055084175969809

theorem tailTrace_5660072 : CollatzResearch.WordTrace tailWord_5660072 prefixEnd_5660072 2906337475055084175969809 := by
  unfold tailWord_5660072
  simp only [CollatzResearch.WordTrace]
  refine ⟨103219892775266641091355235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137626523700355521455140313 103219892775266641091355235)
  ·
    refine ⟨154829839162899961637032853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103219892775266641091355235 154829839162899961637032853)
    ·
      refine ⟨7257648710760935701735915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 154829839162899961637032853 7257648710760935701735915)
      ·
        refine ⟨10886473066141403552603873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7257648710760935701735915 10886473066141403552603873)
        ·
          refine ⟨8164854799606052664452905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10886473066141403552603873 8164854799606052664452905)
          ·
            refine ⟨6123641099704539498339679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8164854799606052664452905 6123641099704539498339679)
            ·
              refine ⟨9185461649556809247509519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6123641099704539498339679 9185461649556809247509519)
              ·
                refine ⟨13778192474335213871264279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9185461649556809247509519 13778192474335213871264279)
                ·
                  refine ⟨20667288711502820806896419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13778192474335213871264279 20667288711502820806896419)
                  ·
                    refine ⟨31000933067254231210344629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20667288711502820806896419 31000933067254231210344629)
                    ·
                      refine ⟨2906337475055084175969809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31000933067254231210344629 2906337475055084175969809)
                      ·
                        rfl

theorem cell23_5660072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_5660072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660072 prefixEnd_5660072 := by exact prefixLift 5660072
  have htrace : WordTrace (prefixWord ++ tailWord_5660072) baseStart_5660072 baseEnd_5660072 := by
    simpa [prefixWord, tailWord_5660072, baseEnd_5660072] using wordTrace_append hprefix tailTrace_5660072
  have hstable : (prefixWord ++ tailWord_5660072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660072).length < 2 ^ (prefixWord ++ tailWord_5660072).sum := by decide
  have hdescent : baseEnd_5660072 < baseStart_5660072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660111 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 5]
def baseStart_5660111 : Nat := 118140960795 + 5660111 * 2 ^ 59
def prefixEnd_5660111 : Nat := 4983230072969 + 3 ^ 40 * 5660111 * 2
def baseEnd_5660111 : Nat := 2906357500800609523382129

theorem tailTrace_5660111 : CollatzResearch.WordTrace tailWord_5660111 prefixEnd_5660111 2906357500800609523382129 := by
  unfold tailWord_5660111
  simp only [CollatzResearch.WordTrace]
  refine ⟨206441207997391991843380187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137627471998261327895586791 206441207997391991843380187)
  ·
    refine ⟨309661811996087987765070281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206441207997391991843380187 309661811996087987765070281)
    ·
      refine ⟨232246358997065990823802711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309661811996087987765070281 232246358997065990823802711)
      ·
        refine ⟨348369538495598986235704067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232246358997065990823802711 348369538495598986235704067)
        ·
          refine ⟨522554307743398479353556101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348369538495598986235704067 522554307743398479353556101)
          ·
            refine ⟨97978932701887214878791769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 522554307743398479353556101 97978932701887214878791769)
            ·
              refine ⟨73484199526415411159093827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97978932701887214878791769 73484199526415411159093827)
              ·
                refine ⟨110226299289623116738640741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73484199526415411159093827 110226299289623116738640741)
                ·
                  refine ⟨20667431116804334388495139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110226299289623116738640741 20667431116804334388495139)
                  ·
                    refine ⟨31001146675206501582742709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20667431116804334388495139 31001146675206501582742709)
                    ·
                      refine ⟨2906357500800609523382129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31001146675206501582742709 2906357500800609523382129)
                      ·
                        rfl

theorem cell23_5660111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_5660111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660111 prefixEnd_5660111 := by exact prefixLift 5660111
  have htrace : WordTrace (prefixWord ++ tailWord_5660111) baseStart_5660111 baseEnd_5660111 := by
    simpa [prefixWord, tailWord_5660111, baseEnd_5660111] using wordTrace_append hprefix tailTrace_5660111
  have hstable : (prefixWord ++ tailWord_5660111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660111).length < 2 ^ (prefixWord ++ tailWord_5660111).sum := by decide
  have hdescent : baseEnd_5660111 < baseStart_5660111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660129 : List Nat := [1, 2, 3, 1, 2, 5, 2, 1, 1, 3, 2]
def baseStart_5660129 : Nat := 118140960795 + 5660129 * 2 ^ 59
def prefixEnd_5660129 : Nat := 4983230072969 + 3 ^ 40 * 5660129 * 2
def baseEnd_5660129 : Nat := 2906366743452390452957047

theorem tailTrace_5660129 : CollatzResearch.WordTrace tailWord_5660129 prefixEnd_5660129 2906366743452390452957047 := by
  unfold tailWord_5660129
  simp only [CollatzResearch.WordTrace]
  refine ⟨206441864511326780917535441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137627909674217853945023627 206441864511326780917535441)
  ·
    refine ⟨154831398383495085688151581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206441864511326780917535441 154831398383495085688151581)
    ·
      refine ⟨58061774393810657133056843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154831398383495085688151581 58061774393810657133056843)
      ·
        refine ⟨87092661590715985699585265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58061774393810657133056843 87092661590715985699585265)
        ·
          refine ⟨65319496193036989274688949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87092661590715985699585265 65319496193036989274688949)
          ·
            refine ⟨6123702768097217744502089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65319496193036989274688949 6123702768097217744502089)
            ·
              refine ⟨4592777076072913308376567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6123702768097217744502089 4592777076072913308376567)
              ·
                refine ⟨6889165614109369962564851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4592777076072913308376567 6889165614109369962564851)
                ·
                  refine ⟨10333748421164054943847277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6889165614109369962564851 10333748421164054943847277)
                  ·
                    refine ⟨3875155657936520603942729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10333748421164054943847277 3875155657936520603942729)
                    ·
                      refine ⟨2906366743452390452957047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3875155657936520603942729 2906366743452390452957047)
                      ·
                        rfl

theorem cell23_5660129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_5660129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660129 prefixEnd_5660129 := by exact prefixLift 5660129
  have htrace : WordTrace (prefixWord ++ tailWord_5660129) baseStart_5660129 baseEnd_5660129 := by
    simpa [prefixWord, tailWord_5660129, baseEnd_5660129] using wordTrace_append hprefix tailTrace_5660129
  have hstable : (prefixWord ++ tailWord_5660129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660129).length < 2 ^ (prefixWord ++ tailWord_5660129).sum := by decide
  have hdescent : baseEnd_5660129 < baseStart_5660129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660142 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 4, 2, 2]
def baseStart_5660142 : Nat := 118140960795 + 5660142 * 2 ^ 59
def prefixEnd_5660142 : Nat := 4983230072969 + 3 ^ 40 * 5660142 * 2
def baseEnd_5660142 : Nat := 2906373418700898902094487

theorem tailTrace_5660142 : CollatzResearch.WordTrace tailWord_5660142 prefixEnd_5660142 2906373418700898902094487 := by
  unfold tailWord_5660142
  simp only [CollatzResearch.WordTrace]
  refine ⟨25805292332534960517219835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137628225773519789425172453 25805292332534960517219835)
  ·
    refine ⟨38707938498802440775829753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25805292332534960517219835 38707938498802440775829753)
    ·
      refine ⟨29030953874101830581872315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38707938498802440775829753 29030953874101830581872315)
      ·
        refine ⟨43546430811152745872808473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29030953874101830581872315 43546430811152745872808473)
        ·
          refine ⟨32659823108364559404606355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43546430811152745872808473 32659823108364559404606355)
          ·
            refine ⟨48989734662546839106909533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32659823108364559404606355 48989734662546839106909533)
            ·
              refine ⟨18371150498455064665091075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48989734662546839106909533 18371150498455064665091075)
              ·
                refine ⟨27556725747682596997636613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18371150498455064665091075 27556725747682596997636613)
                ·
                  refine ⟨5166886077690486937056865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27556725747682596997636613 5166886077690486937056865)
                  ·
                    refine ⟨3875164558267865202792649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5166886077690486937056865 3875164558267865202792649)
                    ·
                      refine ⟨2906373418700898902094487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3875164558267865202792649 2906373418700898902094487)
                      ·
                        rfl

theorem cell23_5660142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_5660142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660142 prefixEnd_5660142 := by exact prefixLift 5660142
  have htrace : WordTrace (prefixWord ++ tailWord_5660142) baseStart_5660142 baseEnd_5660142 := by
    simpa [prefixWord, tailWord_5660142, baseEnd_5660142] using wordTrace_append hprefix tailTrace_5660142
  have hstable : (prefixWord ++ tailWord_5660142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660142).length < 2 ^ (prefixWord ++ tailWord_5660142).sum := by decide
  have hdescent : baseEnd_5660142 < baseStart_5660142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660188 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_5660188 : Nat := 118140960795 + 5660188 * 2 ^ 59
def prefixEnd_5660188 : Nat := 4983230072969 + 3 ^ 40 * 5660188 * 2
def baseEnd_5660188 : Nat := 2906397038811005722119275

theorem tailTrace_5660188 : CollatzResearch.WordTrace tailWord_5660188 prefixEnd_5660188 2906397038811005722119275 := by
  unfold tailWord_5660188
  simp only [CollatzResearch.WordTrace]
  refine ⟨103222008209056516996966609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137629344278742022662622145 103222008209056516996966609)
  ·
    refine ⟨77416506156792387747724957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103222008209056516996966609 77416506156792387747724957)
    ·
      refine ⟨29031189808797145405396859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77416506156792387747724957 29031189808797145405396859)
      ·
        refine ⟨43546784713195718108095289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29031189808797145405396859 43546784713195718108095289)
        ·
          refine ⟨32660088534896788581071467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43546784713195718108095289 32660088534896788581071467)
          ·
            refine ⟨48990132802345182871607201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32660088534896788581071467 48990132802345182871607201)
            ·
              refine ⟨36742599601758887153705401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48990132802345182871607201 36742599601758887153705401)
              ·
                refine ⟨27556949701319165365279051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36742599601758887153705401 27556949701319165365279051)
                ·
                  refine ⟨41335424551978748047918577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27556949701319165365279051 41335424551978748047918577)
                  ·
                    refine ⟨31001568413984061035938933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41335424551978748047918577 31001568413984061035938933)
                    ·
                      refine ⟨2906397038811005722119275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31001568413984061035938933 2906397038811005722119275)
                      ·
                        rfl

theorem cell23_5660188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_5660188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660188 prefixEnd_5660188 := by exact prefixLift 5660188
  have htrace : WordTrace (prefixWord ++ tailWord_5660188) baseStart_5660188 baseEnd_5660188 := by
    simpa [prefixWord, tailWord_5660188, baseEnd_5660188] using wordTrace_append hprefix tailTrace_5660188
  have hstable : (prefixWord ++ tailWord_5660188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660188).length < 2 ^ (prefixWord ++ tailWord_5660188).sum := by decide
  have hdescent : baseEnd_5660188 < baseStart_5660188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660195 : List Nat := [1, 1, 1, 4, 5, 1, 1, 2, 2, 5]
def baseStart_5660195 : Nat := 118140960795 + 5660195 * 2 ^ 59
def prefixEnd_5660195 : Nat := 4983230072969 + 3 ^ 40 * 5660195 * 2
def baseEnd_5660195 : Nat := 968800211058529064910581

theorem tailTrace_5660195 : CollatzResearch.WordTrace tailWord_5660195 prefixEnd_5660195 968800211058529064910581 := by
  unfold tailWord_5660195
  simp only [CollatzResearch.WordTrace]
  refine ⟨206444271729087674189438039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137629514486058449459625359 206444271729087674189438039)
  ·
    refine ⟨309666407593631511284157059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206444271729087674189438039 309666407593631511284157059)
    ·
      refine ⟨464499611390447266926235589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309666407593631511284157059 464499611390447266926235589)
      ·
        refine ⟨87093677135708862548669173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 464499611390447266926235589 87093677135708862548669173)
        ·
          refine ⟨8165032231472705863937735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87093677135708862548669173 8165032231472705863937735)
          ·
            refine ⟨12247548347209058795906603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8165032231472705863937735 12247548347209058795906603)
            ·
              refine ⟨18371322520813588193859905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12247548347209058795906603 18371322520813588193859905)
              ·
                refine ⟨13778491890610191145394929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18371322520813588193859905 13778491890610191145394929)
                ·
                  refine ⟨10333868917957643359046197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13778491890610191145394929 10333868917957643359046197)
                  ·
                    refine ⟨968800211058529064910581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10333868917957643359046197 968800211058529064910581)
                    ·
                      rfl

theorem cell23_5660195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 5].length) (baseStart_5660195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660195 prefixEnd_5660195 := by exact prefixLift 5660195
  have htrace : WordTrace (prefixWord ++ tailWord_5660195) baseStart_5660195 baseEnd_5660195 := by
    simpa [prefixWord, tailWord_5660195, baseEnd_5660195] using wordTrace_append hprefix tailTrace_5660195
  have hstable : (prefixWord ++ tailWord_5660195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660195).length < 2 ^ (prefixWord ++ tailWord_5660195).sum := by decide
  have hdescent : baseEnd_5660195 < baseStart_5660195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660225 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 5, 4]
def baseStart_5660225 : Nat := 118140960795 + 5660225 * 2 ^ 59
def prefixEnd_5660225 : Nat := 4983230072969 + 3 ^ 40 * 5660225 * 2
def baseEnd_5660225 : Nat := 968805345865074025785535

theorem tailTrace_5660225 : CollatzResearch.WordTrace tailWord_5660225 prefixEnd_5660225 968805345865074025785535 := by
  unfold tailWord_5660225
  simp only [CollatzResearch.WordTrace]
  refine ⟨206445365918978989313030129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137630243945985992875353419 206445365918978989313030129)
  ·
    refine ⟨154834024439234241984772597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206445365918978989313030129 154834024439234241984772597)
    ·
      refine ⟨14515689791178210186072431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154834024439234241984772597 14515689791178210186072431)
      ·
        refine ⟨21773534686767315279108647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14515689791178210186072431 21773534686767315279108647)
        ·
          refine ⟨32660302030150972918662971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21773534686767315279108647 32660302030150972918662971)
          ·
            refine ⟨48990453045226459377994457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32660302030150972918662971 48990453045226459377994457)
            ·
              refine ⟨36742839783919844533495843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48990453045226459377994457 36742839783919844533495843)
              ·
                refine ⟨55114259675879766800243765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36742839783919844533495843 55114259675879766800243765)
                ·
                  refine ⟨5166961844613728137522853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55114259675879766800243765 5166961844613728137522853)
                  ·
                    refine ⟨968805345865074025785535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5166961844613728137522853 968805345865074025785535)
                    ·
                      rfl

theorem cell23_5660225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_5660225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660225 prefixEnd_5660225 := by exact prefixLift 5660225
  have htrace : WordTrace (prefixWord ++ tailWord_5660225) baseStart_5660225 baseEnd_5660225 := by
    simpa [prefixWord, tailWord_5660225, baseEnd_5660225] using wordTrace_append hprefix tailTrace_5660225
  have hstable : (prefixWord ++ tailWord_5660225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660225).length < 2 ^ (prefixWord ++ tailWord_5660225).sum := by decide
  have hdescent : baseEnd_5660225 < baseStart_5660225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660252 : List Nat := [2, 2, 4, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_5660252 : Nat := 118140960795 + 5660252 * 2 ^ 59
def prefixEnd_5660252 : Nat := 4983230072969 + 3 ^ 40 * 5660252 * 2
def baseEnd_5660252 : Nat := 2906429901572893471718981

theorem tailTrace_5660252 : CollatzResearch.WordTrace tailWord_5660252 prefixEnd_5660252 2906429901572893471718981 := by
  unfold tailWord_5660252
  simp only [CollatzResearch.WordTrace]
  refine ⟨103223175344940586462131505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137630900459920781949508673 103223175344940586462131505)
  ·
    refine ⟨77417381508705439846598629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103223175344940586462131505 77417381508705439846598629)
    ·
      refine ⟨14515759032882269971237243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77417381508705439846598629 14515759032882269971237243)
      ·
        refine ⟨21773638549323404956855865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14515759032882269971237243 21773638549323404956855865)
        ·
          refine ⟨16330228911992553717641899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21773638549323404956855865 16330228911992553717641899)
          ·
            refine ⟨24495343367988830576462849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16330228911992553717641899 24495343367988830576462849)
            ·
              refine ⟨18371507525991622932347137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24495343367988830576462849 18371507525991622932347137)
              ·
                refine ⟨13778630644493717199260353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18371507525991622932347137 13778630644493717199260353)
                ·
                  refine ⟨10333972983370287899445265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13778630644493717199260353 10333972983370287899445265)
                  ·
                    refine ⟨7750479737527715924583949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10333972983370287899445265 7750479737527715924583949)
                    ·
                      refine ⟨2906429901572893471718981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7750479737527715924583949 2906429901572893471718981)
                      ·
                        rfl

theorem cell23_5660252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_5660252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660252 prefixEnd_5660252 := by exact prefixLift 5660252
  have htrace : WordTrace (prefixWord ++ tailWord_5660252) baseStart_5660252 baseEnd_5660252 := by
    simpa [prefixWord, tailWord_5660252, baseEnd_5660252] using wordTrace_append hprefix tailTrace_5660252
  have hstable : (prefixWord ++ tailWord_5660252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660252).length < 2 ^ (prefixWord ++ tailWord_5660252).sum := by decide
  have hdescent : baseEnd_5660252 < baseStart_5660252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660259 : List Nat := [1, 1, 1, 5, 1, 3, 4, 2, 1, 4]
def baseStart_5660259 : Nat := 118140960795 + 5660259 * 2 ^ 59
def prefixEnd_5660259 : Nat := 4983230072969 + 3 ^ 40 * 5660259 * 2
def baseEnd_5660259 : Nat := 968811165312491648110483

theorem tailTrace_5660259 : CollatzResearch.WordTrace tailWord_5660259 prefixEnd_5660259 968811165312491648110483 := by
  unfold tailWord_5660259
  simp only [CollatzResearch.WordTrace]
  refine ⟨206446606000855813119767831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137631070667237208746511887 206446606000855813119767831)
  ·
    refine ⟨309669909001283719679651747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206446606000855813119767831 309669909001283719679651747)
    ·
      refine ⟨464504863501925579519477621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309669909001283719679651747 464504863501925579519477621)
      ·
        refine ⟨43547330953305523079951027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 464504863501925579519477621 43547330953305523079951027)
        ·
          refine ⟨65320996429958284619926541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43547330953305523079951027 65320996429958284619926541)
          ·
            refine ⟨24495373661234356732472453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65320996429958284619926541 24495373661234356732472453)
            ·
              refine ⟨4592882561481441887338585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24495373661234356732472453 4592882561481441887338585)
              ·
                refine ⟨3444661921111081415503939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4592882561481441887338585 3444661921111081415503939)
                ·
                  refine ⟨5166992881666622123255909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3444661921111081415503939 5166992881666622123255909)
                  ·
                    refine ⟨968811165312491648110483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5166992881666622123255909 968811165312491648110483)
                    ·
                      rfl

theorem cell23_5660259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 1, 4].length) (baseStart_5660259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660259 prefixEnd_5660259 := by exact prefixLift 5660259
  have htrace : WordTrace (prefixWord ++ tailWord_5660259) baseStart_5660259 baseEnd_5660259 := by
    simpa [prefixWord, tailWord_5660259, baseEnd_5660259] using wordTrace_append hprefix tailTrace_5660259
  have hstable : (prefixWord ++ tailWord_5660259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660259).length < 2 ^ (prefixWord ++ tailWord_5660259).sum := by decide
  have hdescent : baseEnd_5660259 < baseStart_5660259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660285 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 3, 5]
def baseStart_5660285 : Nat := 118140960795 + 5660285 * 2 ^ 59
def prefixEnd_5660285 : Nat := 4983230072969 + 3 ^ 40 * 5660285 * 2
def baseEnd_5660285 : Nat := 968815615478163947535443

theorem tailTrace_5660285 : CollatzResearch.WordTrace tailWord_5660285 prefixEnd_5660285 968815615478163947535443 := by
  unfold tailWord_5660285
  simp only [CollatzResearch.WordTrace]
  refine ⟨206447554298761619560214309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137631702865841079706809539 206447554298761619560214309)
  ·
    refine ⟨38708916431017803667540183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206447554298761619560214309 38708916431017803667540183)
    ·
      refine ⟨58063374646526705501310275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38708916431017803667540183 58063374646526705501310275)
      ·
        refine ⟨87095061969790058251965413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58063374646526705501310275 87095061969790058251965413)
        ·
          refine ⟨16330324119335635922243515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87095061969790058251965413 16330324119335635922243515)
          ·
            refine ⟨24495486179003453883365273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16330324119335635922243515 24495486179003453883365273)
            ·
              refine ⟨18371614634252590412523955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24495486179003453883365273 18371614634252590412523955)
              ·
                refine ⟨27557421951378885618785933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18371614634252590412523955 27557421951378885618785933)
                ·
                  refine ⟨10334033231767082107044725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27557421951378885618785933 10334033231767082107044725)
                  ·
                    refine ⟨968815615478163947535443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10334033231767082107044725 968815615478163947535443)
                    ·
                      rfl

theorem cell23_5660285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_5660285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660285 prefixEnd_5660285 := by exact prefixLift 5660285
  have htrace : WordTrace (prefixWord ++ tailWord_5660285) baseStart_5660285 baseEnd_5660285 := by
    simpa [prefixWord, tailWord_5660285, baseEnd_5660285] using wordTrace_append hprefix tailTrace_5660285
  have hstable : (prefixWord ++ tailWord_5660285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660285).length < 2 ^ (prefixWord ++ tailWord_5660285).sum := by decide
  have hdescent : baseEnd_5660285 < baseStart_5660285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660299 : List Nat := [1, 1, 1, 1, 4, 1, 6, 3, 1, 1, 3]
def baseStart_5660299 : Nat := 118140960795 + 5660299 * 2 ^ 59
def prefixEnd_5660299 : Nat := 4983230072969 + 3 ^ 40 * 5660299 * 2
def baseEnd_5660299 : Nat := 2906454035163654787831265

theorem tailTrace_5660299 : CollatzResearch.WordTrace tailWord_5660299 prefixEnd_5660299 2906454035163654787831265 := by
  unfold tailWord_5660299
  simp only [CollatzResearch.WordTrace]
  refine ⟨206448064920710899951223951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137632043280473933300815967 206448064920710899951223951)
  ·
    refine ⟨309672097381066349926835927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206448064920710899951223951 309672097381066349926835927)
    ·
      refine ⟨464508146071599524890253891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309672097381066349926835927 464508146071599524890253891)
      ·
        refine ⟨696762219107399287335380837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464508146071599524890253891 696762219107399287335380837)
        ·
          refine ⟨130642916082637366375383907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 696762219107399287335380837 130642916082637366375383907)
          ·
            refine ⟨195964374123956049563075861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130642916082637366375383907 195964374123956049563075861)
            ·
              refine ⟨9185830037060439823269181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 195964374123956049563075861 9185830037060439823269181)
              ·
                refine ⟨3444686263897664933725943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9185830037060439823269181 3444686263897664933725943)
                ·
                  refine ⟨5167029395846497400588915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3444686263897664933725943 5167029395846497400588915)
                  ·
                    refine ⟨7750544093769746100883373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5167029395846497400588915 7750544093769746100883373)
                    ·
                      refine ⟨2906454035163654787831265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7750544093769746100883373 2906454035163654787831265)
                      ·
                        rfl

theorem cell23_5660299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 1, 1, 3].length) (baseStart_5660299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660299 prefixEnd_5660299 := by exact prefixLift 5660299
  have htrace : WordTrace (prefixWord ++ tailWord_5660299) baseStart_5660299 baseEnd_5660299 := by
    simpa [prefixWord, tailWord_5660299, baseEnd_5660299] using wordTrace_append hprefix tailTrace_5660299
  have hstable : (prefixWord ++ tailWord_5660299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660299).length < 2 ^ (prefixWord ++ tailWord_5660299).sum := by decide
  have hdescent : baseEnd_5660299 < baseStart_5660299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5660302 : List Nat := [4, 1, 1, 3, 1, 3, 1, 3, 1, 5]
def baseStart_5660302 : Nat := 118140960795 + 5660302 * 2 ^ 59
def prefixEnd_5660302 : Nat := 4983230072969 + 3 ^ 40 * 5660302 * 2
def baseEnd_5660302 : Nat := 968818525201872758697917

theorem tailTrace_5660302 : CollatzResearch.WordTrace tailWord_5660302 prefixEnd_5660302 968818525201872758697917 := by
  unfold tailWord_5660302
  simp only [CollatzResearch.WordTrace]
  refine ⟨25806021792462503932947895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137632116226466687642388773 25806021792462503932947895)
  ·
    refine ⟨38709032688693755899421843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25806021792462503932947895 38709032688693755899421843)
    ·
      refine ⟨58063549033040633849132765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38709032688693755899421843 58063549033040633849132765)
      ·
        refine ⟨21773830887390237693424787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58063549033040633849132765 21773830887390237693424787)
        ·
          refine ⟨32660746331085356540137181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21773830887390237693424787 32660746331085356540137181)
          ·
            refine ⟨12247779874157008702551443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32660746331085356540137181 12247779874157008702551443)
            ·
              refine ⟨18371669811235513053827165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12247779874157008702551443 18371669811235513053827165)
              ·
                refine ⟨6889376179213317395185187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18371669811235513053827165 6889376179213317395185187)
                ·
                  refine ⟨10334064268819976092777781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6889376179213317395185187 10334064268819976092777781)
                  ·
                    refine ⟨968818525201872758697917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10334064268819976092777781 968818525201872758697917)
                    ·
                      rfl

theorem cell23_5660302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_5660302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5660302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5660302 prefixEnd_5660302 := by exact prefixLift 5660302
  have htrace : WordTrace (prefixWord ++ tailWord_5660302) baseStart_5660302 baseEnd_5660302 := by
    simpa [prefixWord, tailWord_5660302, baseEnd_5660302] using wordTrace_append hprefix tailTrace_5660302
  have hstable : (prefixWord ++ tailWord_5660302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5660302).length < 2 ^ (prefixWord ++ tailWord_5660302).sum := by decide
  have hdescent : baseEnd_5660302 < baseStart_5660302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5660302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
