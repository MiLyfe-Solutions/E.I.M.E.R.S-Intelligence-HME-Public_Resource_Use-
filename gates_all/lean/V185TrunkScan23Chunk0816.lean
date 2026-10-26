import V185TrunkScan23Chunk0815

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4827585 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 8]
def baseStart_4827585 : Nat := 118140960795 + 4827585 * 2 ^ 59
def prefixEnd_4827585 : Nat := 4983230072969 + 3 ^ 40 * 4827585 * 2
def baseEnd_4827585 : Nat := 275430167270622198353983

theorem tailTrace_4827585 : CollatzResearch.WordTrace tailWord_4827585 prefixEnd_4827585 275430167270622198353983 := by
  unfold tailWord_4827585
  simp only [CollatzResearch.WordTrace]
  refine ⟨176076490215491505722436209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117384326810327670481624139 176076490215491505722436209)
  ·
    refine ⟨132057367661618629291827157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176076490215491505722436209 132057367661618629291827157)
    ·
      refine ⟨3095094554569186624027199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 132057367661618629291827157 3095094554569186624027199)
      ·
        refine ⟨4642641831853779936040799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3095094554569186624027199 4642641831853779936040799)
        ·
          refine ⟨6963962747780669904061199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4642641831853779936040799 6963962747780669904061199)
          ·
            refine ⟨10445944121671004856091799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6963962747780669904061199 10445944121671004856091799)
            ·
              refine ⟨15668916182506507284137699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10445944121671004856091799 15668916182506507284137699)
              ·
                refine ⟨23503374273759760926206549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15668916182506507284137699 23503374273759760926206549)
                ·
                  refine ⟨275430167270622198353983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23503374273759760926206549 275430167270622198353983)
                  ·
                    rfl

theorem cell23_4827585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 8].length) (baseStart_4827585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827585 prefixEnd_4827585 := by exact prefixLift 4827585
  have htrace : WordTrace (prefixWord ++ tailWord_4827585) baseStart_4827585 baseEnd_4827585 := by
    simpa [prefixWord, tailWord_4827585, baseEnd_4827585] using wordTrace_append hprefix tailTrace_4827585
  have hstable : (prefixWord ++ tailWord_4827585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827585).length < 2 ^ (prefixWord ++ tailWord_4827585).sum := by decide
  have hdescent : baseEnd_4827585 < baseStart_4827585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827629 : List Nat := [1, 5, 1, 3, 1, 3, 1, 3, 1, 1, 3]
def baseStart_4827629 : Nat := 118140960795 + 4827629 * 2 ^ 59
def prefixEnd_4827629 : Nat := 4983230072969 + 3 ^ 40 * 4827629 * 2
def baseEnd_4827629 : Nat := 2478894098584397613035645

theorem tailTrace_4827629 : CollatzResearch.WordTrace tailWord_4827629 prefixEnd_4827629 2478894098584397613035645 := by
  unfold tailWord_4827629
  simp only [CollatzResearch.WordTrace]
  refine ⟨176078095027332101237037941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117385396684888067491358627 176078095027332101237037941)
  ·
    refine ⟨16507321408812384490972307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176078095027332101237037941 16507321408812384490972307)
    ·
      refine ⟨24760982113218576736458461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16507321408812384490972307 24760982113218576736458461)
      ·
        refine ⟨9285368292456966276171923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24760982113218576736458461 9285368292456966276171923)
        ·
          refine ⟨13928052438685449414257885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9285368292456966276171923 13928052438685449414257885)
          ·
            refine ⟨5223019664507043530346707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13928052438685449414257885 5223019664507043530346707)
            ·
              refine ⟨7834529496760565295520061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5223019664507043530346707 7834529496760565295520061)
              ·
                refine ⟨2937948561285211985820023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7834529496760565295520061 2937948561285211985820023)
                ·
                  refine ⟨4406922841927817978730035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2937948561285211985820023 4406922841927817978730035)
                  ·
                    refine ⟨6610384262891726968095053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4406922841927817978730035 6610384262891726968095053)
                    ·
                      refine ⟨2478894098584397613035645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6610384262891726968095053 2478894098584397613035645)
                      ·
                        rfl

theorem cell23_4827629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_4827629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827629 prefixEnd_4827629 := by exact prefixLift 4827629
  have htrace : WordTrace (prefixWord ++ tailWord_4827629) baseStart_4827629 baseEnd_4827629 := by
    simpa [prefixWord, tailWord_4827629, baseEnd_4827629] using wordTrace_append hprefix tailTrace_4827629
  have hstable : (prefixWord ++ tailWord_4827629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827629).length < 2 ^ (prefixWord ++ tailWord_4827629).sum := by decide
  have hdescent : baseEnd_4827629 < baseStart_4827629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827638 : List Nat := [5, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_4827638 : Nat := 118140960795 + 4827638 * 2 ^ 59
def prefixEnd_4827638 : Nat := 4983230072969 + 3 ^ 40 * 4827638 * 2
def baseEnd_4827638 : Nat := 2478898719910288077823103

theorem tailTrace_4827638 : CollatzResearch.WordTrace tailWord_4827638 prefixEnd_4827638 2478898719910288077823103 := by
  unfold tailWord_4827638
  simp only [CollatzResearch.WordTrace]
  refine ⟨11004901455268718485882223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117385615522866330516077045 11004901455268718485882223)
  ·
    refine ⟨16507352182903077728823335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11004901455268718485882223 16507352182903077728823335)
    ·
      refine ⟨24761028274354616593235003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16507352182903077728823335 24761028274354616593235003)
      ·
        refine ⟨37141542411531924889852505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24761028274354616593235003 37141542411531924889852505)
        ·
          refine ⟨27856156808648943667389379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37141542411531924889852505 27856156808648943667389379)
          ·
            refine ⟨41784235212973415501084069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27856156808648943667389379 41784235212973415501084069)
            ·
              refine ⟨7834544102432515406453263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41784235212973415501084069 7834544102432515406453263)
              ·
                refine ⟨11751816153648773109679895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7834544102432515406453263 11751816153648773109679895)
                ·
                  refine ⟨17627724230473159664519843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11751816153648773109679895 17627724230473159664519843)
                  ·
                    refine ⟨26441586345709739496779765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17627724230473159664519843 26441586345709739496779765)
                    ·
                      refine ⟨2478898719910288077823103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26441586345709739496779765 2478898719910288077823103)
                      ·
                        rfl

theorem cell23_4827638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_4827638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827638 prefixEnd_4827638 := by exact prefixLift 4827638
  have htrace : WordTrace (prefixWord ++ tailWord_4827638) baseStart_4827638 baseEnd_4827638 := by
    simpa [prefixWord, tailWord_4827638, baseEnd_4827638] using wordTrace_append hprefix tailTrace_4827638
  have hstable : (prefixWord ++ tailWord_4827638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827638).length < 2 ^ (prefixWord ++ tailWord_4827638).sum := by decide
  have hdescent : baseEnd_4827638 < baseStart_4827638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827652 : List Nat := [2, 3, 2, 3, 1, 1, 3, 1, 3, 2, 2]
def baseStart_4827652 : Nat := 118140960795 + 4827652 * 2 ^ 59
def prefixEnd_4827652 : Nat := 4983230072969 + 3 ^ 40 * 4827652 * 2
def baseEnd_4827652 : Nat := 2478905908639451023048039

theorem tailTrace_4827652 : CollatzResearch.WordTrace tailWord_4827652 prefixEnd_4827652 2478905908639451023048039 := by
  unfold tailWord_4827652
  simp only [CollatzResearch.WordTrace]
  refine ⟨88039466953124388082562605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117385955937499184110083473 88039466953124388082562605)
  ·
    refine ⟨33014800107421645530960977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88039466953124388082562605 33014800107421645530960977)
    ·
      refine ⟨24761100080566234148220733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33014800107421645530960977 24761100080566234148220733)
      ·
        refine ⟨9285412530212337805582775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24761100080566234148220733 9285412530212337805582775)
        ·
          refine ⟨13928118795318506708374163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9285412530212337805582775 13928118795318506708374163)
          ·
            refine ⟨20892178192977760062561245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13928118795318506708374163 20892178192977760062561245)
            ·
              refine ⟨7834566822366660023460467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20892178192977760062561245 7834566822366660023460467)
              ·
                refine ⟨11751850233549990035190701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7834566822366660023460467 11751850233549990035190701)
                ·
                  refine ⟨4406943837581246263196513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11751850233549990035190701 4406943837581246263196513)
                  ·
                    refine ⟨3305207878185934697397385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4406943837581246263196513 3305207878185934697397385)
                    ·
                      refine ⟨2478905908639451023048039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3305207878185934697397385 2478905908639451023048039)
                      ·
                        rfl

theorem cell23_4827652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_4827652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827652 prefixEnd_4827652 := by exact prefixLift 4827652
  have htrace : WordTrace (prefixWord ++ tailWord_4827652) baseStart_4827652 baseEnd_4827652 := by
    simpa [prefixWord, tailWord_4827652, baseEnd_4827652] using wordTrace_append hprefix tailTrace_4827652
  have hstable : (prefixWord ++ tailWord_4827652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827652).length < 2 ^ (prefixWord ++ tailWord_4827652).sum := by decide
  have hdescent : baseEnd_4827652 < baseStart_4827652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827662 : List Nat := [4, 1, 1, 2, 3, 3, 2, 1, 2, 4]
def baseStart_4827662 : Nat := 118140960795 + 4827662 * 2 ^ 59
def prefixEnd_4827662 : Nat := 4983230072969 + 3 ^ 40 * 4827662 * 2
def baseEnd_4827662 : Nat := 826303681148665327974331

theorem tailTrace_4827662 : CollatzResearch.WordTrace tailWord_4827662 prefixEnd_4827662 826303681148665327974331 := by
  unfold tailWord_4827662
  simp only [CollatzResearch.WordTrace]
  refine ⟨22009912329526568484123655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117386199090808365248659493 22009912329526568484123655)
  ·
    refine ⟨33014868494289852726185483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22009912329526568484123655 33014868494289852726185483)
    ·
      refine ⟨49522302741434779089278225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33014868494289852726185483 49522302741434779089278225)
      ·
        refine ⟨37141727056076084316958669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49522302741434779089278225 37141727056076084316958669)
        ·
          refine ⟨13928147646028531618859501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37141727056076084316958669 13928147646028531618859501)
          ·
            refine ⟨5223055367260699357072313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13928147646028531618859501 5223055367260699357072313)
            ·
              refine ⟨3917291525445524517804235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5223055367260699357072313 3917291525445524517804235)
              ·
                refine ⟨5875937288168286776706353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3917291525445524517804235 5875937288168286776706353)
                ·
                  refine ⟨4406952966126215082529765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5875937288168286776706353 4406952966126215082529765)
                  ·
                    refine ⟨826303681148665327974331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4406952966126215082529765 826303681148665327974331)
                    ·
                      rfl

theorem cell23_4827662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_4827662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827662 prefixEnd_4827662 := by exact prefixLift 4827662
  have htrace : WordTrace (prefixWord ++ tailWord_4827662) baseStart_4827662 baseEnd_4827662 := by
    simpa [prefixWord, tailWord_4827662, baseEnd_4827662] using wordTrace_append hprefix tailTrace_4827662
  have hstable : (prefixWord ++ tailWord_4827662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827662).length < 2 ^ (prefixWord ++ tailWord_4827662).sum := by decide
  have hdescent : baseEnd_4827662 < baseStart_4827662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827701 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 2, 6]
def baseStart_4827701 : Nat := 118140960795 + 4827701 * 2 ^ 59
def prefixEnd_4827701 : Nat := 4983230072969 + 3 ^ 40 * 4827701 * 2
def baseEnd_4827701 : Nat := 826310356397173777111771

theorem tailTrace_4827701 : CollatzResearch.WordTrace tailWord_4827701 prefixEnd_4827701 826310356397173777111771 := by
  unfold tailWord_4827701
  simp only [CollatzResearch.WordTrace]
  refine ⟨176080721083071257533658957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117387147388714171689105971 176080721083071257533658957)
  ·
    refine ⟨66030270406151721575122109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176080721083071257533658957 66030270406151721575122109)
    ·
      refine ⟨24761351402306895590670791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66030270406151721575122109 24761351402306895590670791)
      ·
        refine ⟨37142027103460343386006187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24761351402306895590670791 37142027103460343386006187)
        ·
          refine ⟨55713040655190515079009281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37142027103460343386006187 55713040655190515079009281)
          ·
            refine ⟨41784780491392886309256961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55713040655190515079009281 41784780491392886309256961)
            ·
              refine ⟨31338585368544664731942721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41784780491392886309256961 31338585368544664731942721)
              ·
                refine ⟨23503939026408498548957041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31338585368544664731942721 23503939026408498548957041)
                ·
                  refine ⟨17627954269806373911717781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23503939026408498548957041 17627954269806373911717781)
                  ·
                    refine ⟨826310356397173777111771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17627954269806373911717781 826310356397173777111771)
                    ·
                      rfl

theorem cell23_4827701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_4827701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827701 prefixEnd_4827701 := by exact prefixLift 4827701
  have htrace : WordTrace (prefixWord ++ tailWord_4827701) baseStart_4827701 baseEnd_4827701 := by
    simpa [prefixWord, tailWord_4827701, baseEnd_4827701] using wordTrace_append hprefix tailTrace_4827701
  have hstable : (prefixWord ++ tailWord_4827701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827701).length < 2 ^ (prefixWord ++ tailWord_4827701).sum := by decide
  have hdescent : baseEnd_4827701 < baseStart_4827701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827702 : List Nat := [5, 1, 2, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_4827702 : Nat := 118140960795 + 4827702 * 2 ^ 59
def prefixEnd_4827702 : Nat := 4983230072969 + 3 ^ 40 * 4827702 * 2
def baseEnd_4827702 : Nat := 2478931582672175827422809

theorem tailTrace_4827702 : CollatzResearch.WordTrace tailWord_4827702 prefixEnd_4827702 2478931582672175827422809 := by
  unfold tailWord_4827702
  simp only [CollatzResearch.WordTrace]
  refine ⟨11005047347254227169027835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117387171704045089802963573 11005047347254227169027835)
  ·
    refine ⟨16507571020881340753541753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11005047347254227169027835 16507571020881340753541753)
    ·
      refine ⟨12380678265661005565156315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16507571020881340753541753 12380678265661005565156315)
      ·
        refine ⟨18571017398491508347734473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12380678265661005565156315 18571017398491508347734473)
        ·
          refine ⟨13928263048868631260800855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18571017398491508347734473 13928263048868631260800855)
          ·
            refine ⟨20892394573302946891201283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13928263048868631260800855 20892394573302946891201283)
            ·
              refine ⟨31338591859954420336801925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20892394573302946891201283 31338591859954420336801925)
              ·
                refine ⟨5875985973741453813150361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31338591859954420336801925 5875985973741453813150361)
                ·
                  refine ⟨4406989480306090359862771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5875985973741453813150361 4406989480306090359862771)
                  ·
                    refine ⟨6610484220459135539794157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4406989480306090359862771 6610484220459135539794157)
                    ·
                      refine ⟨2478931582672175827422809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6610484220459135539794157 2478931582672175827422809)
                      ·
                        rfl

theorem cell23_4827702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_4827702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827702 prefixEnd_4827702 := by exact prefixLift 4827702
  have htrace : WordTrace (prefixWord ++ tailWord_4827702) baseStart_4827702 baseEnd_4827702 := by
    simpa [prefixWord, tailWord_4827702, baseEnd_4827702] using wordTrace_append hprefix tailTrace_4827702
  have hstable : (prefixWord ++ tailWord_4827702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827702).length < 2 ^ (prefixWord ++ tailWord_4827702).sum := by decide
  have hdescent : baseEnd_4827702 < baseStart_4827702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827711 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 3]
def baseStart_4827711 : Nat := 118140960795 + 4827711 * 2 ^ 59
def prefixEnd_4827711 : Nat := 4983230072969 + 3 ^ 40 * 4827711 * 2
def baseEnd_4827711 : Nat := 2478936203998066292210267

theorem tailTrace_4827711 : CollatzResearch.WordTrace tailWord_4827711 prefixEnd_4827711 2478936203998066292210267 := by
  unfold tailWord_4827711
  simp only [CollatzResearch.WordTrace]
  refine ⟨176081085813035029241522987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117387390542023352827681991 176081085813035029241522987)
  ·
    refine ⟨264121628719552543862284481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176081085813035029241522987 264121628719552543862284481)
    ·
      refine ⟨198091221539664407896713361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264121628719552543862284481 198091221539664407896713361)
      ·
        refine ⟨148568416154748305922535021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198091221539664407896713361 148568416154748305922535021)
        ·
          refine ⟨55713156058030614720950633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148568416154748305922535021 55713156058030614720950633)
          ·
            refine ⟨41784867043522961040712975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55713156058030614720950633 41784867043522961040712975)
            ·
              refine ⟨62677300565284441561069463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41784867043522961040712975 62677300565284441561069463)
              ·
                refine ⟨94015950847926662341604195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62677300565284441561069463 94015950847926662341604195)
                ·
                  refine ⟨141023926271889993512406293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94015950847926662341604195 141023926271889993512406293)
                  ·
                    refine ⟨6610496543994843445894045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 141023926271889993512406293 6610496543994843445894045)
                    ·
                      refine ⟨2478936203998066292210267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6610496543994843445894045 2478936203998066292210267)
                      ·
                        rfl

theorem cell23_4827711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_4827711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827711 prefixEnd_4827711 := by exact prefixLift 4827711
  have htrace : WordTrace (prefixWord ++ tailWord_4827711) baseStart_4827711 baseEnd_4827711 := by
    simpa [prefixWord, tailWord_4827711, baseEnd_4827711] using wordTrace_append hprefix tailTrace_4827711
  have hstable : (prefixWord ++ tailWord_4827711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827711).length < 2 ^ (prefixWord ++ tailWord_4827711).sum := by decide
  have hdescent : baseEnd_4827711 < baseStart_4827711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827765 : List Nat := [1, 3, 4, 2, 2, 1, 2, 1, 7]
def baseStart_4827765 : Nat := 118140960795 + 4827765 * 2 ^ 59
def prefixEnd_4827765 : Nat := 4983230072969 + 3 ^ 40 * 4827765 * 2
def baseEnd_4827765 : Nat := 275440436883712120103891

theorem tailTrace_4827765 : CollatzResearch.WordTrace tailWord_4827765 prefixEnd_4827765 275440436883712120103891 := by
  unfold tailWord_4827765
  simp only [CollatzResearch.WordTrace]
  refine ⟨176083055354839396463988749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117388703569892930975992499 176083055354839396463988749)
  ·
    refine ⟨66031145758064773673995781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176083055354839396463988749 66031145758064773673995781)
    ·
      refine ⟨12380839829637145063874209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66031145758064773673995781 12380839829637145063874209)
      ·
        refine ⟨9285629872227858797905657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12380839829637145063874209 9285629872227858797905657)
        ·
          refine ⟨6964222404170894098429243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9285629872227858797905657 6964222404170894098429243)
          ·
            refine ⟨10446333606256341147643865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6964222404170894098429243 10446333606256341147643865)
            ·
              refine ⟨7834750204692255860732899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10446333606256341147643865 7834750204692255860732899)
              ·
                refine ⟨11752125307038383791099349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7834750204692255860732899 11752125307038383791099349)
                ·
                  refine ⟨275440436883712120103891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11752125307038383791099349 275440436883712120103891)
                  ·
                    rfl

theorem cell23_4827765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 7].length) (baseStart_4827765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827765 prefixEnd_4827765 := by exact prefixLift 4827765
  have htrace : WordTrace (prefixWord ++ tailWord_4827765) baseStart_4827765 baseEnd_4827765 := by
    simpa [prefixWord, tailWord_4827765, baseEnd_4827765] using wordTrace_append hprefix tailTrace_4827765
  have hstable : (prefixWord ++ tailWord_4827765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827765).length < 2 ^ (prefixWord ++ tailWord_4827765).sum := by decide
  have hdescent : baseEnd_4827765 < baseStart_4827765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827811 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 6]
def baseStart_4827811 : Nat := 118140960795 + 4827811 * 2 ^ 59
def prefixEnd_4827811 : Nat := 4983230072969 + 3 ^ 40 * 4827811 * 2
def baseEnd_4827811 : Nat := 2478987552063515900959807

theorem tailTrace_4827811 : CollatzResearch.WordTrace tailWord_4827811 prefixEnd_4827811 2478987552063515900959807 := by
  unfold tailWord_4827811
  simp only [CollatzResearch.WordTrace]
  refine ⟨176084733112672746320163287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117389822075115164213442191 176084733112672746320163287)
  ·
    refine ⟨264127099669009119480244931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176084733112672746320163287 264127099669009119480244931)
    ·
      refine ⟨396190649503513679220367397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264127099669009119480244931 396190649503513679220367397)
      ·
        refine ⟨74285746781908814853818887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 396190649503513679220367397 74285746781908814853818887)
        ·
          refine ⟨111428620172863222280728331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74285746781908814853818887 111428620172863222280728331)
          ·
            refine ⟨167142930259294833421092497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111428620172863222280728331 167142930259294833421092497)
            ·
              refine ⟨125357197694471125065819373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167142930259294833421092497 125357197694471125065819373)
              ·
                refine ⟨47008949135426671899682265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125357197694471125065819373 47008949135426671899682265)
                ·
                  refine ⟨35256711851570003924761699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47008949135426671899682265 35256711851570003924761699)
                  ·
                    refine ⟨52885067777355005887142549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35256711851570003924761699 52885067777355005887142549)
                    ·
                      refine ⟨2478987552063515900959807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52885067777355005887142549 2478987552063515900959807)
                      ·
                        rfl

theorem cell23_4827811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_4827811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827811 prefixEnd_4827811 := by exact prefixLift 4827811
  have htrace : WordTrace (prefixWord ++ tailWord_4827811) baseStart_4827811 baseEnd_4827811 := by
    simpa [prefixWord, tailWord_4827811, baseEnd_4827811] using wordTrace_append hprefix tailTrace_4827811
  have hstable : (prefixWord ++ tailWord_4827811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827811).length < 2 ^ (prefixWord ++ tailWord_4827811).sum := by decide
  have hdescent : baseEnd_4827811 < baseStart_4827811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827852 : List Nat := [2, 2, 1, 5, 1, 2, 2, 1, 2, 2, 3]
def baseStart_4827852 : Nat := 118140960795 + 4827852 * 2 ^ 59
def prefixEnd_4827852 : Nat := 4983230072969 + 3 ^ 40 * 4827852 * 2
def baseEnd_4827852 : Nat := 2479008604770350240547119

theorem tailTrace_4827852 : CollatzResearch.WordTrace tailWord_4827852 prefixEnd_4827852 2479008604770350240547119 := by
  unfold tailWord_4827852
  simp only [CollatzResearch.WordTrace]
  refine ⟨88043114252762105161202905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117390819003682806881603873 88043114252762105161202905)
  ·
    refine ⟨66032335689571578870902179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88043114252762105161202905 66032335689571578870902179)
    ·
      refine ⟨99048503534357368306353269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66032335689571578870902179 99048503534357368306353269)
      ·
        refine ⟨9285797206346003278720619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99048503534357368306353269 9285797206346003278720619)
        ·
          refine ⟨13928695809519004918080929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9285797206346003278720619 13928695809519004918080929)
          ·
            refine ⟨10446521857139253688560697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13928695809519004918080929 10446521857139253688560697)
            ·
              refine ⟨7834891392854440266420523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10446521857139253688560697 7834891392854440266420523)
              ·
                refine ⟨11752337089281660399630785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7834891392854440266420523 11752337089281660399630785)
                ·
                  refine ⟨8814252816961245299723089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11752337089281660399630785 8814252816961245299723089)
                  ·
                    refine ⟨6610689612720933974792317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8814252816961245299723089 6610689612720933974792317)
                    ·
                      refine ⟨2479008604770350240547119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6610689612720933974792317 2479008604770350240547119)
                      ·
                        rfl

theorem cell23_4827852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_4827852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827852 prefixEnd_4827852 := by exact prefixLift 4827852
  have htrace : WordTrace (prefixWord ++ tailWord_4827852) baseStart_4827852 baseEnd_4827852 := by
    simpa [prefixWord, tailWord_4827852, baseEnd_4827852] using wordTrace_append hprefix tailTrace_4827852
  have hstable : (prefixWord ++ tailWord_4827852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827852).length < 2 ^ (prefixWord ++ tailWord_4827852).sum := by decide
  have hdescent : baseEnd_4827852 < baseStart_4827852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827888 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 4]
def baseStart_4827888 : Nat := 118140960795 + 4827888 * 2 ^ 59
def prefixEnd_4827888 : Nat := 4983230072969 + 3 ^ 40 * 4827888 * 2
def baseEnd_4827888 : Nat := 2479027090073912099696953

theorem tailTrace_4827888 : CollatzResearch.WordTrace tailWord_4827888 prefixEnd_4827888 2479027090073912099696953 := by
  unfold tailWord_4827888
  simp only [CollatzResearch.WordTrace]
  refine ⟨88043770766696894235358159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117391694355595858980477545 88043770766696894235358159)
  ·
    refine ⟨132065656150045341353037239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88043770766696894235358159 132065656150045341353037239)
    ·
      refine ⟨198098484225068012029555859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132065656150045341353037239 198098484225068012029555859)
      ·
        refine ⟨297147726337602018044333789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198098484225068012029555859 297147726337602018044333789)
        ·
          refine ⟨111430397376600756766625171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297147726337602018044333789 111430397376600756766625171)
          ·
            refine ⟨167145596064901135149937757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111430397376600756766625171 167145596064901135149937757)
            ·
              refine ⟨62679598524337925681226659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167145596064901135149937757 62679598524337925681226659)
              ·
                refine ⟨94019397786506888521839989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62679598524337925681226659 94019397786506888521839989)
                ·
                  refine ⟨8814318542485020798922499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94019397786506888521839989 8814318542485020798922499)
                  ·
                    refine ⟨13221477813727531198383749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8814318542485020798922499 13221477813727531198383749)
                    ·
                      refine ⟨2479027090073912099696953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13221477813727531198383749 2479027090073912099696953)
                      ·
                        rfl

theorem cell23_4827888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 4].length) (baseStart_4827888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827888 prefixEnd_4827888 := by exact prefixLift 4827888
  have htrace : WordTrace (prefixWord ++ tailWord_4827888) baseStart_4827888 baseEnd_4827888 := by
    simpa [prefixWord, tailWord_4827888, baseEnd_4827888] using wordTrace_append hprefix tailTrace_4827888
  have hstable : (prefixWord ++ tailWord_4827888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827888).length < 2 ^ (prefixWord ++ tailWord_4827888).sum := by decide
  have hdescent : baseEnd_4827888 < baseStart_4827888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827898 : List Nat := [3, 1, 1, 1, 1, 3, 3, 3, 1, 6]
def baseStart_4827898 : Nat := 118140960795 + 4827898 * 2 ^ 59
def prefixEnd_4827898 : Nat := 4983230072969 + 3 ^ 40 * 4827898 * 2
def baseEnd_4827898 : Nat := 826344074960152353523969

theorem tailTrace_4827898 : CollatzResearch.WordTrace tailWord_4827898 prefixEnd_4827898 826344074960152353523969 := by
  unfold tailWord_4827898
  simp only [CollatzResearch.WordTrace]
  refine ⟨44021976565839390044645087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117391937508905040119053565 44021976565839390044645087)
  ·
    refine ⟨66032964848759085066967631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44021976565839390044645087 66032964848759085066967631)
    ·
      refine ⟨99049447273138627600451447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66032964848759085066967631 99049447273138627600451447)
      ·
        refine ⟨148574170909707941400677171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99049447273138627600451447 148574170909707941400677171)
        ·
          refine ⟨222861256364561912101015757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148574170909707941400677171 222861256364561912101015757)
          ·
            refine ⟨83572971136710717037880909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222861256364561912101015757 83572971136710717037880909)
            ·
              refine ⟨31339864176266518889205341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83572971136710717037880909 31339864176266518889205341)
              ·
                refine ⟨11752449066099944583452003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31339864176266518889205341 11752449066099944583452003)
                ·
                  refine ⟨17628673599149916875178005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11752449066099944583452003 17628673599149916875178005)
                  ·
                    refine ⟨826344074960152353523969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17628673599149916875178005 826344074960152353523969)
                    ·
                      rfl

theorem cell23_4827898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_4827898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827898 prefixEnd_4827898 := by exact prefixLift 4827898
  have htrace : WordTrace (prefixWord ++ tailWord_4827898) baseStart_4827898 baseEnd_4827898 := by
    simpa [prefixWord, tailWord_4827898, baseEnd_4827898] using wordTrace_append hprefix tailTrace_4827898
  have hstable : (prefixWord ++ tailWord_4827898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827898).length < 2 ^ (prefixWord ++ tailWord_4827898).sum := by decide
  have hdescent : baseEnd_4827898 < baseStart_4827898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827905 : List Nat := [1, 2, 4, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_4827905 : Nat := 118140960795 + 4827905 * 2 ^ 59
def prefixEnd_4827905 : Nat := 4983230072969 + 3 ^ 40 * 4827905 * 2
def baseEnd_4827905 : Nat := 2479035819245038533184375

theorem tailTrace_4827905 : CollatzResearch.WordTrace tailWord_4827905 prefixEnd_4827905 2479035819245038533184375 := by
  unfold tailWord_4827905
  simp only [CollatzResearch.WordTrace]
  refine ⟨176088161574332200374085169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117392107716221466916056779 176088161574332200374085169)
  ·
    refine ⟨132066121180749150280563877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176088161574332200374085169 132066121180749150280563877)
    ·
      refine ⟨24762397721390465677605727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132066121180749150280563877 24762397721390465677605727)
      ·
        refine ⟨37143596582085698516408591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24762397721390465677605727 37143596582085698516408591)
        ·
          refine ⟨55715394873128547774612887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37143596582085698516408591 55715394873128547774612887)
          ·
            refine ⟨83573092309692821661919331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55715394873128547774612887 83573092309692821661919331)
            ·
              refine ⟨125359638464539232492878997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83573092309692821661919331 125359638464539232492878997)
              ·
                refine ⟨5876233053025276523103703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 125359638464539232492878997 5876233053025276523103703)
                ·
                  refine ⟨8814349579537914784655555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5876233053025276523103703 8814349579537914784655555)
                  ·
                    refine ⟨13221524369306872176983333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8814349579537914784655555 13221524369306872176983333)
                    ·
                      refine ⟨2479035819245038533184375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13221524369306872176983333 2479035819245038533184375)
                      ·
                        rfl

theorem cell23_4827905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_4827905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827905 prefixEnd_4827905 := by exact prefixLift 4827905
  have htrace : WordTrace (prefixWord ++ tailWord_4827905) baseStart_4827905 baseEnd_4827905 := by
    simpa [prefixWord, tailWord_4827905, baseEnd_4827905] using wordTrace_append hprefix tailTrace_4827905
  have hstable : (prefixWord ++ tailWord_4827905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827905).length < 2 ^ (prefixWord ++ tailWord_4827905).sum := by decide
  have hdescent : baseEnd_4827905 < baseStart_4827905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827918 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_4827918 : Nat := 118140960795 + 4827918 * 2 ^ 59
def prefixEnd_4827918 : Nat := 4983230072969 + 3 ^ 40 * 4827918 * 2
def baseEnd_4827918 : Nat := 2479042494493546982321815

theorem tailTrace_4827918 : CollatzResearch.WordTrace tailWord_4827918 prefixEnd_4827918 2479042494493546982321815 := by
  unfold tailWord_4827918
  simp only [CollatzResearch.WordTrace]
  refine ⟨22011079465410637949288551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117392423815523402396205605 22011079465410637949288551)
  ·
    refine ⟨33016619198115956923932827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22011079465410637949288551 33016619198115956923932827)
    ·
      refine ⟨49524928797173935385899241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33016619198115956923932827 49524928797173935385899241)
      ·
        refine ⟨37143696597880451539424431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49524928797173935385899241 37143696597880451539424431)
        ·
          refine ⟨55715544896820677309136647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37143696597880451539424431 55715544896820677309136647)
          ·
            refine ⟨83573317345231015963704971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55715544896820677309136647 83573317345231015963704971)
            ·
              refine ⟨125359976017846523945557457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83573317345231015963704971 125359976017846523945557457)
              ·
                refine ⟨94019982013384892959168093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125359976017846523945557457 94019982013384892959168093)
                ·
                  refine ⟨35257493255019334859688035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94019982013384892959168093 35257493255019334859688035)
                  ·
                    refine ⟨52886239882529002289532053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35257493255019334859688035 52886239882529002289532053)
                    ·
                      refine ⟨2479042494493546982321815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52886239882529002289532053 2479042494493546982321815)
                      ·
                        rfl

theorem cell23_4827918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_4827918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827918 prefixEnd_4827918 := by exact prefixLift 4827918
  have htrace : WordTrace (prefixWord ++ tailWord_4827918) baseStart_4827918 baseEnd_4827918 := by
    simpa [prefixWord, tailWord_4827918, baseEnd_4827918] using wordTrace_append hprefix tailTrace_4827918
  have hstable : (prefixWord ++ tailWord_4827918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827918).length < 2 ^ (prefixWord ++ tailWord_4827918).sum := by decide
  have hdescent : baseEnd_4827918 < baseStart_4827918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827932 : List Nat := [2, 2, 3, 1, 1, 3, 3, 2, 2, 4]
def baseStart_4827932 : Nat := 118140960795 + 4827932 * 2 ^ 59
def prefixEnd_4827932 : Nat := 4983230072969 + 3 ^ 40 * 4827932 * 2
def baseEnd_4827932 : Nat := 826349894407569975848917

theorem tailTrace_4827932 : CollatzResearch.WordTrace tailWord_4827932 prefixEnd_4827932 826349894407569975848917 := by
  unfold tailWord_4827932
  simp only [CollatzResearch.WordTrace]
  refine ⟨88044573172617191992659025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117392764230156255990212033 88044573172617191992659025)
  ·
    refine ⟨66033429879462893994494269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88044573172617191992659025 66033429879462893994494269)
    ·
      refine ⟨24762536204798585247935351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66033429879462893994494269 24762536204798585247935351)
      ·
        refine ⟨37143804307197877871903027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24762536204798585247935351 37143804307197877871903027)
        ·
          refine ⟨55715706460796816807854541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37143804307197877871903027 55715706460796816807854541)
          ·
            refine ⟨20893389922798806302945453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55715706460796816807854541 20893389922798806302945453)
            ·
              refine ⟨7835021221049552363604545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20893389922798806302945453 7835021221049552363604545)
              ·
                refine ⟨5876265915787164272703409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7835021221049552363604545 5876265915787164272703409)
                ·
                  refine ⟨4407199436840373204527557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5876265915787164272703409 4407199436840373204527557)
                  ·
                    refine ⟨826349894407569975848917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4407199436840373204527557 826349894407569975848917)
                    ·
                      rfl

theorem cell23_4827932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_4827932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827932 prefixEnd_4827932 := by exact prefixLift 4827932
  have htrace : WordTrace (prefixWord ++ tailWord_4827932) baseStart_4827932 baseEnd_4827932 := by
    simpa [prefixWord, tailWord_4827932, baseEnd_4827932] using wordTrace_append hprefix tailTrace_4827932
  have hstable : (prefixWord ++ tailWord_4827932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827932).length < 2 ^ (prefixWord ++ tailWord_4827932).sum := by decide
  have hdescent : baseEnd_4827932 < baseStart_4827932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827962 : List Nat := [3, 1, 1, 1, 6, 2, 2, 7]
def baseStart_4827962 : Nat := 118140960795 + 4827962 * 2 ^ 59
def prefixEnd_4827962 : Nat := 4983230072969 + 3 ^ 40 * 4827962 * 2
def baseEnd_4827962 : Nat := 91817225468234992969319

theorem tailTrace_4827962 : CollatzResearch.WordTrace tailWord_4827962 prefixEnd_4827962 91817225468234992969319 := by
  unfold tailWord_4827962
  simp only [CollatzResearch.WordTrace]
  refine ⟨44022560133781424777227535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117393493690083799405940093 44022560133781424777227535)
  ·
    refine ⟨66033840200672137165841303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44022560133781424777227535 66033840200672137165841303)
    ·
      refine ⟨99050760301008205748761955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66033840200672137165841303 99050760301008205748761955)
      ·
        refine ⟨148576140451512308623142933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99050760301008205748761955 148576140451512308623142933)
        ·
          refine ⟨6964506583664639466709825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 148576140451512308623142933 6964506583664639466709825)
          ·
            refine ⟨5223379937748479600032369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6964506583664639466709825 5223379937748479600032369)
            ·
              refine ⟨3917534953311359700024277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5223379937748479600032369 3917534953311359700024277)
              ·
                refine ⟨91817225468234992969319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3917534953311359700024277 91817225468234992969319)
                ·
                  rfl

theorem cell23_4827962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 7].length) (baseStart_4827962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827962 prefixEnd_4827962 := by exact prefixLift 4827962
  have htrace : WordTrace (prefixWord ++ tailWord_4827962) baseStart_4827962 baseEnd_4827962 := by
    simpa [prefixWord, tailWord_4827962, baseEnd_4827962] using wordTrace_append hprefix tailTrace_4827962
  have hstable : (prefixWord ++ tailWord_4827962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827962).length < 2 ^ (prefixWord ++ tailWord_4827962).sum := by decide
  have hdescent : baseEnd_4827962 < baseStart_4827962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828012 : List Nat := [2, 2, 1, 1, 4, 1, 2, 3, 1, 4, 2]
def baseStart_4828012 : Nat := 118140960795 + 4828012 * 2 ^ 59
def prefixEnd_4828012 : Nat := 4983230072969 + 3 ^ 40 * 4828012 * 2
def baseEnd_4828012 : Nat := 2479090761675069614546383

theorem tailTrace_4828012 : CollatzResearch.WordTrace tailWord_4828012 prefixEnd_4828012 2479090761675069614546383 := by
  unfold tailWord_4828012
  simp only [CollatzResearch.WordTrace]
  refine ⟨88046032092472278824115145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117394709456629705098820193 88046032092472278824115145)
  ·
    refine ⟨66034524069354209118086359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88046032092472278824115145 66034524069354209118086359)
    ·
      refine ⟨99051786104031313677129539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66034524069354209118086359 99051786104031313677129539)
      ·
        refine ⟨148577679156046970515694309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99051786104031313677129539 148577679156046970515694309)
        ·
          refine ⟨27858314841758806971692683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148577679156046970515694309 27858314841758806971692683)
          ·
            refine ⟨41787472262638210457539025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27858314841758806971692683 41787472262638210457539025)
            ·
              refine ⟨31340604196978657843154269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41787472262638210457539025 31340604196978657843154269)
              ·
                refine ⟨11752726573866996691182851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31340604196978657843154269 11752726573866996691182851)
                ·
                  refine ⟨17629089860800495036774277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11752726573866996691182851 17629089860800495036774277)
                  ·
                    refine ⟨3305454348900092819395177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17629089860800495036774277 3305454348900092819395177)
                    ·
                      refine ⟨2479090761675069614546383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3305454348900092819395177 2479090761675069614546383)
                      ·
                        rfl

theorem cell23_4828012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 4, 2].length) (baseStart_4828012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828012 prefixEnd_4828012 := by exact prefixLift 4828012
  have htrace : WordTrace (prefixWord ++ tailWord_4828012) baseStart_4828012 baseEnd_4828012 := by
    simpa [prefixWord, tailWord_4828012, baseEnd_4828012] using wordTrace_append hprefix tailTrace_4828012
  have hstable : (prefixWord ++ tailWord_4828012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828012).length < 2 ^ (prefixWord ++ tailWord_4828012).sum := by decide
  have hdescent : baseEnd_4828012 < baseStart_4828012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828105 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 5, 4, 3]
def baseStart_4828105 : Nat := 118140960795 + 4828105 * 2 ^ 59
def prefixEnd_4828105 : Nat := 4983230072969 + 3 ^ 40 * 4828105 * 2
def baseEnd_4828105 : Nat := 2479138515375937750683455

theorem tailTrace_4828105 : CollatzResearch.WordTrace tailWord_4828105 prefixEnd_4828105 2479138515375937750683455 := by
  unfold tailWord_4828105
  simp only [CollatzResearch.WordTrace]
  refine ⟨176095456173607634531365769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117396970782405089687577179 176095456173607634531365769)
  ·
    refine ⟨132071592130205725898524327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176095456173607634531365769 132071592130205725898524327)
    ·
      refine ⟨198107388195308588847786491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132071592130205725898524327 198107388195308588847786491)
      ·
        refine ⟨297161082292962883271679737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198107388195308588847786491 297161082292962883271679737)
        ·
          refine ⟨222870811719722162453759803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297161082292962883271679737 222870811719722162453759803)
          ·
            refine ⟨334306217579583243680639705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222870811719722162453759803 334306217579583243680639705)
            ·
              refine ⟨250729663184687432760479779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334306217579583243680639705 250729663184687432760479779)
              ·
                refine ⟨376094494777031149140719669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250729663184687432760479779 376094494777031149140719669)
                ·
                  refine ⟨35258858885346670231942469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 376094494777031149140719669 35258858885346670231942469)
                  ·
                    refine ⟨6611036041002500668489213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35258858885346670231942469 6611036041002500668489213)
                    ·
                      refine ⟨2479138515375937750683455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6611036041002500668489213 2479138515375937750683455)
                      ·
                        rfl

theorem cell23_4828105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 4, 3].length) (baseStart_4828105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828105 prefixEnd_4828105 := by exact prefixLift 4828105
  have htrace : WordTrace (prefixWord ++ tailWord_4828105) baseStart_4828105 baseEnd_4828105 := by
    simpa [prefixWord, tailWord_4828105, baseEnd_4828105] using wordTrace_append hprefix tailTrace_4828105
  have hstable : (prefixWord ++ tailWord_4828105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828105).length < 2 ^ (prefixWord ++ tailWord_4828105).sum := by decide
  have hdescent : baseEnd_4828105 < baseStart_4828105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828122 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3]
def baseStart_4828122 : Nat := 118140960795 + 4828122 * 2 ^ 59
def prefixEnd_4828122 : Nat := 4983230072969 + 3 ^ 40 * 4828122 * 2
def baseEnd_4828122 : Nat := 2479147244547064184170877

theorem tailTrace_4828122 : CollatzResearch.WordTrace tailWord_4828122 prefixEnd_4828122 2479147244547064184170877 := by
  unfold tailWord_4828122
  simp only [CollatzResearch.WordTrace]
  refine ⟨44024019053636511608683655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117397384143030697623156413 44024019053636511608683655)
  ·
    refine ⟨66036028580454767413025483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44024019053636511608683655 66036028580454767413025483)
    ·
      refine ⟨99054042870682151119538225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66036028580454767413025483 99054042870682151119538225)
      ·
        refine ⟨74290532153011613339653669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99054042870682151119538225 74290532153011613339653669)
        ·
          refine ⟨13929474778689677501185063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74290532153011613339653669 13929474778689677501185063)
          ·
            refine ⟨20894212168034516251777595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13929474778689677501185063 20894212168034516251777595)
            ·
              refine ⟨31341318252051774377666393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20894212168034516251777595 31341318252051774377666393)
              ·
                refine ⟨23505988689038830783249795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31341318252051774377666393 23505988689038830783249795)
                ·
                  refine ⟨35258983033558246174874693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23505988689038830783249795 35258983033558246174874693)
                  ·
                    refine ⟨6611059318792171157789005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35258983033558246174874693 6611059318792171157789005)
                    ·
                      refine ⟨2479147244547064184170877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6611059318792171157789005 2479147244547064184170877)
                      ·
                        rfl

theorem cell23_4828122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_4828122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828122 prefixEnd_4828122 := by exact prefixLift 4828122
  have htrace : WordTrace (prefixWord ++ tailWord_4828122) baseStart_4828122 baseEnd_4828122 := by
    simpa [prefixWord, tailWord_4828122, baseEnd_4828122] using wordTrace_append hprefix tailTrace_4828122
  have hstable : (prefixWord ++ tailWord_4828122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828122).length < 2 ^ (prefixWord ++ tailWord_4828122).sum := by decide
  have hdescent : baseEnd_4828122 < baseStart_4828122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828155 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 5, 5]
def baseStart_4828155 : Nat := 118140960795 + 4828155 * 2 ^ 59
def prefixEnd_4828155 : Nat := 4983230072969 + 3 ^ 40 * 4828155 * 2
def baseEnd_4828155 : Nat := 826388063136220851686075

theorem tailTrace_4828155 : CollatzResearch.WordTrace tailWord_4828155 prefixEnd_4828155 826388063136220851686075 := by
  unfold tailWord_4828155
  simp only [CollatzResearch.WordTrace]
  refine ⟨176097279823426493070685919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117398186548950995380457279 176097279823426493070685919)
  ·
    refine ⟨264145919735139739606028879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176097279823426493070685919 264145919735139739606028879)
    ·
      refine ⟨396218879602709609409043319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264145919735139739606028879 396218879602709609409043319)
      ·
        refine ⟨594328319404064414113564979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396218879602709609409043319 594328319404064414113564979)
        ·
          refine ⟨891492479106096621170347469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 594328319404064414113564979 891492479106096621170347469)
          ·
            refine ⟨334309679664786232938880301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 891492479106096621170347469 334309679664786232938880301)
            ·
              refine ⟨125366129874294837352080113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 334309679664786232938880301 125366129874294837352080113)
              ·
                refine ⟨94024597405721128014060085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125366129874294837352080113 94024597405721128014060085)
                ·
                  refine ⟨8814806006786355751318133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94024597405721128014060085 8814806006786355751318133)
                  ·
                    refine ⟨826388063136220851686075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8814806006786355751318133 826388063136220851686075)
                    ·
                      rfl

theorem cell23_4828155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 5].length) (baseStart_4828155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828155 prefixEnd_4828155 := by exact prefixLift 4828155
  have htrace : WordTrace (prefixWord ++ tailWord_4828155) baseStart_4828155 baseEnd_4828155 := by
    simpa [prefixWord, tailWord_4828155, baseEnd_4828155] using wordTrace_append hprefix tailTrace_4828155
  have hstable : (prefixWord ++ tailWord_4828155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828155).length < 2 ^ (prefixWord ++ tailWord_4828155).sum := by decide
  have hdescent : baseEnd_4828155 < baseStart_4828155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828189 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 3, 5]
def baseStart_4828189 : Nat := 118140960795 + 4828189 * 2 ^ 59
def prefixEnd_4828189 : Nat := 4983230072969 + 3 ^ 40 * 4828189 * 2
def baseEnd_4828189 : Nat := 826393882583638474011023

theorem tailTrace_4828189 : CollatzResearch.WordTrace tailWord_4828189 prefixEnd_4828189 826393882583638474011023 := by
  unfold tailWord_4828189
  simp only [CollatzResearch.WordTrace]
  refine ⟨176098519905303316877423621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117399013270202211251615747 176098519905303316877423621)
  ·
    refine ⟨33018472482244371914516929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176098519905303316877423621 33018472482244371914516929)
    ·
      refine ⟨24763854361683278935887697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33018472482244371914516929 24763854361683278935887697)
      ·
        refine ⟨18572890771262459201915773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24763854361683278935887697 18572890771262459201915773)
        ·
          refine ⟨6964834039223422200718415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18572890771262459201915773 6964834039223422200718415)
          ·
            refine ⟨10447251058835133301077623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6964834039223422200718415 10447251058835133301077623)
            ·
              refine ⟨15670876588252699951616435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10447251058835133301077623 15670876588252699951616435)
              ·
                refine ⟨23506314882379049927424653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15670876588252699951616435 23506314882379049927424653)
                ·
                  refine ⟨8814868080892143722784245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23506314882379049927424653 8814868080892143722784245)
                  ·
                    refine ⟨826393882583638474011023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8814868080892143722784245 826393882583638474011023)
                    ·
                      rfl

theorem cell23_4828189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_4828189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828189 prefixEnd_4828189 := by exact prefixLift 4828189
  have htrace : WordTrace (prefixWord ++ tailWord_4828189) baseStart_4828189 baseEnd_4828189 := by
    simpa [prefixWord, tailWord_4828189, baseEnd_4828189] using wordTrace_append hprefix tailTrace_4828189
  have hstable : (prefixWord ++ tailWord_4828189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828189).length < 2 ^ (prefixWord ++ tailWord_4828189).sum := by decide
  have hdescent : baseEnd_4828189 < baseStart_4828189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828196 : List Nat := [2, 3, 1, 4, 1, 1, 1, 3, 2, 3, 2]
def baseStart_4828196 : Nat := 118140960795 + 4828196 * 2 ^ 59
def prefixEnd_4828196 : Nat := 4983230072969 + 3 ^ 40 * 4828196 * 2
def baseEnd_4828196 : Nat := 2479185242115496894645537

theorem tailTrace_4828196 : CollatzResearch.WordTrace tailWord_4828196 prefixEnd_4828196 2479185242115496894645537 := by
  unfold tailWord_4828196
  simp only [CollatzResearch.WordTrace]
  refine ⟨88049387608138978536464221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117399183477518638048618961 88049387608138978536464221)
  ·
    refine ⟨33018520353052116951174083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88049387608138978536464221 33018520353052116951174083)
    ·
      refine ⟨49527780529578175426761125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33018520353052116951174083 49527780529578175426761125)
      ·
        refine ⟨9286458849295907892517711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49527780529578175426761125 9286458849295907892517711)
        ·
          refine ⟨13929688273943861838776567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9286458849295907892517711 13929688273943861838776567)
          ·
            refine ⟨20894532410915792758164851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13929688273943861838776567 20894532410915792758164851)
            ·
              refine ⟨31341798616373689137247277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20894532410915792758164851 31341798616373689137247277)
              ·
                refine ⟨11753174481140133426467729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31341798616373689137247277 11753174481140133426467729)
                ·
                  refine ⟨8814880860855100069850797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11753174481140133426467729 8814880860855100069850797)
                  ·
                    refine ⟨3305580322820662526194049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8814880860855100069850797 3305580322820662526194049)
                    ·
                      refine ⟨2479185242115496894645537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3305580322820662526194049 2479185242115496894645537)
                      ·
                        rfl

theorem cell23_4828196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_4828196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828196 prefixEnd_4828196 := by exact prefixLift 4828196
  have htrace : WordTrace (prefixWord ++ tailWord_4828196) baseStart_4828196 baseEnd_4828196 := by
    simpa [prefixWord, tailWord_4828196, baseEnd_4828196] using wordTrace_append hprefix tailTrace_4828196
  have hstable : (prefixWord ++ tailWord_4828196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828196).length < 2 ^ (prefixWord ++ tailWord_4828196).sum := by decide
  have hdescent : baseEnd_4828196 < baseStart_4828196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828206 : List Nat := [4, 1, 3, 1, 1, 1, 5, 1, 1, 5]
def baseStart_4828206 : Nat := 118140960795 + 4828206 * 2 ^ 59
def prefixEnd_4828206 : Nat := 4983230072969 + 3 ^ 40 * 4828206 * 2
def baseEnd_4828206 : Nat := 826396792307347285173497

theorem tailTrace_4828206 : CollatzResearch.WordTrace tailWord_4828206 prefixEnd_4828206 826396792307347285173497 := by
  unfold tailWord_4828206
  simp only [CollatzResearch.WordTrace]
  refine ⟨22012392493280216097599059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117399426630827819187194981 22012392493280216097599059)
  ·
    refine ⟨33018588739920324146398589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22012392493280216097599059 33018588739920324146398589)
    ·
      refine ⟨12381970777470121554899471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33018588739920324146398589 12381970777470121554899471)
      ·
        refine ⟨18572956166205182332349207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12381970777470121554899471 18572956166205182332349207)
        ·
          refine ⟨27859434249307773498523811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18572956166205182332349207 27859434249307773498523811)
          ·
            refine ⟨41789151373961660247785717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27859434249307773498523811 41789151373961660247785717)
            ·
              refine ⟨3917732941308905648229911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41789151373961660247785717 3917732941308905648229911)
              ·
                refine ⟨5876599411963358472344867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3917732941308905648229911 5876599411963358472344867)
                ·
                  refine ⟨8814899117945037708517301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5876599411963358472344867 8814899117945037708517301)
                  ·
                    refine ⟨826396792307347285173497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8814899117945037708517301 826396792307347285173497)
                    ·
                      rfl

theorem cell23_4828206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_4828206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828206 prefixEnd_4828206 := by exact prefixLift 4828206
  have htrace : WordTrace (prefixWord ++ tailWord_4828206) baseStart_4828206 baseEnd_4828206 := by
    simpa [prefixWord, tailWord_4828206, baseEnd_4828206] using wordTrace_append hprefix tailTrace_4828206
  have hstable : (prefixWord ++ tailWord_4828206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828206).length < 2 ^ (prefixWord ++ tailWord_4828206).sum := by decide
  have hdescent : baseEnd_4828206 < baseStart_4828206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828220 : List Nat := [2, 2, 2, 2, 2, 4, 2, 2, 1, 1, 3]
def baseStart_4828220 : Nat := 118140960795 + 4828220 * 2 ^ 59
def prefixEnd_4828220 : Nat := 4983230072969 + 3 ^ 40 * 4828220 * 2
def baseEnd_4828220 : Nat := 2479197565651204800745427

theorem tailTrace_4828220 : CollatzResearch.WordTrace tailWord_4828220 prefixEnd_4828220 2479197565651204800745427 := by
  unfold tailWord_4828220
  simp only [CollatzResearch.WordTrace]
  refine ⟨88049825284095504585901057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117399767045460672781201409 88049825284095504585901057)
  ·
    refine ⟨66037368963071628439425793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88049825284095504585901057 66037368963071628439425793)
    ·
      refine ⟨49528026722303721329569345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66037368963071628439425793 49528026722303721329569345)
      ·
        refine ⟨37146020041727790997177009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49528026722303721329569345 37146020041727790997177009)
        ·
          refine ⟨27859515031295843247882757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37146020041727790997177009 27859515031295843247882757)
          ·
            refine ⟨5223659068367970608978017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27859515031295843247882757 5223659068367970608978017)
            ·
              refine ⟨3917744301275977956733513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5223659068367970608978017 3917744301275977956733513)
              ·
                refine ⟨2938308225956983467550135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3917744301275977956733513 2938308225956983467550135)
                ·
                  refine ⟨4407462338935475201325203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938308225956983467550135 4407462338935475201325203)
                  ·
                    refine ⟨6611193508403212801987805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4407462338935475201325203 6611193508403212801987805)
                    ·
                      refine ⟨2479197565651204800745427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6611193508403212801987805 2479197565651204800745427)
                      ·
                        rfl

theorem cell23_4828220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_4828220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828220 prefixEnd_4828220 := by exact prefixLift 4828220
  have htrace : WordTrace (prefixWord ++ tailWord_4828220) baseStart_4828220 baseEnd_4828220 := by
    simpa [prefixWord, tailWord_4828220, baseEnd_4828220] using wordTrace_append hprefix tailTrace_4828220
  have hstable : (prefixWord ++ tailWord_4828220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828220).length < 2 ^ (prefixWord ++ tailWord_4828220).sum := by decide
  have hdescent : baseEnd_4828220 < baseStart_4828220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828259 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 4, 1, 3]
def baseStart_4828259 : Nat := 118140960795 + 4828259 * 2 ^ 59
def prefixEnd_4828259 : Nat := 4983230072969 + 3 ^ 40 * 4828259 * 2
def baseEnd_4828259 : Nat := 2479217591396730148157747

theorem tailTrace_4828259 : CollatzResearch.WordTrace tailWord_4828259 prefixEnd_4828259 2479217591396730148157747 := by
  unfold tailWord_4828259
  simp only [CollatzResearch.WordTrace]
  refine ⟨176101073015049718832471831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117400715343366479221647887 176101073015049718832471831)
  ·
    refine ⟨264151609522574578248707747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176101073015049718832471831 264151609522574578248707747)
    ·
      refine ⟨396227414283861867373061621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264151609522574578248707747 396227414283861867373061621)
      ·
        refine ⟨37146320089112050066224527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 396227414283861867373061621 37146320089112050066224527)
        ·
          refine ⟨55719480133668075099336791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37146320089112050066224527 55719480133668075099336791)
          ·
            refine ⟨83579220200502112649005187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55719480133668075099336791 83579220200502112649005187)
            ·
              refine ⟨125368830300753168973507781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83579220200502112649005187 125368830300753168973507781)
              ·
                refine ⟨23506655681391219182532709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125368830300753168973507781 23506655681391219182532709)
                ·
                  refine ⟨4407497940260853596724883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23506655681391219182532709 4407497940260853596724883)
                  ·
                    refine ⟨6611246910391280395087325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4407497940260853596724883 6611246910391280395087325)
                    ·
                      refine ⟨2479217591396730148157747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6611246910391280395087325 2479217591396730148157747)
                      ·
                        rfl

theorem cell23_4828259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_4828259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828259 prefixEnd_4828259 := by exact prefixLift 4828259
  have htrace : WordTrace (prefixWord ++ tailWord_4828259) baseStart_4828259 baseEnd_4828259 := by
    simpa [prefixWord, tailWord_4828259, baseEnd_4828259] using wordTrace_append hprefix tailTrace_4828259
  have hstable : (prefixWord ++ tailWord_4828259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828259).length < 2 ^ (prefixWord ++ tailWord_4828259).sum := by decide
  have hdescent : baseEnd_4828259 < baseStart_4828259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828263 : List Nat := [1, 1, 5, 1, 1, 5, 2, 1, 1, 2, 3]
def baseStart_4828263 : Nat := 118140960795 + 4828263 * 2 ^ 59
def prefixEnd_4828263 : Nat := 4983230072969 + 3 ^ 40 * 4828263 * 2
def baseEnd_4828263 : Nat := 2479219645319348132507729

theorem tailTrace_4828263 : CollatzResearch.WordTrace tailWord_4828263 prefixEnd_4828263 2479219645319348132507729 := by
  unfold tailWord_4828263
  simp only [CollatzResearch.WordTrace]
  refine ⟨176101218907035227515617443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117400812604690151677078295 176101218907035227515617443)
  ·
    refine ⟨264151828360552841273426165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176101218907035227515617443 264151828360552841273426165)
    ·
      refine ⟨24764233908801828869383703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 264151828360552841273426165 24764233908801828869383703)
      ·
        refine ⟨37146350863202743304075555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24764233908801828869383703 37146350863202743304075555)
        ·
          refine ⟨55719526294804114956113333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37146350863202743304075555 55719526294804114956113333)
          ·
            refine ⟨5223705590137885777135625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55719526294804114956113333 5223705590137885777135625)
            ·
              refine ⟨3917779192603414332851719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5223705590137885777135625 3917779192603414332851719)
              ·
                refine ⟨5876668788905121499277579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3917779192603414332851719 5876668788905121499277579)
                ·
                  refine ⟨8815003183357682248916369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5876668788905121499277579 8815003183357682248916369)
                  ·
                    refine ⟨6611252387518261686687277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8815003183357682248916369 6611252387518261686687277)
                    ·
                      refine ⟨2479219645319348132507729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6611252387518261686687277 2479219645319348132507729)
                      ·
                        rfl

theorem cell23_4828263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_4828263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828263 prefixEnd_4828263 := by exact prefixLift 4828263
  have htrace : WordTrace (prefixWord ++ tailWord_4828263) baseStart_4828263 baseEnd_4828263 := by
    simpa [prefixWord, tailWord_4828263, baseEnd_4828263] using wordTrace_append hprefix tailTrace_4828263
  have hstable : (prefixWord ++ tailWord_4828263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828263).length < 2 ^ (prefixWord ++ tailWord_4828263).sum := by decide
  have hdescent : baseEnd_4828263 < baseStart_4828263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828293 : List Nat := [1, 3, 1, 1, 7, 1, 1, 1, 1, 3, 3]
def baseStart_4828293 : Nat := 118140960795 + 4828293 * 2 ^ 59
def prefixEnd_4828293 : Nat := 4983230072969 + 3 ^ 40 * 4828293 * 2
def baseEnd_4828293 : Nat := 2479235049738983015132591

theorem tailTrace_4828293 : CollatzResearch.WordTrace tailWord_4828293 prefixEnd_4828293 2479235049738983015132591 := by
  unfold tailWord_4828293
  simp only [CollatzResearch.WordTrace]
  refine ⟨176102313096926542639209533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117401542064617695092806355 176102313096926542639209533)
  ·
    refine ⟨66038367411347453489703575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176102313096926542639209533 66038367411347453489703575)
    ·
      refine ⟨99057551117021180234555363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66038367411347453489703575 99057551117021180234555363)
      ·
        refine ⟨148586326675531770351833045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99057551117021180234555363 148586326675531770351833045)
        ·
          refine ⟨3482492031457775867621087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 148586326675531770351833045 3482492031457775867621087)
          ·
            refine ⟨5223738047186663801431631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3482492031457775867621087 5223738047186663801431631)
            ·
              refine ⟨7835607070779995702147447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5223738047186663801431631 7835607070779995702147447)
              ·
                refine ⟨11753410606169993553221171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7835607070779995702147447 11753410606169993553221171)
                ·
                  refine ⟨17630115909254990329831757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11753410606169993553221171 17630115909254990329831757)
                  ·
                    refine ⟨6611293465970621373686909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17630115909254990329831757 6611293465970621373686909)
                    ·
                      refine ⟨2479235049738983015132591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6611293465970621373686909 2479235049738983015132591)
                      ·
                        rfl

theorem cell23_4828293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 1, 3, 3].length) (baseStart_4828293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828293 prefixEnd_4828293 := by exact prefixLift 4828293
  have htrace : WordTrace (prefixWord ++ tailWord_4828293) baseStart_4828293 baseEnd_4828293 := by
    simpa [prefixWord, tailWord_4828293, baseEnd_4828293] using wordTrace_append hprefix tailTrace_4828293
  have hstable : (prefixWord ++ tailWord_4828293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828293).length < 2 ^ (prefixWord ++ tailWord_4828293).sum := by decide
  have hdescent : baseEnd_4828293 < baseStart_4828293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828339 : List Nat := [1, 1, 1, 2, 3, 2, 2, 6, 5]
def baseStart_4828339 : Nat := 118140960795 + 4828339 * 2 ^ 59
def prefixEnd_4828339 : Nat := 4983230072969 + 3 ^ 40 * 4828339 * 2
def baseEnd_4828339 : Nat := 275473185538787759461931

theorem tailTrace_4828339 : CollatzResearch.WordTrace tailWord_4828339 prefixEnd_4828339 275473185538787759461931 := by
  unfold tailWord_4828339
  simp only [CollatzResearch.WordTrace]
  refine ⟨176103990854759892495384071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117402660569839928330256047 176103990854759892495384071)
  ·
    refine ⟨264155986282139838743076107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176103990854759892495384071 264155986282139838743076107)
    ·
      refine ⟨396233979423209758114614161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264155986282139838743076107 396233979423209758114614161)
      ·
        refine ⟨297175484567407318585960621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 396233979423209758114614161 297175484567407318585960621)
        ·
          refine ⟨111440806712777744469735233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297175484567407318585960621 111440806712777744469735233)
          ·
            refine ⟨83580605034583308352301425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111440806712777744469735233 83580605034583308352301425)
            ·
              refine ⟨62685453775937481264226069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83580605034583308352301425 62685453775937481264226069)
              ·
                refine ⟨2938380645747069434260597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62685453775937481264226069 2938380645747069434260597)
                ·
                  refine ⟨275473185538787759461931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2938380645747069434260597 275473185538787759461931)
                  ·
                    rfl

theorem cell23_4828339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 5].length) (baseStart_4828339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828339 prefixEnd_4828339 := by exact prefixLift 4828339
  have htrace : WordTrace (prefixWord ++ tailWord_4828339) baseStart_4828339 baseEnd_4828339 := by
    simpa [prefixWord, tailWord_4828339, baseEnd_4828339] using wordTrace_append hprefix tailTrace_4828339
  have hstable : (prefixWord ++ tailWord_4828339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828339).length < 2 ^ (prefixWord ++ tailWord_4828339).sum := by decide
  have hdescent : baseEnd_4828339 < baseStart_4828339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828349 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 2, 3, 3]
def baseStart_4828349 : Nat := 118140960795 + 4828349 * 2 ^ 59
def prefixEnd_4828349 : Nat := 4983230072969 + 3 ^ 40 * 4828349 * 2
def baseEnd_4828349 : Nat := 2479263804655634796032333

theorem tailTrace_4828349 : CollatzResearch.WordTrace tailWord_4828349 prefixEnd_4828349 2479263804655634796032333 := by
  unfold tailWord_4828349
  simp only [CollatzResearch.WordTrace]
  refine ⟨176104355584723664203248101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117402903723149109468832067 176104355584723664203248101)
  ·
    refine ⟨33019566672135687038109019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176104355584723664203248101 33019566672135687038109019)
    ·
      refine ⟨49529350008203530557163529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33019566672135687038109019 49529350008203530557163529)
      ·
        refine ⟨37147012506152647917872647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49529350008203530557163529 37147012506152647917872647)
        ·
          refine ⟨55720518759228971876808971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37147012506152647917872647 55720518759228971876808971)
          ·
            refine ⟨83580778138843457815213457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55720518759228971876808971 83580778138843457815213457)
            ·
              refine ⟨62685583604132593361410093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83580778138843457815213457 62685583604132593361410093)
              ·
                refine ⟨23507093851549722510528785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62685583604132593361410093 23507093851549722510528785)
                ·
                  refine ⟨17630320388662291882896589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23507093851549722510528785 17630320388662291882896589)
                  ·
                    refine ⟨6611370145748359456086221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17630320388662291882896589 6611370145748359456086221)
                    ·
                      refine ⟨2479263804655634796032333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6611370145748359456086221 2479263804655634796032333)
                      ·
                        rfl

theorem cell23_4828349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_4828349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828349 prefixEnd_4828349 := by exact prefixLift 4828349
  have htrace : WordTrace (prefixWord ++ tailWord_4828349) baseStart_4828349 baseEnd_4828349 := by
    simpa [prefixWord, tailWord_4828349, baseEnd_4828349] using wordTrace_append hprefix tailTrace_4828349
  have hstable : (prefixWord ++ tailWord_4828349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828349).length < 2 ^ (prefixWord ++ tailWord_4828349).sum := by decide
  have hdescent : baseEnd_4828349 < baseStart_4828349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828350 : List Nat := [4, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2]
def baseStart_4828350 : Nat := 118140960795 + 4828350 * 2 ^ 59
def prefixEnd_4828350 : Nat := 4983230072969 + 3 ^ 40 * 4828350 * 2
def baseEnd_4828350 : Nat := 2479264318136289292119829

theorem tailTrace_4828350 : CollatzResearch.WordTrace tailWord_4828350 prefixEnd_4828350 2479264318136289292119829 := by
  unfold tailWord_4828350
  simp only [CollatzResearch.WordTrace]
  refine ⟨22013049007215005171754313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117402928038480027582689669 22013049007215005171754313)
  ·
    refine ⟨16509786755411253878815735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22013049007215005171754313 16509786755411253878815735)
    ·
      refine ⟨24764680133116880818223603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16509786755411253878815735 24764680133116880818223603)
      ·
        refine ⟨37147020199675321227335405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24764680133116880818223603 37147020199675321227335405)
        ·
          refine ⟨13930132574878245460250777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37147020199675321227335405 13930132574878245460250777)
          ·
            refine ⟨10447599431158684095188083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13930132574878245460250777 10447599431158684095188083)
            ·
              refine ⟨15671399146738026142782125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10447599431158684095188083 15671399146738026142782125)
              ·
                refine ⟨5876774680026759803543297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15671399146738026142782125 5876774680026759803543297)
                ·
                  refine ⟨4407581010020069852657473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5876774680026759803543297 4407581010020069852657473)
                  ·
                    refine ⟨3305685757515052389493105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4407581010020069852657473 3305685757515052389493105)
                    ·
                      refine ⟨2479264318136289292119829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3305685757515052389493105 2479264318136289292119829)
                      ·
                        rfl

theorem cell23_4828350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_4828350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828350 prefixEnd_4828350 := by exact prefixLift 4828350
  have htrace : WordTrace (prefixWord ++ tailWord_4828350) baseStart_4828350 baseEnd_4828350 := by
    simpa [prefixWord, tailWord_4828350, baseEnd_4828350] using wordTrace_append hprefix tailTrace_4828350
  have hstable : (prefixWord ++ tailWord_4828350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828350).length < 2 ^ (prefixWord ++ tailWord_4828350).sum := by decide
  have hdescent : baseEnd_4828350 < baseStart_4828350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828354 : List Nat := [3, 5, 1, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_4828354 : Nat := 118140960795 + 4828354 * 2 ^ 59
def prefixEnd_4828354 : Nat := 4983230072969 + 3 ^ 40 * 4828354 * 2
def baseEnd_4828354 : Nat := 2479266372058907276469811

theorem tailTrace_4828354 : CollatzResearch.WordTrace tailWord_4828354 prefixEnd_4828354 2479266372058907276469811 := by
  unfold tailWord_4828354
  simp only [CollatzResearch.WordTrace]
  refine ⟨44026134487426387514295029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117403025299803700038120077 44026134487426387514295029)
  ·
    refine ⟨4127450108196223829465159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44026134487426387514295029 4127450108196223829465159)
    ·
      refine ⟨6191175162294335744197739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4127450108196223829465159 6191175162294335744197739)
      ·
        refine ⟨9286762743441503616296609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6191175162294335744197739 9286762743441503616296609)
        ·
          refine ⟨6965072057581127712222457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9286762743441503616296609 6965072057581127712222457)
          ·
            refine ⟨5223804043185845784166843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6965072057581127712222457 5223804043185845784166843)
            ·
              refine ⟨7835706064778768676250265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5223804043185845784166843 7835706064778768676250265)
              ·
                refine ⟨5876779548584076507187699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7835706064778768676250265 5876779548584076507187699)
                ·
                  refine ⟨8815169322876114760781549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5876779548584076507187699 8815169322876114760781549)
                  ·
                    refine ⟨3305688496078543035293081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8815169322876114760781549 3305688496078543035293081)
                    ·
                      refine ⟨2479266372058907276469811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3305688496078543035293081 2479266372058907276469811)
                      ·
                        rfl

theorem cell23_4828354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_4828354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828354 prefixEnd_4828354 := by exact prefixLift 4828354
  have htrace : WordTrace (prefixWord ++ tailWord_4828354) baseStart_4828354 baseEnd_4828354 := by
    simpa [prefixWord, tailWord_4828354, baseEnd_4828354] using wordTrace_append hprefix tailTrace_4828354
  have hstable : (prefixWord ++ tailWord_4828354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828354).length < 2 ^ (prefixWord ++ tailWord_4828354).sum := by decide
  have hdescent : baseEnd_4828354 < baseStart_4828354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828409 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 1, 4, 3]
def baseStart_4828409 : Nat := 118140960795 + 4828409 * 2 ^ 59
def prefixEnd_4828409 : Nat := 4983230072969 + 3 ^ 40 * 4828409 * 2
def baseEnd_4828409 : Nat := 2479294613494904561282057

theorem tailTrace_4828409 : CollatzResearch.WordTrace tailWord_4828409 prefixEnd_4828409 2479294613494904561282057 := by
  unfold tailWord_4828409
  simp only [CollatzResearch.WordTrace]
  refine ⟨176106543964506294450432281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117404362643004196300288187 176106543964506294450432281)
  ·
    refine ⟨132079907973379720837824211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176106543964506294450432281 132079907973379720837824211)
    ·
      refine ⟨198119861960069581256736317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132079907973379720837824211 198119861960069581256736317)
      ·
        refine ⟨74294948235026092971276119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198119861960069581256736317 74294948235026092971276119)
        ·
          refine ⟨111442422352539139456914179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74294948235026092971276119 111442422352539139456914179)
          ·
            refine ⟨167163633528808709185371269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111442422352539139456914179 167163633528808709185371269)
            ·
              refine ⟨31343181286651632972257113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167163633528808709185371269 31343181286651632972257113)
              ·
                refine ⟨23507385964988724729192835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31343181286651632972257113 23507385964988724729192835)
                ·
                  refine ⟨35261078947483087093789253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23507385964988724729192835 35261078947483087093789253)
                  ·
                    refine ⟨6611452302653078830085485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35261078947483087093789253 6611452302653078830085485)
                    ·
                      refine ⟨2479294613494904561282057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6611452302653078830085485 2479294613494904561282057)
                      ·
                        rfl

theorem cell23_4828409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_4828409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828409 prefixEnd_4828409 := by exact prefixLift 4828409
  have htrace : WordTrace (prefixWord ++ tailWord_4828409) baseStart_4828409 baseEnd_4828409 := by
    simpa [prefixWord, tailWord_4828409, baseEnd_4828409] using wordTrace_append hprefix tailTrace_4828409
  have hstable : (prefixWord ++ tailWord_4828409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828409).length < 2 ^ (prefixWord ++ tailWord_4828409).sum := by decide
  have hdescent : baseEnd_4828409 < baseStart_4828409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828433 : List Nat := [1, 2, 2, 1, 1, 4, 4, 3, 1, 4]
def baseStart_4828433 : Nat := 118140960795 + 4828433 * 2 ^ 59
def prefixEnd_4828433 : Nat := 4983230072969 + 3 ^ 40 * 4828433 * 2
def baseEnd_4828433 : Nat := 826435645676870822460649

theorem tailTrace_4828433 : CollatzResearch.WordTrace tailWord_4828433 prefixEnd_4828433 826435645676870822460649 := by
  unfold tailWord_4828433
  simp only [CollatzResearch.WordTrace]
  refine ⟨176107419316419346549305953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117404946210946231032870635 176107419316419346549305953)
  ·
    refine ⟨132080564487314509911979465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176107419316419346549305953 132080564487314509911979465)
    ·
      refine ⟨99060423365485882433984599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132080564487314509911979465 99060423365485882433984599)
      ·
        refine ⟨148590635048228823650976899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99060423365485882433984599 148590635048228823650976899)
        ·
          refine ⟨222885952572343235476465349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148590635048228823650976899 222885952572343235476465349)
          ·
            refine ⟨41791116107314356651837253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 222885952572343235476465349 41791116107314356651837253)
            ·
              refine ⟨7835834270121441872219485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41791116107314356651837253 7835834270121441872219485)
              ·
                refine ⟨2938437851295540702082307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7835834270121441872219485 2938437851295540702082307)
                ·
                  refine ⟨4407656776943311053123461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938437851295540702082307 4407656776943311053123461)
                  ·
                    refine ⟨826435645676870822460649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4407656776943311053123461 826435645676870822460649)
                    ·
                      rfl

theorem cell23_4828433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 1, 4].length) (baseStart_4828433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828433 prefixEnd_4828433 := by exact prefixLift 4828433
  have htrace : WordTrace (prefixWord ++ tailWord_4828433) baseStart_4828433 baseEnd_4828433 := by
    simpa [prefixWord, tailWord_4828433, baseEnd_4828433] using wordTrace_append hprefix tailTrace_4828433
  have hstable : (prefixWord ++ tailWord_4828433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828433).length < 2 ^ (prefixWord ++ tailWord_4828433).sum := by decide
  have hdescent : baseEnd_4828433 < baseStart_4828433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828476 : List Nat := [2, 2, 2, 2, 1, 3, 1, 4, 1, 5]
def baseStart_4828476 : Nat := 118140960795 + 4828476 * 2 ^ 59
def prefixEnd_4828476 : Nat := 4983230072969 + 3 ^ 40 * 4828476 * 2
def baseEnd_4828476 : Nat := 826443005566251933048083

theorem tailTrace_4828476 : CollatzResearch.WordTrace tailWord_4828476 prefixEnd_4828476 826443005566251933048083 := by
  unfold tailWord_4828476
  simp only [CollatzResearch.WordTrace]
  refine ⟨88054493827631782446560641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117405991770175709928747521 88054493827631782446560641)
  ·
    refine ⟨66040870370723836834920481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88054493827631782446560641 66040870370723836834920481)
    ·
      refine ⟨49530652778042877626190361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66040870370723836834920481 49530652778042877626190361)
      ·
        refine ⟨37147989583532158219642771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49530652778042877626190361 37147989583532158219642771)
        ·
          refine ⟨55721984375298237329464157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37147989583532158219642771 55721984375298237329464157)
          ·
            refine ⟨20895744140736838998549059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55721984375298237329464157 20895744140736838998549059)
            ·
              refine ⟨31343616211105258497823589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20895744140736838998549059 31343616211105258497823589)
              ·
                refine ⟨5876928039582235968341923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31343616211105258497823589 5876928039582235968341923)
                ·
                  refine ⟨8815392059373353952512885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5876928039582235968341923 8815392059373353952512885)
                  ·
                    refine ⟨826443005566251933048083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8815392059373353952512885 826443005566251933048083)
                    ·
                      rfl

theorem cell23_4828476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_4828476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828476 prefixEnd_4828476 := by exact prefixLift 4828476
  have htrace : WordTrace (prefixWord ++ tailWord_4828476) baseStart_4828476 baseEnd_4828476 := by
    simpa [prefixWord, tailWord_4828476, baseEnd_4828476] using wordTrace_append hprefix tailTrace_4828476
  have hstable : (prefixWord ++ tailWord_4828476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828476).length < 2 ^ (prefixWord ++ tailWord_4828476).sum := by decide
  have hdescent : baseEnd_4828476 < baseStart_4828476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828489 : List Nat := [1, 2, 1, 1, 2, 3, 2, 4, 1, 6]
def baseStart_4828489 : Nat := 118140960795 + 4828489 * 2 ^ 59
def prefixEnd_4828489 : Nat := 4983230072969 + 3 ^ 40 * 4828489 * 2
def baseEnd_4828489 : Nat := 826445230649088082760563

theorem tailTrace_4828489 : CollatzResearch.WordTrace tailWord_4828489 prefixEnd_4828489 826445230649088082760563 := by
  unfold tailWord_4828489
  simp only [CollatzResearch.WordTrace]
  refine ⟨176109461804216468113344521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117406307869477645408896347 176109461804216468113344521)
  ·
    refine ⟨132082096353162351085008391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176109461804216468113344521 132082096353162351085008391)
    ·
      refine ⟨198123144529743526627512587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132082096353162351085008391 198123144529743526627512587)
      ·
        refine ⟨297184716794615289941268881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198123144529743526627512587 297184716794615289941268881)
        ·
          refine ⟨222888537595961467455951661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297184716794615289941268881 222888537595961467455951661)
          ·
            refine ⟨83583201598485550295981873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222888537595961467455951661 83583201598485550295981873)
            ·
              refine ⟨62687401198864162721986405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83583201598485550295981873 62687401198864162721986405)
              ·
                refine ⟨11753887724787030510372451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62687401198864162721986405 11753887724787030510372451)
                ·
                  refine ⟨17630831587180545765558677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11753887724787030510372451 17630831587180545765558677)
                  ·
                    refine ⟨826445230649088082760563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17630831587180545765558677 826445230649088082760563)
                    ·
                      rfl

theorem cell23_4828489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 6].length) (baseStart_4828489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828489 prefixEnd_4828489 := by exact prefixLift 4828489
  have htrace : WordTrace (prefixWord ++ tailWord_4828489) baseStart_4828489 baseEnd_4828489 := by
    simpa [prefixWord, tailWord_4828489, baseEnd_4828489] using wordTrace_append hprefix tailTrace_4828489
  have hstable : (prefixWord ++ tailWord_4828489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828489).length < 2 ^ (prefixWord ++ tailWord_4828489).sum := by decide
  have hdescent : baseEnd_4828489 < baseStart_4828489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828496 : List Nat := [2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 4]
def baseStart_4828496 : Nat := 118140960795 + 4828496 * 2 ^ 59
def prefixEnd_4828496 : Nat := 4983230072969 + 3 ^ 40 * 4828496 * 2
def baseEnd_4828496 : Nat := 2479339286311845720894157

theorem tailTrace_4828496 : CollatzResearch.WordTrace tailWord_4828496 prefixEnd_4828496 2479339286311845720894157 := by
  unfold tailWord_4828496
  simp only [CollatzResearch.WordTrace]
  refine ⟨88054858557595554154424671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117406478076794072205899561 88054858557595554154424671)
  ·
    refine ⟨132082287836393331231637007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88054858557595554154424671 132082287836393331231637007)
    ·
      refine ⟨198123431754589996847455511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132082287836393331231637007 198123431754589996847455511)
      ·
        refine ⟨297185147631884995271183267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198123431754589996847455511 297185147631884995271183267)
        ·
          refine ⟨445777721447827492906774901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297185147631884995271183267 445777721447827492906774901)
          ·
            refine ⟨41791661385733827460010147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 445777721447827492906774901 41791661385733827460010147)
            ·
              refine ⟨62687492078600741190015221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41791661385733827460010147 62687492078600741190015221)
              ·
                refine ⟨5876952382368819486563927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62687492078600741190015221 5876952382368819486563927)
                ·
                  refine ⟨8815428573553229229845891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5876952382368819486563927 8815428573553229229845891)
                  ·
                    refine ⟨13223142860329843844768837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8815428573553229229845891 13223142860329843844768837)
                    ·
                      refine ⟨2479339286311845720894157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13223142860329843844768837 2479339286311845720894157)
                      ·
                        rfl

theorem cell23_4828496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 4].length) (baseStart_4828496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828496 prefixEnd_4828496 := by exact prefixLift 4828496
  have htrace : WordTrace (prefixWord ++ tailWord_4828496) baseStart_4828496 baseEnd_4828496 := by
    simpa [prefixWord, tailWord_4828496, baseEnd_4828496] using wordTrace_append hprefix tailTrace_4828496
  have hstable : (prefixWord ++ tailWord_4828496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828496).length < 2 ^ (prefixWord ++ tailWord_4828496).sum := by decide
  have hdescent : baseEnd_4828496 < baseStart_4828496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828506 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 4, 4]
def baseStart_4828506 : Nat := 118140960795 + 4828506 * 2 ^ 59
def prefixEnd_4828506 : Nat := 4983230072969 + 3 ^ 40 * 4828506 * 2
def baseEnd_4828506 : Nat := 826448140372796893923037

theorem tailTrace_4828506 : CollatzResearch.WordTrace tailWord_4828506 prefixEnd_4828506 826448140372796893923037 := by
  unfold tailWord_4828506
  simp only [CollatzResearch.WordTrace]
  refine ⟨44027520461288720004178343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117406721230103253344475581 44027520461288720004178343)
  ·
    refine ⟨66041280691933080006267515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44027520461288720004178343 66041280691933080006267515)
    ·
      refine ⟨99061921037899620009401273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66041280691933080006267515 99061921037899620009401273)
      ·
        refine ⟨74296440778424715007050955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99061921037899620009401273 74296440778424715007050955)
        ·
          refine ⟨111444661167637072510576433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74296440778424715007050955 111444661167637072510576433)
          ·
            refine ⟨83583495875727804382932325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111444661167637072510576433 83583495875727804382932325)
            ·
              refine ⟨15671905476698963321799811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83583495875727804382932325 15671905476698963321799811)
              ·
                refine ⟨23507858215048444982699717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15671905476698963321799811 23507858215048444982699717)
                ·
                  refine ⟨4407723415321583434256197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23507858215048444982699717 4407723415321583434256197)
                  ·
                    refine ⟨826448140372796893923037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4407723415321583434256197 826448140372796893923037)
                    ·
                      rfl

theorem cell23_4828506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_4828506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828506 prefixEnd_4828506 := by exact prefixLift 4828506
  have htrace : WordTrace (prefixWord ++ tailWord_4828506) baseStart_4828506 baseEnd_4828506 := by
    simpa [prefixWord, tailWord_4828506, baseEnd_4828506] using wordTrace_append hprefix tailTrace_4828506
  have hstable : (prefixWord ++ tailWord_4828506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828506).length < 2 ^ (prefixWord ++ tailWord_4828506).sum := by decide
  have hdescent : baseEnd_4828506 < baseStart_4828506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828516 : List Nat := [2, 3, 1, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_4828516 : Nat := 118140960795 + 4828516 * 2 ^ 59
def prefixEnd_4828516 : Nat := 4983230072969 + 3 ^ 40 * 4828516 * 2
def baseEnd_4828516 : Nat := 2479349555924935642644065

theorem tailTrace_4828516 : CollatzResearch.WordTrace tailWord_4828516 prefixEnd_4828516 2479349555924935642644065 := by
  unfold tailWord_4828516
  simp only [CollatzResearch.WordTrace]
  refine ⟨88055223287559325862288701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117406964383412434483051601 88055223287559325862288701)
  ·
    refine ⟨33020708732834747198358263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88055223287559325862288701 33020708732834747198358263)
    ·
      refine ⟨49531063099252120797537395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33020708732834747198358263 49531063099252120797537395)
      ·
        refine ⟨74296594648878181196306093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49531063099252120797537395 74296594648878181196306093)
        ·
          refine ⟨27861222993329317948614785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74296594648878181196306093 27861222993329317948614785)
          ·
            refine ⟨20895917244996988461461089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27861222993329317948614785 20895917244996988461461089)
            ·
              refine ⟨15671937933747741346095817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20895917244996988461461089 15671937933747741346095817)
              ·
                refine ⟨11753953450310806009571863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15671937933747741346095817 11753953450310806009571863)
                ·
                  refine ⟨17630930175466209014357795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11753953450310806009571863 17630930175466209014357795)
                  ·
                    refine ⟨26446395263199313521536693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17630930175466209014357795 26446395263199313521536693)
                    ·
                      refine ⟨2479349555924935642644065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26446395263199313521536693 2479349555924935642644065)
                      ·
                        rfl

theorem cell23_4828516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_4828516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828516 prefixEnd_4828516 := by exact prefixLift 4828516
  have htrace : WordTrace (prefixWord ++ tailWord_4828516) baseStart_4828516 baseEnd_4828516 := by
    simpa [prefixWord, tailWord_4828516, baseEnd_4828516] using wordTrace_append hprefix tailTrace_4828516
  have hstable : (prefixWord ++ tailWord_4828516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828516).length < 2 ^ (prefixWord ++ tailWord_4828516).sum := by decide
  have hdescent : baseEnd_4828516 < baseStart_4828516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828564 : List Nat := [2, 4, 2, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_4828564 : Nat := 118140960795 + 4828564 * 2 ^ 59
def prefixEnd_4828564 : Nat := 4983230072969 + 3 ^ 40 * 4828564 * 2
def baseEnd_4828564 : Nat := 2479374202996351454843845

theorem tailTrace_4828564 : CollatzResearch.WordTrace tailWord_4828564 prefixEnd_4828564 2479374202996351454843845 := by
  unfold tailWord_4828564
  simp only [CollatzResearch.WordTrace]
  refine ⟨88056098639472377961162373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117408131519296503948216497 88056098639472377961162373)
  ·
    refine ⟨16510518494901070867717945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88056098639472377961162373 16510518494901070867717945)
    ·
      refine ⟨12382888871175803150788459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16510518494901070867717945 12382888871175803150788459)
      ·
        refine ⟨18574333306763704726182689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12382888871175803150788459 18574333306763704726182689)
        ·
          refine ⟨13930749980072778544637017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18574333306763704726182689 13930749980072778544637017)
          ·
            refine ⟨10448062485054583908477763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13930749980072778544637017 10448062485054583908477763)
            ·
              refine ⟨15672093727581875862716645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10448062485054583908477763 15672093727581875862716645)
              ·
                refine ⟨2938517573921601724259371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15672093727581875862716645 2938517573921601724259371)
                ·
                  refine ⟨4407776360882402586389057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938517573921601724259371 4407776360882402586389057)
                  ·
                    refine ⟨3305832270661801939791793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4407776360882402586389057 3305832270661801939791793)
                    ·
                      refine ⟨2479374202996351454843845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3305832270661801939791793 2479374202996351454843845)
                      ·
                        rfl

theorem cell23_4828564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_4828564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828564 prefixEnd_4828564 := by exact prefixLift 4828564
  have htrace : WordTrace (prefixWord ++ tailWord_4828564) baseStart_4828564 baseEnd_4828564 := by
    simpa [prefixWord, tailWord_4828564, baseEnd_4828564] using wordTrace_append hprefix tailTrace_4828564
  have hstable : (prefixWord ++ tailWord_4828564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828564).length < 2 ^ (prefixWord ++ tailWord_4828564).sum := by decide
  have hdescent : baseEnd_4828564 < baseStart_4828564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828606 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_4828606 : Nat := 118140960795 + 4828606 * 2 ^ 59
def prefixEnd_4828606 : Nat := 4983230072969 + 3 ^ 40 * 4828606 * 2
def baseEnd_4828606 : Nat := 2479395769183840290518651

theorem tailTrace_4828606 : CollatzResearch.WordTrace tailWord_4828606 prefixEnd_4828606 2479395769183840290518651 := by
  unfold tailWord_4828606
  simp only [CollatzResearch.WordTrace]
  refine ⟨22014216143099074636919209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117409152763195064730235781 22014216143099074636919209)
  ·
    refine ⟨16510662107324305977689407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22014216143099074636919209 16510662107324305977689407)
    ·
      refine ⟨24765993160986458966534111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16510662107324305977689407 24765993160986458966534111)
      ·
        refine ⟨37148989741479688449801167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24765993160986458966534111 37148989741479688449801167)
        ·
          refine ⟨55723484612219532674701751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37148989741479688449801167 55723484612219532674701751)
          ·
            refine ⟨83585226918329299012052627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55723484612219532674701751 83585226918329299012052627)
            ·
              refine ⟨125377840377493948518078941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83585226918329299012052627 125377840377493948518078941)
              ·
                refine ⟨47016690141560230694279603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125377840377493948518078941 47016690141560230694279603)
                ·
                  refine ⟨70525035212340346041419405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47016690141560230694279603 70525035212340346041419405)
                  ·
                    refine ⟨26446888204627629765532277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70525035212340346041419405 26446888204627629765532277)
                    ·
                      refine ⟨2479395769183840290518651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26446888204627629765532277 2479395769183840290518651)
                      ·
                        rfl

theorem cell23_4828606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_4828606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828606 prefixEnd_4828606 := by exact prefixLift 4828606
  have htrace : WordTrace (prefixWord ++ tailWord_4828606) baseStart_4828606 baseEnd_4828606 := by
    simpa [prefixWord, tailWord_4828606, baseEnd_4828606] using wordTrace_append hprefix tailTrace_4828606
  have hstable : (prefixWord ++ tailWord_4828606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828606).length < 2 ^ (prefixWord ++ tailWord_4828606).sum := by decide
  have hdescent : baseEnd_4828606 < baseStart_4828606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828616 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_4828616 : Nat := 118140960795 + 4828616 * 2 ^ 59
def prefixEnd_4828616 : Nat := 4983230072969 + 3 ^ 40 * 4828616 * 2
def baseEnd_4828616 : Nat := 2479400903990385251393605

theorem tailTrace_4828616 : CollatzResearch.WordTrace tailWord_4828616 prefixEnd_4828616 2479400903990385251393605 := by
  unfold tailWord_4828616
  simp only [CollatzResearch.WordTrace]
  refine ⟨88057046937378184401608851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117409395916504245868811801 88057046937378184401608851)
  ·
    refine ⟨132085570406067276602413277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88057046937378184401608851 132085570406067276602413277)
    ·
      refine ⟨49532088902275228725904979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132085570406067276602413277 49532088902275228725904979)
      ·
        refine ⟨74298133353412843088857469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49532088902275228725904979 74298133353412843088857469)
        ·
          refine ⟨27861800007529816158321551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74298133353412843088857469 27861800007529816158321551)
          ·
            refine ⟨41792700011294724237482327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27861800007529816158321551 41792700011294724237482327)
            ·
              refine ⟨62689050016942086356223491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41792700011294724237482327 62689050016942086356223491)
              ·
                refine ⟨94033575025413129534335237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62689050016942086356223491 94033575025413129534335237)
                ·
                  refine ⟨17631295317264961787687857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94033575025413129534335237 17631295317264961787687857)
                  ·
                    refine ⟨13223471487948721340765893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17631295317264961787687857 13223471487948721340765893)
                    ·
                      refine ⟨2479400903990385251393605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13223471487948721340765893 2479400903990385251393605)
                      ·
                        rfl

theorem cell23_4828616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_4828616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828616 prefixEnd_4828616 := by exact prefixLift 4828616
  have htrace : WordTrace (prefixWord ++ tailWord_4828616) baseStart_4828616 baseEnd_4828616 := by
    simpa [prefixWord, tailWord_4828616, baseEnd_4828616] using wordTrace_append hprefix tailTrace_4828616
  have hstable : (prefixWord ++ tailWord_4828616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828616).length < 2 ^ (prefixWord ++ tailWord_4828616).sum := by decide
  have hdescent : baseEnd_4828616 < baseStart_4828616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828637 : List Nat := [1, 4, 3, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_4828637 : Nat := 118140960795 + 4828637 * 2 ^ 59
def prefixEnd_4828637 : Nat := 4983230072969 + 3 ^ 40 * 4828637 * 2
def baseEnd_4828637 : Nat := 2479411687084129669231009

theorem tailTrace_4828637 : CollatzResearch.WordTrace tailWord_4828637 prefixEnd_4828637 2479411687084129669231009 := by
  unfold tailWord_4828637
  simp only [CollatzResearch.WordTrace]
  refine ⟨176114859807680289389732165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117409906538453526259821443 176114859807680289389732165)
  ·
    refine ⟨33021536213940054260574781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176114859807680289389732165 33021536213940054260574781)
    ·
      refine ⟨12383076080227520347715543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33021536213940054260574781 12383076080227520347715543)
      ·
        refine ⟨18574614120341280521573315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12383076080227520347715543 18574614120341280521573315)
        ·
          refine ⟨27861921180511920782359973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18574614120341280521573315 27861921180511920782359973)
          ·
            refine ⟨5224110221345985146692495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27861921180511920782359973 5224110221345985146692495)
            ·
              refine ⟨7836165332018977720038743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5224110221345985146692495 7836165332018977720038743)
              ·
                refine ⟨11754247998028466580058115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7836165332018977720038743 11754247998028466580058115)
                ·
                  refine ⟨17631371997042699870087173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11754247998028466580058115 17631371997042699870087173)
                  ·
                    refine ⟨3305882249445506225641345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17631371997042699870087173 3305882249445506225641345)
                    ·
                      refine ⟨2479411687084129669231009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3305882249445506225641345 2479411687084129669231009)
                      ·
                        rfl

theorem cell23_4828637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_4828637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828637 prefixEnd_4828637 := by exact prefixLift 4828637
  have htrace : WordTrace (prefixWord ++ tailWord_4828637) baseStart_4828637 baseEnd_4828637 := by
    simpa [prefixWord, tailWord_4828637, baseEnd_4828637] using wordTrace_append hprefix tailTrace_4828637
  have hstable : (prefixWord ++ tailWord_4828637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828637).length < 2 ^ (prefixWord ++ tailWord_4828637).sum := by decide
  have hdescent : baseEnd_4828637 < baseStart_4828637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828656 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 1, 7]
def baseStart_4828656 : Nat := 118140960795 + 4828656 * 2 ^ 59
def prefixEnd_4828656 : Nat := 4983230072969 + 3 ^ 40 * 4828656 * 2
def baseEnd_4828656 : Nat := 826473814405521698297807

theorem tailTrace_4828656 : CollatzResearch.WordTrace tailWord_4828656 prefixEnd_4828656 826473814405521698297807 := by
  unfold tailWord_4828656
  simp only [CollatzResearch.WordTrace]
  refine ⟨88057776397305727817336911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117410368529740970423115881 88057776397305727817336911)
  ·
    refine ⟨132086664595958591726005367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88057776397305727817336911 132086664595958591726005367)
    ·
      refine ⟨198129996893937887589008051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132086664595958591726005367 198129996893937887589008051)
      ·
        refine ⟨297194995340906831383512077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198129996893937887589008051 297194995340906831383512077)
        ·
          refine ⟨111448123252840061768817029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297194995340906831383512077 111448123252840061768817029)
          ·
            refine ⟨20896523109907511581653193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111448123252840061768817029 20896523109907511581653193)
            ·
              refine ⟨15672392332430633686239895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20896523109907511581653193 15672392332430633686239895)
              ·
                refine ⟨23508588498645950529359843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15672392332430633686239895 23508588498645950529359843)
                ·
                  refine ⟨35262882747968925794039765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23508588498645950529359843 35262882747968925794039765)
                  ·
                    refine ⟨826473814405521698297807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35262882747968925794039765 826473814405521698297807)
                    ·
                      rfl

theorem cell23_4828656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 1, 7].length) (baseStart_4828656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828656 prefixEnd_4828656 := by exact prefixLift 4828656
  have htrace : WordTrace (prefixWord ++ tailWord_4828656) baseStart_4828656 baseEnd_4828656 := by
    simpa [prefixWord, tailWord_4828656, baseEnd_4828656] using wordTrace_append hprefix tailTrace_4828656
  have hstable : (prefixWord ++ tailWord_4828656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828656).length < 2 ^ (prefixWord ++ tailWord_4828656).sum := by decide
  have hdescent : baseEnd_4828656 < baseStart_4828656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828666 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5]
def baseStart_4828666 : Nat := 118140960795 + 4828666 * 2 ^ 59
def prefixEnd_4828666 : Nat := 4983230072969 + 3 ^ 40 * 4828666 * 2
def baseEnd_4828666 : Nat := 2479426578023110055768375

theorem tailTrace_4828666 : CollatzResearch.WordTrace tailWord_4828666 prefixEnd_4828666 2479426578023110055768375 := by
  unfold tailWord_4828666
  simp only [CollatzResearch.WordTrace]
  refine ⟨44028979381143806835634463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117410611683050151561691901 44028979381143806835634463)
  ·
    refine ⟨66043469071715710253451695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44028979381143806835634463 66043469071715710253451695)
    ·
      refine ⟨99065203607573565380177543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66043469071715710253451695 99065203607573565380177543)
      ·
        refine ⟨148597805411360348070266315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99065203607573565380177543 148597805411360348070266315)
        ·
          refine ⟨222896708117040522105399473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148597805411360348070266315 222896708117040522105399473)
          ·
            refine ⟨167172531087780391579049605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222896708117040522105399473 167172531087780391579049605)
            ·
              refine ⟨31344849578958823421071801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167172531087780391579049605 31344849578958823421071801)
              ·
                refine ⟨23508637184219117565803851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31344849578958823421071801 23508637184219117565803851)
                ·
                  refine ⟨35262955776328676348705777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23508637184219117565803851 35262955776328676348705777)
                  ·
                    refine ⟨26447216832246507261529333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35262955776328676348705777 26447216832246507261529333)
                    ·
                      refine ⟨2479426578023110055768375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26447216832246507261529333 2479426578023110055768375)
                      ·
                        rfl

theorem cell23_4828666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_4828666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828666 prefixEnd_4828666 := by exact prefixLift 4828666
  have htrace : WordTrace (prefixWord ++ tailWord_4828666) baseStart_4828666 baseEnd_4828666 := by
    simpa [prefixWord, tailWord_4828666, baseEnd_4828666] using wordTrace_append hprefix tailTrace_4828666
  have hstable : (prefixWord ++ tailWord_4828666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828666).length < 2 ^ (prefixWord ++ tailWord_4828666).sum := by decide
  have hdescent : baseEnd_4828666 < baseStart_4828666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828683 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 5]
def baseStart_4828683 : Nat := 118140960795 + 4828683 * 2 ^ 59
def prefixEnd_4828683 : Nat := 4983230072969 + 3 ^ 40 * 4828683 * 2
def baseEnd_4828683 : Nat := 2479435307194236489255797

theorem tailTrace_4828683 : CollatzResearch.WordTrace tailWord_4828683 prefixEnd_4828683 2479435307194236489255797 := by
  unfold tailWord_4828683
  simp only [CollatzResearch.WordTrace]
  refine ⟨176116537565513639245906703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117411025043675759497271135 176116537565513639245906703)
  ·
    refine ⟨264174806348270458868860055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176116537565513639245906703 264174806348270458868860055)
    ·
      refine ⟨396262209522405688303290083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264174806348270458868860055 396262209522405688303290083)
      ·
        refine ⟨594393314283608532454935125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396262209522405688303290083 594393314283608532454935125)
        ·
          refine ⟨6965546651761037489706271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 594393314283608532454935125 6965546651761037489706271)
          ·
            refine ⟨10448319977641556234559407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6965546651761037489706271 10448319977641556234559407)
            ·
              refine ⟨15672479966462334351839111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10448319977641556234559407 15672479966462334351839111)
              ·
                refine ⟨23508719949693501527758667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15672479966462334351839111 23508719949693501527758667)
                ·
                  refine ⟨35263079924540252291638001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23508719949693501527758667 35263079924540252291638001)
                  ·
                    refine ⟨26447309943405189218728501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35263079924540252291638001 26447309943405189218728501)
                    ·
                      refine ⟨2479435307194236489255797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26447309943405189218728501 2479435307194236489255797)
                      ·
                        rfl

theorem cell23_4828683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 5].length) (baseStart_4828683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828683 prefixEnd_4828683 := by exact prefixLift 4828683
  have htrace : WordTrace (prefixWord ++ tailWord_4828683) baseStart_4828683 baseEnd_4828683 := by
    simpa [prefixWord, tailWord_4828683, baseEnd_4828683] using wordTrace_append hprefix tailTrace_4828683
  have hstable : (prefixWord ++ tailWord_4828683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828683).length < 2 ^ (prefixWord ++ tailWord_4828683).sum := by decide
  have hdescent : baseEnd_4828683 < baseStart_4828683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828703 : List Nat := [1, 1, 2, 4, 1, 1, 2, 4, 3, 4]
def baseStart_4828703 : Nat := 118140960795 + 4828703 * 2 ^ 59
def prefixEnd_4828703 : Nat := 4983230072969 + 3 ^ 40 * 4828703 * 2
def baseEnd_4828703 : Nat := 826481858935775470335235

theorem tailTrace_4828703 : CollatzResearch.WordTrace tailWord_4828703 prefixEnd_4828703 826481858935775470335235 := by
  unfold tailWord_4828703
  simp only [CollatzResearch.WordTrace]
  refine ⟨176117267025441182661634763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117411511350294121774423175 176117267025441182661634763)
  ·
    refine ⟨264175900538161773992452145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176117267025441182661634763 264175900538161773992452145)
    ·
      refine ⟨198131925403621330494339109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264175900538161773992452145 198131925403621330494339109)
      ·
        refine ⟨37149736013178999467688583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198131925403621330494339109 37149736013178999467688583)
        ·
          refine ⟨55724604019768499201532875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37149736013178999467688583 55724604019768499201532875)
          ·
            refine ⟨83586906029652748802299313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55724604019768499201532875 83586906029652748802299313)
            ·
              refine ⟨62690179522239561601724485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83586906029652748802299313 62690179522239561601724485)
              ·
                refine ⟨11754408660419917800323341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62690179522239561601724485 11754408660419917800323341)
                ·
                  refine ⟨4407903247657469175121253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11754408660419917800323341 4407903247657469175121253)
                  ·
                    refine ⟨826481858935775470335235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4407903247657469175121253 826481858935775470335235)
                    ·
                      rfl

theorem cell23_4828703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 4].length) (baseStart_4828703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828703 prefixEnd_4828703 := by exact prefixLift 4828703
  have htrace : WordTrace (prefixWord ++ tailWord_4828703) baseStart_4828703 baseEnd_4828703 := by
    simpa [prefixWord, tailWord_4828703, baseEnd_4828703] using wordTrace_append hprefix tailTrace_4828703
  have hstable : (prefixWord ++ tailWord_4828703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828703).length < 2 ^ (prefixWord ++ tailWord_4828703).sum := by decide
  have hdescent : baseEnd_4828703 < baseStart_4828703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828720 : List Nat := [2, 1, 1, 1, 2, 3, 1, 7, 1, 4]
def baseStart_4828720 : Nat := 118140960795 + 4828720 * 2 ^ 59
def prefixEnd_4828720 : Nat := 4983230072969 + 3 ^ 40 * 4828720 * 2
def baseEnd_4828720 : Nat := 826484768659484281497709

theorem tailTrace_4828720 : CollatzResearch.WordTrace tailWord_4828720 prefixEnd_4828720 826484768659484281497709 := by
  unfold tailWord_4828720
  simp only [CollatzResearch.WordTrace]
  refine ⟨88058943533189797282501807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117411924710919729710002409 88058943533189797282501807)
  ·
    refine ⟨132088415299784695923752711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88058943533189797282501807 132088415299784695923752711)
    ·
      refine ⟨198132622949677043885629067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132088415299784695923752711 198132622949677043885629067)
      ·
        refine ⟨297198934424515565828443601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198132622949677043885629067 297198934424515565828443601)
        ·
          refine ⟨222899200818386674371332701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297198934424515565828443601 222899200818386674371332701)
          ·
            refine ⟨83587200306895002889249763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222899200818386674371332701 83587200306895002889249763)
            ·
              refine ⟨125380800460342504333874645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83587200306895002889249763 125380800460342504333874645)
              ·
                refine ⟨2938612510789277445325187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 125380800460342504333874645 2938612510789277445325187)
                ·
                  refine ⟨4407918766183916167987781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938612510789277445325187 4407918766183916167987781)
                  ·
                    refine ⟨826484768659484281497709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4407918766183916167987781 826484768659484281497709)
                    ·
                      rfl

theorem cell23_4828720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 1, 4].length) (baseStart_4828720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828720 prefixEnd_4828720 := by exact prefixLift 4828720
  have htrace : WordTrace (prefixWord ++ tailWord_4828720) baseStart_4828720 baseEnd_4828720 := by
    simpa [prefixWord, tailWord_4828720, baseEnd_4828720] using wordTrace_append hprefix tailTrace_4828720
  have hstable : (prefixWord ++ tailWord_4828720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828720).length < 2 ^ (prefixWord ++ tailWord_4828720).sum := by decide
  have hdescent : baseEnd_4828720 < baseStart_4828720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828736 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 6]
def baseStart_4828736 : Nat := 118140960795 + 4828736 * 2 ^ 59
def prefixEnd_4828736 : Nat := 4983230072969 + 3 ^ 40 * 4828736 * 2
def baseEnd_4828736 : Nat := 2479462521668924781893053

theorem tailTrace_4828736 : CollatzResearch.WordTrace tailWord_4828736 prefixEnd_4828736 2479462521668924781893053 := by
  unfold tailWord_4828736
  simp only [CollatzResearch.WordTrace]
  refine ⟨88059235317160814648793031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117412313756214419531724041 88059235317160814648793031)
  ·
    refine ⟨132088852975741221973189547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88059235317160814648793031 132088852975741221973189547)
    ·
      refine ⟨198133279463611832959784321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132088852975741221973189547 198133279463611832959784321)
      ·
        refine ⟨148599959597708874719838241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198133279463611832959784321 148599959597708874719838241)
        ·
          refine ⟨111449969698281656039878681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148599959597708874719838241 111449969698281656039878681)
          ·
            refine ⟨83587477273711242029909011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111449969698281656039878681 83587477273711242029909011)
            ·
              refine ⟨125381215910566863044863517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83587477273711242029909011 125381215910566863044863517)
              ·
                refine ⟨47017955966462573641823819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125381215910566863044863517 47017955966462573641823819)
                ·
                  refine ⟨70526933949693860462735729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47017955966462573641823819 70526933949693860462735729)
                  ·
                    refine ⟨52895200462270395347051797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70526933949693860462735729 52895200462270395347051797)
                    ·
                      refine ⟨2479462521668924781893053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52895200462270395347051797 2479462521668924781893053)
                      ·
                        rfl

theorem cell23_4828736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_4828736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828736 prefixEnd_4828736 := by exact prefixLift 4828736
  have htrace : WordTrace (prefixWord ++ tailWord_4828736) baseStart_4828736 baseEnd_4828736 := by
    simpa [prefixWord, tailWord_4828736, baseEnd_4828736] using wordTrace_append hprefix tailTrace_4828736
  have hstable : (prefixWord ++ tailWord_4828736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828736).length < 2 ^ (prefixWord ++ tailWord_4828736).sum := by decide
  have hdescent : baseEnd_4828736 < baseStart_4828736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828737 : List Nat := [1, 2, 5, 1, 1, 1, 3, 4, 1, 4]
def baseStart_4828737 : Nat := 118140960795 + 4828737 * 2 ^ 59
def prefixEnd_4828737 : Nat := 4983230072969 + 3 ^ 40 * 4828737 * 2
def baseEnd_4828737 : Nat := 826487678383193092660183

theorem tailTrace_4828737 : CollatzResearch.WordTrace tailWord_4828737 prefixEnd_4828737 826487678383193092660183 := by
  unfold tailWord_4828737
  simp only [CollatzResearch.WordTrace]
  refine ⟨176118507107318006468372465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117412338071545337645581643 176118507107318006468372465)
  ·
    refine ⟨132088880330488504851279349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176118507107318006468372465 132088880330488504851279349)
    ·
      refine ⟨12383332530983297329807439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132088880330488504851279349 12383332530983297329807439)
      ·
        refine ⟨18574998796474945994711159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12383332530983297329807439 18574998796474945994711159)
        ·
          refine ⟨27862498194712418992066739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18574998796474945994711159 27862498194712418992066739)
          ·
            refine ⟨41793747292068628488100109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27862498194712418992066739 41793747292068628488100109)
            ·
              refine ⟨15672655234525735683037541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41793747292068628488100109 15672655234525735683037541)
              ·
                refine ⟨2938622856473575440569539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15672655234525735683037541 2938622856473575440569539)
                ·
                  refine ⟨4407934284710363160854309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938622856473575440569539 4407934284710363160854309)
                  ·
                    refine ⟨826487678383193092660183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4407934284710363160854309 826487678383193092660183)
                    ·
                      rfl

theorem cell23_4828737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_4828737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828737 prefixEnd_4828737 := by exact prefixLift 4828737
  have htrace : WordTrace (prefixWord ++ tailWord_4828737) baseStart_4828737 baseEnd_4828737 := by
    simpa [prefixWord, tailWord_4828737, baseEnd_4828737] using wordTrace_append hprefix tailTrace_4828737
  have hstable : (prefixWord ++ tailWord_4828737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828737).length < 2 ^ (prefixWord ++ tailWord_4828737).sum := by decide
  have hdescent : baseEnd_4828737 < baseStart_4828737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828777 : List Nat := [1, 2, 1, 1, 1, 4, 3, 5, 1, 1, 3]
def baseStart_4828777 : Nat := 118140960795 + 4828777 * 2 ^ 59
def prefixEnd_4828777 : Nat := 4983230072969 + 3 ^ 40 * 4828777 * 2
def baseEnd_4828777 : Nat := 2479483574375759121480365

theorem tailTrace_4828777 : CollatzResearch.WordTrace tailWord_4828777 prefixEnd_4828777 2479483574375759121480365 := by
  unfold tailWord_4828777
  simp only [CollatzResearch.WordTrace]
  refine ⟨176119966027173093299828585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117413310684782062199885723 176119966027173093299828585)
  ·
    refine ⟨132089974520379819974871439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176119966027173093299828585 132089974520379819974871439)
    ·
      refine ⟨198134961780569729962307159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132089974520379819974871439 198134961780569729962307159)
      ·
        refine ⟨297202442670854594943460739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198134961780569729962307159 297202442670854594943460739)
        ·
          refine ⟨445803664006281892415191109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297202442670854594943460739 445803664006281892415191109)
          ·
            refine ⟨83588187001177854827848333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 445803664006281892415191109 83588187001177854827848333)
            ·
              refine ⟨31345570125441695560443125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83588187001177854827848333 31345570125441695560443125)
              ·
                refine ⟨2938647199260158958791543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31345570125441695560443125 2938647199260158958791543)
                ·
                  refine ⟨4407970798890238438187315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938647199260158958791543 4407970798890238438187315)
                  ·
                    refine ⟨6611956198335357657280973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4407970798890238438187315 6611956198335357657280973)
                    ·
                      refine ⟨2479483574375759121480365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6611956198335357657280973 2479483574375759121480365)
                      ·
                        rfl

theorem cell23_4828777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 1, 1, 3].length) (baseStart_4828777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828777 prefixEnd_4828777 := by exact prefixLift 4828777
  have htrace : WordTrace (prefixWord ++ tailWord_4828777) baseStart_4828777 baseEnd_4828777 := by
    simpa [prefixWord, tailWord_4828777, baseEnd_4828777] using wordTrace_append hprefix tailTrace_4828777
  have hstable : (prefixWord ++ tailWord_4828777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828777).length < 2 ^ (prefixWord ++ tailWord_4828777).sum := by decide
  have hdescent : baseEnd_4828777 < baseStart_4828777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828810 : List Nat := [3, 1, 2, 3, 2, 1, 3, 1, 1, 6]
def baseStart_4828810 : Nat := 118140960795 + 4828810 * 2 ^ 59
def prefixEnd_4828810 : Nat := 4983230072969 + 3 ^ 40 * 4828810 * 2
def baseEnd_4828810 : Nat := 826500173079119164122571

theorem tailTrace_4828810 : CollatzResearch.WordTrace tailWord_4828810 prefixEnd_4828810 826500173079119164122571 := by
  unfold tailWord_4828810
  simp only [CollatzResearch.WordTrace]
  refine ⟨44030292409013384983944971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117414113090702359957186589 44030292409013384983944971)
  ·
    refine ⟨66045438613520077475917457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44030292409013384983944971 66045438613520077475917457)
    ·
      refine ⟨49534078960140058106938093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66045438613520077475917457 49534078960140058106938093)
      ·
        refine ⟨18575279610052521790101785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49534078960140058106938093 18575279610052521790101785)
        ·
          refine ⟨13931459707539391342576339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18575279610052521790101785 13931459707539391342576339)
          ·
            refine ⟨20897189561309087013864509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13931459707539391342576339 20897189561309087013864509)
            ·
              refine ⟨7836446085490907630199191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20897189561309087013864509 7836446085490907630199191)
              ·
                refine ⟨11754669128236361445298787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7836446085490907630199191 11754669128236361445298787)
                ·
                  refine ⟨17632003692354542167948181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11754669128236361445298787 17632003692354542167948181)
                  ·
                    refine ⟨826500173079119164122571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17632003692354542167948181 826500173079119164122571)
                    ·
                      rfl

theorem cell23_4828810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_4828810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828810 prefixEnd_4828810 := by exact prefixLift 4828810
  have htrace : WordTrace (prefixWord ++ tailWord_4828810) baseStart_4828810 baseEnd_4828810 := by
    simpa [prefixWord, tailWord_4828810, baseEnd_4828810] using wordTrace_append hprefix tailTrace_4828810
  have hstable : (prefixWord ++ tailWord_4828810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828810).length < 2 ^ (prefixWord ++ tailWord_4828810).sum := by decide
  have hdescent : baseEnd_4828810 < baseStart_4828810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828823 : List Nat := [1, 1, 3, 3, 2, 3, 1, 9]
def baseStart_4828823 : Nat := 118140960795 + 4828823 * 2 ^ 59
def prefixEnd_4828823 : Nat := 4983230072969 + 3 ^ 40 * 4828823 * 2
def baseEnd_4828823 : Nat := 91833599795772812648339

theorem tailTrace_4828823 : CollatzResearch.WordTrace tailWord_4828823 prefixEnd_4828823 91833599795772812648339 := by
  unfold tailWord_4828823
  simp only [CollatzResearch.WordTrace]
  refine ⟨176121643785006443156003123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117414429190004295437335415 176121643785006443156003123)
  ·
    refine ⟨264182465677509664734004685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176121643785006443156003123 264182465677509664734004685)
    ·
      refine ⟨99068424629066124275251757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264182465677509664734004685 99068424629066124275251757)
      ·
        refine ⟨37150659235899796603219409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99068424629066124275251757 37150659235899796603219409)
        ·
          refine ⟨27862994426924847452414557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37150659235899796603219409 27862994426924847452414557)
          ·
            refine ⟨10448622910096817794655459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27862994426924847452414557 10448622910096817794655459)
            ·
              refine ⟨15672934365145226691983189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10448622910096817794655459 15672934365145226691983189)
              ·
                refine ⟨91833599795772812648339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15672934365145226691983189 91833599795772812648339)
                ·
                  rfl

theorem cell23_4828823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 9].length) (baseStart_4828823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828823 prefixEnd_4828823 := by exact prefixLift 4828823
  have htrace : WordTrace (prefixWord ++ tailWord_4828823) baseStart_4828823 baseEnd_4828823 := by
    simpa [prefixWord, tailWord_4828823, baseEnd_4828823] using wordTrace_append hprefix tailTrace_4828823
  have hstable : (prefixWord ++ tailWord_4828823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828823).length < 2 ^ (prefixWord ++ tailWord_4828823).sum := by decide
  have hdescent : baseEnd_4828823 < baseStart_4828823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828828 : List Nat := [2, 2, 3, 2, 4, 1, 1, 3, 1, 1, 3]
def baseStart_4828828 : Nat := 118140960795 + 4828828 * 2 ^ 59
def prefixEnd_4828828 : Nat := 4983230072969 + 3 ^ 40 * 4828828 * 2
def baseEnd_4828828 : Nat := 2479509761889138421942631

theorem tailTrace_4828828 : CollatzResearch.WordTrace tailWord_4828828 prefixEnd_4828828 2479509761889138421942631 := by
  unfold tailWord_4828828
  simp only [CollatzResearch.WordTrace]
  refine ⟨88060913074994164504967569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117414550766658886006623425 88060913074994164504967569)
  ·
    refine ⟨66045684806245623378725677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88060913074994164504967569 66045684806245623378725677)
    ·
      refine ⟨24767131802342108767022129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66045684806245623378725677 24767131802342108767022129)
      ·
        refine ⟨18575348851756581575266597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24767131802342108767022129 18575348851756581575266597)
        ·
          refine ⟨3482877909704359045362487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18575348851756581575266597 3482877909704359045362487)
          ·
            refine ⟨5224316864556538568043731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3482877909704359045362487 5224316864556538568043731)
            ·
              refine ⟨7836475296834807852065597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5224316864556538568043731 7836475296834807852065597)
              ·
                refine ⟨2938678236313052944524599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7836475296834807852065597 2938678236313052944524599)
                ·
                  refine ⟨4408017354469579416786899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938678236313052944524599 4408017354469579416786899)
                  ·
                    refine ⟨6612026031704369125180349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4408017354469579416786899 6612026031704369125180349)
                    ·
                      refine ⟨2479509761889138421942631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6612026031704369125180349 2479509761889138421942631)
                      ·
                        rfl

theorem cell23_4828828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_4828828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828828 prefixEnd_4828828 := by exact prefixLift 4828828
  have htrace : WordTrace (prefixWord ++ tailWord_4828828) baseStart_4828828 baseEnd_4828828 := by
    simpa [prefixWord, tailWord_4828828, baseEnd_4828828] using wordTrace_append hprefix tailTrace_4828828
  have hstable : (prefixWord ++ tailWord_4828828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828828).length < 2 ^ (prefixWord ++ tailWord_4828828).sum := by decide
  have hdescent : baseEnd_4828828 < baseStart_4828828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828851 : List Nat := [1, 1, 1, 2, 3, 3, 5, 2, 1, 2, 2]
def baseStart_4828851 : Nat := 118140960795 + 4828851 * 2 ^ 59
def prefixEnd_4828851 : Nat := 4983230072969 + 3 ^ 40 * 4828851 * 2
def baseEnd_4828851 : Nat := 2479521571944191831955025

theorem tailTrace_4828851 : CollatzResearch.WordTrace tailWord_4828851 prefixEnd_4828851 2479521571944191831955025 := by
  unfold tailWord_4828851
  simp only [CollatzResearch.WordTrace]
  refine ⟨176122665028905003938022407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117415110019270002625348271 176122665028905003938022407)
  ·
    refine ⟨264183997543357505907033611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176122665028905003938022407 264183997543357505907033611)
    ·
      refine ⟨396275996315036258860550417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264183997543357505907033611 396275996315036258860550417)
      ·
        refine ⟨297206997236277194145412813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 396275996315036258860550417 297206997236277194145412813)
        ·
          refine ⟨111452623963603947804529805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297206997236277194145412813 111452623963603947804529805)
          ·
            refine ⟨41794733986351480426698677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111452623963603947804529805 41794733986351480426698677)
            ·
              refine ⟨3918256311220451290003001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41794733986351480426698677 3918256311220451290003001)
              ·
                refine ⟨2938692233415338467502251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3918256311220451290003001 2938692233415338467502251)
                ·
                  refine ⟨4408038350123007701253377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938692233415338467502251 4408038350123007701253377)
                  ·
                    refine ⟨3306028762592255775940033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4408038350123007701253377 3306028762592255775940033)
                    ·
                      refine ⟨2479521571944191831955025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3306028762592255775940033 2479521571944191831955025)
                      ·
                        rfl

theorem cell23_4828851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 1, 2, 2].length) (baseStart_4828851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828851 prefixEnd_4828851 := by exact prefixLift 4828851
  have htrace : WordTrace (prefixWord ++ tailWord_4828851) baseStart_4828851 baseEnd_4828851 := by
    simpa [prefixWord, tailWord_4828851, baseEnd_4828851] using wordTrace_append hprefix tailTrace_4828851
  have hstable : (prefixWord ++ tailWord_4828851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828851).length < 2 ^ (prefixWord ++ tailWord_4828851).sum := by decide
  have hdescent : baseEnd_4828851 < baseStart_4828851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828907 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 4, 2, 2]
def baseStart_4828907 : Nat := 118140960795 + 4828907 * 2 ^ 59
def prefixEnd_4828907 : Nat := 4983230072969 + 3 ^ 40 * 4828907 * 2
def baseEnd_4828907 : Nat := 2479550326860843612854767

theorem tailTrace_4828907 : CollatzResearch.WordTrace tailWord_4828907 prefixEnd_4828907 2479550326860843612854767 := by
  unfold tailWord_4828907
  simp only [CollatzResearch.WordTrace]
  refine ⟨176124707516702125502060975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117416471677801417001373983 176124707516702125502060975)
  ·
    refine ⟨264187061275053188253091463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176124707516702125502060975 264187061275053188253091463)
    ·
      refine ⟨396280591912579782379637195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264187061275053188253091463 396280591912579782379637195)
      ·
        refine ⟨594420887868869673569455793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396280591912579782379637195 594420887868869673569455793)
        ·
          refine ⟨445815665901652255177091845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 594420887868869673569455793 445815665901652255177091845)
          ·
            refine ⟨83590437356559797845704721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 445815665901652255177091845 83590437356559797845704721)
            ·
              refine ⟨62692828017419848384278541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83590437356559797845704721 62692828017419848384278541)
              ·
                refine ⟨23509810506532443144104453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62692828017419848384278541 23509810506532443144104453)
                ·
                  refine ⟨4408089469974833089519585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23509810506532443144104453 4408089469974833089519585)
                  ·
                    refine ⟨3306067102481124817139689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4408089469974833089519585 3306067102481124817139689)
                    ·
                      refine ⟨2479550326860843612854767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3306067102481124817139689 2479550326860843612854767)
                      ·
                        rfl

theorem cell23_4828907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 2, 2].length) (baseStart_4828907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828907 prefixEnd_4828907 := by exact prefixLift 4828907
  have htrace : WordTrace (prefixWord ++ tailWord_4828907) baseStart_4828907 baseEnd_4828907 := by
    simpa [prefixWord, tailWord_4828907, baseEnd_4828907] using wordTrace_append hprefix tailTrace_4828907
  have hstable : (prefixWord ++ tailWord_4828907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828907).length < 2 ^ (prefixWord ++ tailWord_4828907).sum := by decide
  have hdescent : baseEnd_4828907 < baseStart_4828907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828910 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_4828910 : Nat := 118140960795 + 4828910 * 2 ^ 59
def prefixEnd_4828910 : Nat := 4983230072969 + 3 ^ 40 * 4828910 * 2
def baseEnd_4828910 : Nat := 2479551867302807101117253

theorem tailTrace_4828910 : CollatzResearch.WordTrace tailWord_4828910 prefixEnd_4828910 2479551867302807101117253 := by
  unfold tailWord_4828910
  simp only [CollatzResearch.WordTrace]
  refine ⟨22015602116961407126802523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117416544623794171342946789 22015602116961407126802523)
  ·
    refine ⟨33023403175442110690203785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22015602116961407126802523 33023403175442110690203785)
    ·
      refine ⟨24767552381581583017652839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33023403175442110690203785 24767552381581583017652839)
      ·
        refine ⟨37151328572372374526479259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24767552381581583017652839 37151328572372374526479259)
        ·
          refine ⟨55726992858558561789718889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37151328572372374526479259 55726992858558561789718889)
          ·
            refine ⟨41795244643918921342289167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55726992858558561789718889 41795244643918921342289167)
            ·
              refine ⟨62692866965878382013433751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41795244643918921342289167 62692866965878382013433751)
              ·
                refine ⟨94039300448817573020150627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62692866965878382013433751 94039300448817573020150627)
                ·
                  refine ⟨141058950673226359530225941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94039300448817573020150627 141058950673226359530225941)
                  ·
                    refine ⟨6612138312807485602979341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 141058950673226359530225941 6612138312807485602979341)
                    ·
                      refine ⟨2479551867302807101117253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6612138312807485602979341 2479551867302807101117253)
                      ·
                        rfl

theorem cell23_4828910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_4828910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828910 prefixEnd_4828910 := by exact prefixLift 4828910
  have htrace : WordTrace (prefixWord ++ tailWord_4828910) baseStart_4828910 baseEnd_4828910 := by
    simpa [prefixWord, tailWord_4828910, baseEnd_4828910] using wordTrace_append hprefix tailTrace_4828910
  have hstable : (prefixWord ++ tailWord_4828910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828910).length < 2 ^ (prefixWord ++ tailWord_4828910).sum := by decide
  have hdescent : baseEnd_4828910 < baseStart_4828910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828924 : List Nat := [2, 2, 2, 1, 3, 1, 1, 5, 2, 2, 2]
def baseStart_4828924 : Nat := 118140960795 + 4828924 * 2 ^ 59
def prefixEnd_4828924 : Nat := 4983230072969 + 3 ^ 40 * 4828924 * 2
def baseEnd_4828924 : Nat := 2479559056031970046342189

theorem tailTrace_4828924 : CollatzResearch.WordTrace tailWord_4828924 prefixEnd_4828924 2479559056031970046342189 := by
  unfold tailWord_4828924
  simp only [CollatzResearch.WordTrace]
  refine ⟨88062663778820268702714913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117416885038427024936953217 88062663778820268702714913)
  ·
    refine ⟨66046997834115201527036185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88062663778820268702714913 66046997834115201527036185)
    ·
      refine ⟨49535248375586401145277139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66046997834115201527036185 49535248375586401145277139)
      ·
        refine ⟨74302872563379601717915709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49535248375586401145277139 74302872563379601717915709)
        ·
          refine ⟨27863577211267350644218391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74302872563379601717915709 27863577211267350644218391)
          ·
            refine ⟨41795365816901025966327587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27863577211267350644218391 41795365816901025966327587)
            ·
              refine ⟨62693048725351538949491381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41795365816901025966327587 62693048725351538949491381)
              ·
                refine ⟨5877473318001706776514817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62693048725351538949491381 5877473318001706776514817)
                ·
                  refine ⟨4408104988501280082386113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5877473318001706776514817 4408104988501280082386113)
                  ·
                    refine ⟨3306078741375960061789585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4408104988501280082386113 3306078741375960061789585)
                    ·
                      refine ⟨2479559056031970046342189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3306078741375960061789585 2479559056031970046342189)
                      ·
                        rfl

theorem cell23_4828924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_4828924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828924 prefixEnd_4828924 := by exact prefixLift 4828924
  have htrace : WordTrace (prefixWord ++ tailWord_4828924) baseStart_4828924 baseEnd_4828924 := by
    simpa [prefixWord, tailWord_4828924, baseEnd_4828924] using wordTrace_append hprefix tailTrace_4828924
  have hstable : (prefixWord ++ tailWord_4828924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828924).length < 2 ^ (prefixWord ++ tailWord_4828924).sum := by decide
  have hdescent : baseEnd_4828924 < baseStart_4828924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828960 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 4, 5]
def baseStart_4828960 : Nat := 118140960795 + 4828960 * 2 ^ 59
def prefixEnd_4828960 : Nat := 4983230072969 + 3 ^ 40 * 4828960 * 2
def baseEnd_4828960 : Nat := 826525847111843968497341

theorem tailTrace_4828960 : CollatzResearch.WordTrace tailWord_4828960 prefixEnd_4828960 826525847111843968497341 := by
  unfold tailWord_4828960
  simp only [CollatzResearch.WordTrace]
  refine ⟨88063320292755057776870167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117417760390340077035826889 88063320292755057776870167)
  ·
    refine ⟨132094980439132586665305251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88063320292755057776870167 132094980439132586665305251)
    ·
      refine ⟨198142470658698879997957877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132094980439132586665305251 198142470658698879997957877)
      ·
        refine ⟨18575856624253019999808551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 198142470658698879997957877 18575856624253019999808551)
        ·
          refine ⟨27863784936379529999712827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18575856624253019999808551 27863784936379529999712827)
          ·
            refine ⟨41795677404569294999569241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27863784936379529999712827 41795677404569294999569241)
            ·
              refine ⟨31346758053426971249676931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41795677404569294999569241 31346758053426971249676931)
              ·
                refine ⟨47020137080140456874515397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31346758053426971249676931 47020137080140456874515397)
                ·
                  refine ⟨8816275702526335663971637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47020137080140456874515397 8816275702526335663971637)
                  ·
                    refine ⟨826525847111843968497341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8816275702526335663971637 826525847111843968497341)
                    ·
                      rfl

theorem cell23_4828960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 4, 5].length) (baseStart_4828960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828960 prefixEnd_4828960 := by exact prefixLift 4828960
  have htrace : WordTrace (prefixWord ++ tailWord_4828960) baseStart_4828960 baseEnd_4828960 := by
    simpa [prefixWord, tailWord_4828960, baseEnd_4828960] using wordTrace_append hprefix tailTrace_4828960
  have hstable : (prefixWord ++ tailWord_4828960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828960).length < 2 ^ (prefixWord ++ tailWord_4828960).sum := by decide
  have hdescent : baseEnd_4828960 < baseStart_4828960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4828998 : List Nat := [6, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_4828998 : Nat := 118140960795 + 4828998 * 2 ^ 59
def prefixEnd_4828998 : Nat := 4983230072969 + 3 ^ 40 * 4828998 * 2
def baseEnd_4828998 : Nat := 275510783733378084090761

theorem tailTrace_4828998 : CollatzResearch.WordTrace tailWord_4828998 prefixEnd_4828998 275510783733378084090761 := by
  unfold tailWord_4828998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5504000829980389001363239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 117418684372914965362415765 5504000829980389001363239)
  ·
    refine ⟨8256001244970583502044859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5504000829980389001363239 8256001244970583502044859)
    ·
      refine ⟨12384001867455875253067289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8256001244970583502044859 12384001867455875253067289)
      ·
        refine ⟨9288001400591906439800467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12384001867455875253067289 9288001400591906439800467)
        ·
          refine ⟨13932002100887859659700701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9288001400591906439800467 13932002100887859659700701)
          ·
            refine ⟨5224500787832947372387763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13932002100887859659700701 5224500787832947372387763)
            ·
              refine ⟨7836751181749421058581645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5224500787832947372387763 7836751181749421058581645)
              ·
                refine ⟨2938781693156032896968117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7836751181749421058581645 2938781693156032896968117)
                ·
                  refine ⟨275510783733378084090761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2938781693156032896968117 275510783733378084090761)
                  ·
                    rfl

theorem cell23_4828998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_4828998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4828998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4828998 prefixEnd_4828998 := by exact prefixLift 4828998
  have htrace : WordTrace (prefixWord ++ tailWord_4828998) baseStart_4828998 baseEnd_4828998 := by
    simpa [prefixWord, tailWord_4828998, baseEnd_4828998] using wordTrace_append hprefix tailTrace_4828998
  have hstable : (prefixWord ++ tailWord_4828998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4828998).length < 2 ^ (prefixWord ++ tailWord_4828998).sum := by decide
  have hdescent : baseEnd_4828998 < baseStart_4828998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4828998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829017 : List Nat := [1, 2, 1, 2, 2, 3, 3, 2, 2, 2, 3]
def baseStart_4829017 : Nat := 118140960795 + 4829017 * 2 ^ 59
def prefixEnd_4829017 : Nat := 4983230072969 + 3 ^ 40 * 4829017 * 2
def baseEnd_4829017 : Nat := 2479606809732838182479261

theorem tailTrace_4829017 : CollatzResearch.WordTrace tailWord_4829017 prefixEnd_4829017 2479606809732838182479261 := by
  unfold tailWord_4829017
  simp only [CollatzResearch.WordTrace]
  refine ⟨176128719546303614288565305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117419146364202409525710203 176128719546303614288565305)
  ·
    refine ⟨132096539659727710716423979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176128719546303614288565305 132096539659727710716423979)
    ·
      refine ⟨198144809489591566074635969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132096539659727710716423979 198144809489591566074635969)
      ·
        refine ⟨148608607117193674555976977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198144809489591566074635969 148608607117193674555976977)
        ·
          refine ⟨111456455337895255916982733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148608607117193674555976977 111456455337895255916982733)
          ·
            refine ⟨41796170751710720968868525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111456455337895255916982733 41796170751710720968868525)
            ·
              refine ⟨15673564031891520363325697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41796170751710720968868525 15673564031891520363325697)
              ·
                refine ⟨11755173023918640272494273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15673564031891520363325697 11755173023918640272494273)
                ·
                  refine ⟨8816379767938980204370705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11755173023918640272494273 8816379767938980204370705)
                  ·
                    refine ⟨6612284825954235153278029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8816379767938980204370705 6612284825954235153278029)
                    ·
                      refine ⟨2479606809732838182479261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6612284825954235153278029 2479606809732838182479261)
                      ·
                        rfl

theorem cell23_4829017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_4829017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829017 prefixEnd_4829017 := by exact prefixLift 4829017
  have htrace : WordTrace (prefixWord ++ tailWord_4829017) baseStart_4829017 baseEnd_4829017 := by
    simpa [prefixWord, tailWord_4829017, baseEnd_4829017] using wordTrace_append hprefix tailTrace_4829017
  have hstable : (prefixWord ++ tailWord_4829017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829017).length < 2 ^ (prefixWord ++ tailWord_4829017).sum := by decide
  have hdescent : baseEnd_4829017 < baseStart_4829017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829024 : List Nat := [2, 1, 1, 3, 3, 4, 1, 1, 3, 4]
def baseStart_4829024 : Nat := 118140960795 + 4829024 * 2 ^ 59
def prefixEnd_4829024 : Nat := 4983230072969 + 3 ^ 40 * 4829024 * 2
def baseEnd_4829024 : Nat := 826536801365806551697243

theorem tailTrace_4829024 : CollatzResearch.WordTrace tailWord_4829024 prefixEnd_4829024 826536801365806551697243 := by
  unfold tailWord_4829024
  simp only [CollatzResearch.WordTrace]
  refine ⟨88064487428639127242035063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117419316571518836322713417 88064487428639127242035063)
  ·
    refine ⟨132096731142958690863052595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88064487428639127242035063 132096731142958690863052595)
    ·
      refine ⟨198145096714438036294578893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132096731142958690863052595 198145096714438036294578893)
      ·
        refine ⟨74304411267914263610467085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198145096714438036294578893 74304411267914263610467085)
        ·
          refine ⟨27864154225467848853925157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74304411267914263610467085 27864154225467848853925157)
          ·
            refine ⟨5224528917275221660110967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27864154225467848853925157 5224528917275221660110967)
            ·
              refine ⟨7836793375912832490166451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5224528917275221660110967 7836793375912832490166451)
              ·
                refine ⟨11755190063869248735249677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7836793375912832490166451 11755190063869248735249677)
                ·
                  refine ⟨4408196273950968275718629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11755190063869248735249677 4408196273950968275718629)
                  ·
                    refine ⟨826536801365806551697243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4408196273950968275718629 826536801365806551697243)
                    ·
                      rfl

theorem cell23_4829024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 3, 4].length) (baseStart_4829024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829024 prefixEnd_4829024 := by exact prefixLift 4829024
  have htrace : WordTrace (prefixWord ++ tailWord_4829024) baseStart_4829024 baseEnd_4829024 := by
    simpa [prefixWord, tailWord_4829024, baseEnd_4829024] using wordTrace_append hprefix tailTrace_4829024
  have hstable : (prefixWord ++ tailWord_4829024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829024).length < 2 ^ (prefixWord ++ tailWord_4829024).sum := by decide
  have hdescent : baseEnd_4829024 < baseStart_4829024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829102 : List Nat := [4, 1, 5, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_4829102 : Nat := 118140960795 + 4829102 * 2 ^ 59
def prefixEnd_4829102 : Nat := 4983230072969 + 3 ^ 40 * 4829102 * 2
def baseEnd_4829102 : Nat := 2479650455588470349916371

theorem tailTrace_4829102 : CollatzResearch.WordTrace tailWord_4829102 prefixEnd_4829102 2479650455588470349916371 := by
  unfold tailWord_4829102
  simp only [CollatzResearch.WordTrace]
  refine ⟨22016477468874459225676195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117421213167330449203606373 22016477468874459225676195)
  ·
    refine ⟨33024716203311688838514293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22016477468874459225676195 33024716203311688838514293)
    ·
      refine ⟨3096067144060470828610715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33024716203311688838514293 3096067144060470828610715)
      ·
        refine ⟨4644100716090706242916073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3096067144060470828610715 4644100716090706242916073)
        ·
          refine ⟨3483075537068029682187055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4644100716090706242916073 3483075537068029682187055)
          ·
            refine ⟨5224613305602044523280583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3483075537068029682187055 5224613305602044523280583)
            ·
              refine ⟨7836919958403066784920875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5224613305602044523280583 7836919958403066784920875)
              ·
                refine ⟨11755379937604600177381313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7836919958403066784920875 11755379937604600177381313)
                ·
                  refine ⟨8816534953203450133035985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11755379937604600177381313 8816534953203450133035985)
                  ·
                    refine ⟨6612401214902587599776989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8816534953203450133035985 6612401214902587599776989)
                    ·
                      refine ⟨2479650455588470349916371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6612401214902587599776989 2479650455588470349916371)
                      ·
                        rfl

theorem cell23_4829102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_4829102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829102 prefixEnd_4829102 := by exact prefixLift 4829102
  have htrace : WordTrace (prefixWord ++ tailWord_4829102) baseStart_4829102 baseEnd_4829102 := by
    simpa [prefixWord, tailWord_4829102, baseEnd_4829102] using wordTrace_append hprefix tailTrace_4829102
  have hstable : (prefixWord ++ tailWord_4829102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829102).length < 2 ^ (prefixWord ++ tailWord_4829102).sum := by decide
  have hdescent : baseEnd_4829102 < baseStart_4829102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829107 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 3]
def baseStart_4829107 : Nat := 118140960795 + 4829107 * 2 ^ 59
def prefixEnd_4829107 : Nat := 4983230072969 + 3 ^ 40 * 4829107 * 2
def baseEnd_4829107 : Nat := 2479653022991742830353847

theorem tailTrace_4829107 : CollatzResearch.WordTrace tailWord_4829107 prefixEnd_4829107 2479653022991742830353847 := by
  unfold tailWord_4829107
  simp only [CollatzResearch.WordTrace]
  refine ⟨176132002115977559659341575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117421334743985039772894383 176132002115977559659341575)
  ·
    refine ⟨264198003173966339489012363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176132002115977559659341575 264198003173966339489012363)
    ·
      refine ⟨396297004760949509233518545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264198003173966339489012363 396297004760949509233518545)
      ·
        refine ⟨297222753570712131925138909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 396297004760949509233518545 297222753570712131925138909)
        ·
          refine ⟨111458532589017049471927091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297222753570712131925138909 111458532589017049471927091)
          ·
            refine ⟨167187798883525574207890637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111458532589017049471927091 167187798883525574207890637)
            ·
              refine ⟨62695424581322090327958989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167187798883525574207890637 62695424581322090327958989)
              ·
                refine ⟨23510784217995783872984621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62695424581322090327958989 23510784217995783872984621)
                ·
                  refine ⟨8816544081748418952369233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23510784217995783872984621 8816544081748418952369233)
                  ·
                    refine ⟨6612408061311314214276925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8816544081748418952369233 6612408061311314214276925)
                    ·
                      refine ⟨2479653022991742830353847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6612408061311314214276925 2479653022991742830353847)
                      ·
                        rfl

theorem cell23_4829107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 3].length) (baseStart_4829107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829107 prefixEnd_4829107 := by exact prefixLift 4829107
  have htrace : WordTrace (prefixWord ++ tailWord_4829107) baseStart_4829107 baseEnd_4829107 := by
    simpa [prefixWord, tailWord_4829107, baseEnd_4829107] using wordTrace_append hprefix tailTrace_4829107
  have hstable : (prefixWord ++ tailWord_4829107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829107).length < 2 ^ (prefixWord ++ tailWord_4829107).sum := by decide
  have hdescent : baseEnd_4829107 < baseStart_4829107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829108 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_4829108 : Nat := 118140960795 + 4829108 * 2 ^ 59
def prefixEnd_4829108 : Nat := 4983230072969 + 3 ^ 40 * 4829108 * 2
def baseEnd_4829108 : Nat := 2479653536472397326441343

theorem tailTrace_4829108 : CollatzResearch.WordTrace tailWord_4829108 prefixEnd_4829108 2479653536472397326441343 := by
  unfold tailWord_4829108
  simp only [CollatzResearch.WordTrace]
  refine ⟨88066019294486968415063989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117421359059315957886751985 88066019294486968415063989)
  ·
    refine ⟨8256189308858153288912249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88066019294486968415063989 8256189308858153288912249)
    ·
      refine ⟨6192141981643614966684187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8256189308858153288912249 6192141981643614966684187)
      ·
        refine ⟨9288212972465422450026281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6192141981643614966684187 9288212972465422450026281)
        ·
          refine ⟨6966159729349066837519711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9288212972465422450026281 6966159729349066837519711)
          ·
            refine ⟨10449239594023600256279567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6966159729349066837519711 10449239594023600256279567)
            ·
              refine ⟨15673859391035400384419351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10449239594023600256279567 15673859391035400384419351)
              ·
                refine ⟨23510789086553100576629027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15673859391035400384419351 23510789086553100576629027)
                ·
                  refine ⟨35266183629829650864943541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23510789086553100576629027 35266183629829650864943541)
                  ·
                    refine ⟨3306204715296529768588457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35266183629829650864943541 3306204715296529768588457)
                    ·
                      refine ⟨2479653536472397326441343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3306204715296529768588457 2479653536472397326441343)
                      ·
                        rfl

theorem cell23_4829108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_4829108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829108 prefixEnd_4829108 := by exact prefixLift 4829108
  have htrace : WordTrace (prefixWord ++ tailWord_4829108) baseStart_4829108 baseEnd_4829108 := by
    simpa [prefixWord, tailWord_4829108, baseEnd_4829108] using wordTrace_append hprefix tailTrace_4829108
  have hstable : (prefixWord ++ tailWord_4829108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829108).length < 2 ^ (prefixWord ++ tailWord_4829108).sum := by decide
  have hdescent : baseEnd_4829108 < baseStart_4829108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829164 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 3, 3, 2]
def baseStart_4829164 : Nat := 118140960795 + 4829164 * 2 ^ 59
def prefixEnd_4829164 : Nat := 4983230072969 + 3 ^ 40 * 4829164 * 2
def baseEnd_4829164 : Nat := 2479682291389049107341085

theorem tailTrace_4829164 : CollatzResearch.WordTrace tailWord_4829164 prefixEnd_4829164 2479682291389049107341085 := by
  unfold tailWord_4829164
  simp only [CollatzResearch.WordTrace]
  refine ⟨88067040538385529197083273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117422720717847372262777697 88067040538385529197083273)
  ·
    refine ⟨66050280403789146897812455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88067040538385529197083273 66050280403789146897812455)
    ·
      refine ⟨99075420605683720346718683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66050280403789146897812455 99075420605683720346718683)
      ·
        refine ⟨148613130908525580520078025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99075420605683720346718683 148613130908525580520078025)
        ·
          refine ⟨111459848181394185390058519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148613130908525580520078025 111459848181394185390058519)
          ·
            refine ⟨167189772272091278085087779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111459848181394185390058519 167189772272091278085087779)
            ·
              refine ⟨250784658408136917127631669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167189772272091278085087779 250784658408136917127631669)
              ·
                refine ⟨23511061725762835980715469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 250784658408136917127631669 23511061725762835980715469)
                ·
                  refine ⟨8816648147161063492768301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23511061725762835980715469 8816648147161063492768301)
                  ·
                    refine ⟨3306243055185398809788113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8816648147161063492768301 3306243055185398809788113)
                    ·
                      refine ⟨2479682291389049107341085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3306243055185398809788113 2479682291389049107341085)
                      ·
                        rfl

theorem cell23_4829164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 3, 2].length) (baseStart_4829164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829164 prefixEnd_4829164 := by exact prefixLift 4829164
  have htrace : WordTrace (prefixWord ++ tailWord_4829164) baseStart_4829164 baseEnd_4829164 := by
    simpa [prefixWord, tailWord_4829164, baseEnd_4829164] using wordTrace_append hprefix tailTrace_4829164
  have hstable : (prefixWord ++ tailWord_4829164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829164).length < 2 ^ (prefixWord ++ tailWord_4829164).sum := by decide
  have hdescent : baseEnd_4829164 < baseStart_4829164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829181 : List Nat := [1, 4, 1, 1, 1, 2, 4, 3, 1, 3, 2]
def baseStart_4829181 : Nat := 118140960795 + 4829181 * 2 ^ 59
def prefixEnd_4829181 : Nat := 4983230072969 + 3 ^ 40 * 4829181 * 2
def baseEnd_4829181 : Nat := 2479691020560175540828507

theorem tailTrace_4829181 : CollatzResearch.WordTrace tailWord_4829181 prefixEnd_4829181 2479691020560175540828507 := by
  unfold tailWord_4829181
  simp only [CollatzResearch.WordTrace]
  refine ⟨176134701117709470297535397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117423134078472980198356931 176134701117709470297535397)
  ·
    refine ⟨33025256459570525680787887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176134701117709470297535397 33025256459570525680787887)
    ·
      refine ⟨49537884689355788521181831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33025256459570525680787887 49537884689355788521181831)
      ·
        refine ⟨74306827034033682781772747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49537884689355788521181831 74306827034033682781772747)
        ·
          refine ⟨111460240551050524172659121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74306827034033682781772747 111460240551050524172659121)
          ·
            refine ⟨83595180413287893129494341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111460240551050524172659121 83595180413287893129494341)
            ·
              refine ⟨15674096327491479961780189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83595180413287893129494341 15674096327491479961780189)
              ·
                refine ⟨5877786122809304985667571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15674096327491479961780189 5877786122809304985667571)
                ·
                  refine ⟨8816679184213957478501357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5877786122809304985667571 8816679184213957478501357)
                  ·
                    refine ⟨3306254694080234054438009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8816679184213957478501357 3306254694080234054438009)
                    ·
                      refine ⟨2479691020560175540828507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3306254694080234054438009 2479691020560175540828507)
                      ·
                        rfl

theorem cell23_4829181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_4829181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829181 prefixEnd_4829181 := by exact prefixLift 4829181
  have htrace : WordTrace (prefixWord ++ tailWord_4829181) baseStart_4829181 baseEnd_4829181 := by
    simpa [prefixWord, tailWord_4829181, baseEnd_4829181] using wordTrace_append hprefix tailTrace_4829181
  have hstable : (prefixWord ++ tailWord_4829181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829181).length < 2 ^ (prefixWord ++ tailWord_4829181).sum := by decide
  have hdescent : baseEnd_4829181 < baseStart_4829181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829205 : List Nat := [1, 3, 2, 1, 5, 2, 2, 1, 2, 1, 3]
def baseStart_4829205 : Nat := 118140960795 + 4829205 * 2 ^ 59
def prefixEnd_4829205 : Nat := 4983230072969 + 3 ^ 40 * 4829205 * 2
def baseEnd_4829205 : Nat := 2479703344095883446928397

theorem tailTrace_4829205 : CollatzResearch.WordTrace tailWord_4829205 prefixEnd_4829205 2479703344095883446928397 := by
  unfold tailWord_4829205
  simp only [CollatzResearch.WordTrace]
  refine ⟨176135576469622522396409069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117423717646415014930939379 176135576469622522396409069)
  ·
    refine ⟨66050841176108445898653401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176135576469622522396409069 66050841176108445898653401)
    ·
      refine ⟨49538130882081334423990051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66050841176108445898653401 49538130882081334423990051)
      ·
        refine ⟨74307196323122001635985077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49538130882081334423990051 74307196323122001635985077)
        ·
          refine ⟨6966299655292687653373601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74307196323122001635985077 6966299655292687653373601)
          ·
            refine ⟨5224724741469515740030201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6966299655292687653373601 5224724741469515740030201)
            ·
              refine ⟨3918543556102136805022651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5224724741469515740030201 3918543556102136805022651)
              ·
                refine ⟨5877815334153205207533977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3918543556102136805022651 5877815334153205207533977)
                ·
                  refine ⟨4408361500614903905650483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5877815334153205207533977 4408361500614903905650483)
                  ·
                    refine ⟨6612542250922355858475725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4408361500614903905650483 6612542250922355858475725)
                    ·
                      refine ⟨2479703344095883446928397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6612542250922355858475725 2479703344095883446928397)
                      ·
                        rfl

theorem cell23_4829205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_4829205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829205 prefixEnd_4829205 := by exact prefixLift 4829205
  have htrace : WordTrace (prefixWord ++ tailWord_4829205) baseStart_4829205 baseEnd_4829205 := by
    simpa [prefixWord, tailWord_4829205, baseEnd_4829205] using wordTrace_append hprefix tailTrace_4829205
  have hstable : (prefixWord ++ tailWord_4829205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829205).length < 2 ^ (prefixWord ++ tailWord_4829205).sum := by decide
  have hdescent : baseEnd_4829205 < baseStart_4829205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829227 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 3]
def baseStart_4829227 : Nat := 118140960795 + 4829227 * 2 ^ 59
def prefixEnd_4829227 : Nat := 4983230072969 + 3 ^ 40 * 4829227 * 2
def baseEnd_4829227 : Nat := 2479714640670282360853295

theorem tailTrace_4829227 : CollatzResearch.WordTrace tailWord_4829227 prefixEnd_4829227 2479714640670282360853295 := by
  unfold tailWord_4829227
  simp only [CollatzResearch.WordTrace]
  refine ⟨176136378875542820153709935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117424252583695213435806623 176136378875542820153709935)
  ·
    refine ⟨264204568313314230230564903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176136378875542820153709935 264204568313314230230564903)
    ·
      refine ⟨396306852469971345345847355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264204568313314230230564903 396306852469971345345847355)
      ·
        refine ⟨594460278704957018018771033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396306852469971345345847355 594460278704957018018771033)
        ·
          refine ⟨445845209028717763514078275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 594460278704957018018771033 445845209028717763514078275)
          ·
            refine ⟨668767813543076645271117413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445845209028717763514078275 668767813543076645271117413)
            ·
              refine ⟨125393965039326870988334515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 668767813543076645271117413 125393965039326870988334515)
              ·
                refine ⟨188090947558990306482501773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125393965039326870988334515 188090947558990306482501773)
                ·
                  refine ⟨70534105334621364930938165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188090947558990306482501773 70534105334621364930938165)
                  ·
                    refine ⟨6612572375120752962275453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70534105334621364930938165 6612572375120752962275453)
                    ·
                      refine ⟨2479714640670282360853295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6612572375120752962275453 2479714640670282360853295)
                      ·
                        rfl

theorem cell23_4829227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 3].length) (baseStart_4829227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829227 prefixEnd_4829227 := by exact prefixLift 4829227
  have htrace : WordTrace (prefixWord ++ tailWord_4829227) baseStart_4829227 baseEnd_4829227 := by
    simpa [prefixWord, tailWord_4829227, baseEnd_4829227] using wordTrace_append hprefix tailTrace_4829227
  have hstable : (prefixWord ++ tailWord_4829227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829227).length < 2 ^ (prefixWord ++ tailWord_4829227).sum := by decide
  have hdescent : baseEnd_4829227 < baseStart_4829227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829244 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 2, 3, 3]
def baseStart_4829244 : Nat := 118140960795 + 4829244 * 2 ^ 59
def prefixEnd_4829244 : Nat := 4983230072969 + 3 ^ 40 * 4829244 * 2
def baseEnd_4829244 : Nat := 2479723369841408794340717

theorem tailTrace_4829244 : CollatzResearch.WordTrace tailWord_4829244 prefixEnd_4829244 2479723369841408794340717 := by
  unfold tailWord_4829244
  simp only [CollatzResearch.WordTrace]
  refine ⟨88068499458240616028539393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117424665944320821371385857 88068499458240616028539393)
  ·
    refine ⟨66051374593680462021404545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88068499458240616028539393 66051374593680462021404545)
    ·
      refine ⟨49538530945260346516053409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66051374593680462021404545 49538530945260346516053409)
      ·
        refine ⟨37153898208945259887040057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49538530945260346516053409 37153898208945259887040057)
        ·
          refine ⟨27865423656708944915280043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37153898208945259887040057 27865423656708944915280043)
          ·
            refine ⟨41798135485063417372920065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27865423656708944915280043 41798135485063417372920065)
            ·
              refine ⟨31348601613797563029690049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41798135485063417372920065 31348601613797563029690049)
              ·
                refine ⟨23511451210348172272267537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31348601613797563029690049 23511451210348172272267537)
                ·
                  refine ⟨17633588407761129204200653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23511451210348172272267537 17633588407761129204200653)
                  ·
                    refine ⟨6612595652910423451575245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17633588407761129204200653 6612595652910423451575245)
                    ·
                      refine ⟨2479723369841408794340717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6612595652910423451575245 2479723369841408794340717)
                      ·
                        rfl

theorem cell23_4829244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_4829244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829244 prefixEnd_4829244 := by exact prefixLift 4829244
  have htrace : WordTrace (prefixWord ++ tailWord_4829244) baseStart_4829244 baseEnd_4829244 := by
    simpa [prefixWord, tailWord_4829244, baseEnd_4829244] using wordTrace_append hprefix tailTrace_4829244
  have hstable : (prefixWord ++ tailWord_4829244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829244).length < 2 ^ (prefixWord ++ tailWord_4829244).sum := by decide
  have hdescent : baseEnd_4829244 < baseStart_4829244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829257 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 1, 2, 5]
def baseStart_4829257 : Nat := 118140960795 + 4829257 * 2 ^ 59
def prefixEnd_4829257 : Nat := 4983230072969 + 3 ^ 40 * 4829257 * 2
def baseEnd_4829257 : Nat := 2479730045089917243478157

theorem tailTrace_4829257 : CollatzResearch.WordTrace tailWord_4829257 prefixEnd_4829257 2479730045089917243478157 := by
  unfold tailWord_4829257
  simp only [CollatzResearch.WordTrace]
  refine ⟨176137473065434135277302025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117424982043622756851534683 176137473065434135277302025)
  ·
    refine ⟨132103104799075601457976519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176137473065434135277302025 132103104799075601457976519)
    ·
      refine ⟨198154657198613402186964779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132103104799075601457976519 198154657198613402186964779)
      ·
        refine ⟨297231985797920103280447169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198154657198613402186964779 297231985797920103280447169)
        ·
          refine ⟨222923989348440077460335377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297231985797920103280447169 222923989348440077460335377)
          ·
            refine ⟨167192992011330058095251533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222923989348440077460335377 167192992011330058095251533)
            ·
              refine ⟨62697372004248771785719325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167192992011330058095251533 62697372004248771785719325)
              ·
                refine ⟨23511514501593289419644747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62697372004248771785719325 23511514501593289419644747)
                ·
                  refine ⟨35267271752389934129467121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23511514501593289419644747 35267271752389934129467121)
                  ·
                    refine ⟨26450453814292450597100341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35267271752389934129467121 26450453814292450597100341)
                    ·
                      refine ⟨2479730045089917243478157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26450453814292450597100341 2479730045089917243478157)
                      ·
                        rfl

theorem cell23_4829257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_4829257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829257 prefixEnd_4829257 := by exact prefixLift 4829257
  have htrace : WordTrace (prefixWord ++ tailWord_4829257) baseStart_4829257 baseEnd_4829257 := by
    simpa [prefixWord, tailWord_4829257, baseEnd_4829257] using wordTrace_append hprefix tailTrace_4829257
  have hstable : (prefixWord ++ tailWord_4829257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829257).length < 2 ^ (prefixWord ++ tailWord_4829257).sum := by decide
  have hdescent : baseEnd_4829257 < baseStart_4829257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829261 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_4829261 : Nat := 118140960795 + 4829261 * 2 ^ 59
def prefixEnd_4829261 : Nat := 4983230072969 + 3 ^ 40 * 4829261 * 2
def baseEnd_4829261 : Nat := 2479732099012535227828139

theorem tailTrace_4829261 : CollatzResearch.WordTrace tailWord_4829261 prefixEnd_4829261 2479732099012535227828139 := by
  unfold tailWord_4829261
  simp only [CollatzResearch.WordTrace]
  refine ⟨176137618957419643960447637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117425079304946429306965091 176137618957419643960447637)
  ·
    refine ⟨8256450888629045810645983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 176137618957419643960447637 8256450888629045810645983)
    ·
      refine ⟨12384676332943568715968975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8256450888629045810645983 12384676332943568715968975)
      ·
        refine ⟨18577014499415353073953463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12384676332943568715968975 18577014499415353073953463)
        ·
          refine ⟨27865521749123029610930195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18577014499415353073953463 27865521749123029610930195)
          ·
            refine ⟨41798282623684544416395293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27865521749123029610930195 41798282623684544416395293)
            ·
              refine ⟨15674355983881704156148235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41798282623684544416395293 15674355983881704156148235)
              ·
                refine ⟨23511533975822556234222353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15674355983881704156148235 23511533975822556234222353)
                ·
                  refine ⟨17633650481866917175666765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23511533975822556234222353 17633650481866917175666765)
                  ·
                    refine ⟨6612618930700093940875037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17633650481866917175666765 6612618930700093940875037)
                    ·
                      refine ⟨2479732099012535227828139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6612618930700093940875037 2479732099012535227828139)
                      ·
                        rfl

theorem cell23_4829261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_4829261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829261 prefixEnd_4829261 := by exact prefixLift 4829261
  have htrace : WordTrace (prefixWord ++ tailWord_4829261) baseStart_4829261 baseEnd_4829261 := by
    simpa [prefixWord, tailWord_4829261, baseEnd_4829261] using wordTrace_append hprefix tailTrace_4829261
  have hstable : (prefixWord ++ tailWord_4829261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829261).length < 2 ^ (prefixWord ++ tailWord_4829261).sum := by decide
  have hdescent : baseEnd_4829261 < baseStart_4829261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829297 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 1, 3, 6]
def baseStart_4829297 : Nat := 118140960795 + 4829297 * 2 ^ 59
def prefixEnd_4829297 : Nat := 4983230072969 + 3 ^ 40 * 4829297 * 2
def baseEnd_4829297 : Nat := 2479750584316097086977973

theorem tailTrace_4829297 : CollatzResearch.WordTrace tailWord_4829297 prefixEnd_4829297 2479750584316097086977973 := by
  unfold tailWord_4829297
  simp only [CollatzResearch.WordTrace]
  refine ⟨176138931985289222108758145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117425954656859481405838763 176138931985289222108758145)
  ·
    refine ⟨132104198988966916581568609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176138931985289222108758145 132104198988966916581568609)
    ·
      refine ⟨99078149241725187436176457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132104198988966916581568609 99078149241725187436176457)
      ·
        refine ⟨74308611931293890577132343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99078149241725187436176457 74308611931293890577132343)
        ·
          refine ⟨111462917896940835865698515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74308611931293890577132343 111462917896940835865698515)
          ·
            refine ⟨167194376845411253798547773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111462917896940835865698515 167194376845411253798547773)
            ·
              refine ⟨62697891317029220174455415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167194376845411253798547773 62697891317029220174455415)
              ·
                refine ⟨94046836975543830261683123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62697891317029220174455415 94046836975543830261683123)
                ·
                  refine ⟨141070255463315745392524685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94046836975543830261683123 141070255463315745392524685)
                  ·
                    refine ⟨52901345798743404522196757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 141070255463315745392524685 52901345798743404522196757)
                    ·
                      refine ⟨2479750584316097086977973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52901345798743404522196757 2479750584316097086977973)
                      ·
                        rfl

theorem cell23_4829297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_4829297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829297 prefixEnd_4829297 := by exact prefixLift 4829297
  have htrace : WordTrace (prefixWord ++ tailWord_4829297) baseStart_4829297 baseEnd_4829297 := by
    simpa [prefixWord, tailWord_4829297, baseEnd_4829297] using wordTrace_append hprefix tailTrace_4829297
  have hstable : (prefixWord ++ tailWord_4829297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829297).length < 2 ^ (prefixWord ++ tailWord_4829297).sum := by decide
  have hdescent : baseEnd_4829297 < baseStart_4829297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829304 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 4, 2, 3]
def baseStart_4829304 : Nat := 118140960795 + 4829304 * 2 ^ 59
def prefixEnd_4829304 : Nat := 4983230072969 + 3 ^ 40 * 4829304 * 2
def baseEnd_4829304 : Nat := 2479754178680678559590441

theorem tailTrace_4829304 : CollatzResearch.WordTrace tailWord_4829304 prefixEnd_4829304 2479754178680678559590441 := by
  unfold tailWord_4829304
  simp only [CollatzResearch.WordTrace]
  refine ⟨88069593648131931152131483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117426124864175908202841977 88069593648131931152131483)
  ·
    refine ⟨132104390472197896728197225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88069593648131931152131483 132104390472197896728197225)
    ·
      refine ⟨99078292854148422546147919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132104390472197896728197225 99078292854148422546147919)
      ·
        refine ⟨148617439281222633819221879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99078292854148422546147919 148617439281222633819221879)
        ·
          refine ⟨222926158921833950728832819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148617439281222633819221879 222926158921833950728832819)
          ·
            refine ⟨334389238382750926093249229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222926158921833950728832819 334389238382750926093249229)
            ·
              refine ⟨125395964393531597284968461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 334389238382750926093249229 125395964393531597284968461)
              ·
                refine ⟨47023486647574348981863173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125395964393531597284968461 47023486647574348981863173)
                ·
                  refine ⟨8816903746420190434099345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47023486647574348981863173 8816903746420190434099345)
                  ·
                    refine ⟨6612677809815142825574509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8816903746420190434099345 6612677809815142825574509)
                    ·
                      refine ⟨2479754178680678559590441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6612677809815142825574509 2479754178680678559590441)
                      ·
                        rfl

theorem cell23_4829304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_4829304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829304 prefixEnd_4829304 := by exact prefixLift 4829304
  have htrace : WordTrace (prefixWord ++ tailWord_4829304) baseStart_4829304 baseEnd_4829304 := by
    simpa [prefixWord, tailWord_4829304, baseEnd_4829304] using wordTrace_append hprefix tailTrace_4829304
  have hstable : (prefixWord ++ tailWord_4829304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829304).length < 2 ^ (prefixWord ++ tailWord_4829304).sum := by decide
  have hdescent : baseEnd_4829304 < baseStart_4829304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829337 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 2, 9]
def baseStart_4829337 : Nat := 118140960795 + 4829337 * 2 ^ 59
def prefixEnd_4829337 : Nat := 4983230072969 + 3 ^ 40 * 4829337 * 2
def baseEnd_4829337 : Nat := 826590374514092310159263

theorem tailTrace_4829337 : CollatzResearch.WordTrace tailWord_4829337 prefixEnd_4829337 826590374514092310159263 := by
  unfold tailWord_4829337
  simp only [CollatzResearch.WordTrace]
  refine ⟨176140390905144308940214265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117426927270096205960142843 176140390905144308940214265)
  ·
    refine ⟨132105293178858231705160699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176140390905144308940214265 132105293178858231705160699)
    ·
      refine ⟨198157939768287347557741049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132105293178858231705160699 198157939768287347557741049)
      ·
        refine ⟨148618454826215510668305787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198157939768287347557741049 148618454826215510668305787)
        ·
          refine ⟨222927682239323266002458681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148618454826215510668305787 222927682239323266002458681)
          ·
            refine ⟨167195761679492449501844011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222927682239323266002458681 167195761679492449501844011)
            ·
              refine ⟨250793642519238674252766017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167195761679492449501844011 250793642519238674252766017)
              ·
                refine ⟨188095231889429005689574513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250793642519238674252766017 188095231889429005689574513)
                ·
                  refine ⟨141071423917071754267180885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188095231889429005689574513 141071423917071754267180885)
                  ·
                    refine ⟨826590374514092310159263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 141071423917071754267180885 826590374514092310159263)
                    ·
                      rfl

theorem cell23_4829337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 9].length) (baseStart_4829337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829337 prefixEnd_4829337 := by exact prefixLift 4829337
  have htrace : WordTrace (prefixWord ++ tailWord_4829337) baseStart_4829337 baseEnd_4829337 := by
    simpa [prefixWord, tailWord_4829337, baseEnd_4829337] using wordTrace_append hprefix tailTrace_4829337
  have hstable : (prefixWord ++ tailWord_4829337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829337).length < 2 ^ (prefixWord ++ tailWord_4829337).sum := by decide
  have hdescent : baseEnd_4829337 < baseStart_4829337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829345 : List Nat := [1, 2, 3, 3, 1, 4, 1, 3, 1, 4]
def baseStart_4829345 : Nat := 118140960795 + 4829345 * 2 ^ 59
def prefixEnd_4829345 : Nat := 4983230072969 + 3 ^ 40 * 4829345 * 2
def baseEnd_4829345 : Nat := 826591743795837633059251

theorem tailTrace_4829345 : CollatzResearch.WordTrace tailWord_4829345 prefixEnd_4829345 826591743795837633059251 := by
  unfold tailWord_4829345
  simp only [CollatzResearch.WordTrace]
  refine ⟨176140682689115326306505489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117427121792743550871003659 176140682689115326306505489)
  ·
    refine ⟨132105512016836494729879117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176140682689115326306505489 132105512016836494729879117)
    ·
      refine ⟨49539567006313685523704669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132105512016836494729879117 49539567006313685523704669)
      ·
        refine ⟨18577337627367632071389251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49539567006313685523704669 18577337627367632071389251)
        ·
          refine ⟨27866006441051448107083877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18577337627367632071389251 27866006441051448107083877)
          ·
            refine ⟨5224876207697146520078227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27866006441051448107083877 5224876207697146520078227)
            ·
              refine ⟨7837314311545719780117341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5224876207697146520078227 7837314311545719780117341)
              ·
                refine ⟨2938992866829644917544003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7837314311545719780117341 2938992866829644917544003)
                ·
                  refine ⟨4408489300244467376316005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938992866829644917544003 4408489300244467376316005)
                  ·
                    refine ⟨826591743795837633059251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4408489300244467376316005 826591743795837633059251)
                    ·
                      rfl

theorem cell23_4829345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_4829345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829345 prefixEnd_4829345 := by exact prefixLift 4829345
  have htrace : WordTrace (prefixWord ++ tailWord_4829345) baseStart_4829345 baseEnd_4829345 := by
    simpa [prefixWord, tailWord_4829345, baseEnd_4829345] using wordTrace_append hprefix tailTrace_4829345
  have hstable : (prefixWord ++ tailWord_4829345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829345).length < 2 ^ (prefixWord ++ tailWord_4829345).sum := by decide
  have hdescent : baseEnd_4829345 < baseStart_4829345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829384 : List Nat := [2, 1, 3, 1, 2, 1, 1, 5, 1, 6]
def baseStart_4829384 : Nat := 118140960795 + 4829384 * 2 ^ 59
def prefixEnd_4829384 : Nat := 4983230072969 + 3 ^ 40 * 4829384 * 2
def baseEnd_4829384 : Nat := 826598419044346082196691

theorem tailTrace_4829384 : CollatzResearch.WordTrace tailWord_4829384 prefixEnd_4829384 826598419044346082196691 := by
  unfold tailWord_4829384
  simp only [CollatzResearch.WordTrace]
  refine ⟨88071052567987017983587603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117428070090649357311450137 88071052567987017983587603)
  ·
    refine ⟨132106578851980526975381405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88071052567987017983587603 132106578851980526975381405)
    ·
      refine ⟨49539967069492697615768027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132106578851980526975381405 49539967069492697615768027)
      ·
        refine ⟨74309950604239046423652041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49539967069492697615768027 74309950604239046423652041)
        ·
          refine ⟨55732462953179284817739031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74309950604239046423652041 55732462953179284817739031)
          ·
            refine ⟨83598694429768927226608547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55732462953179284817739031 83598694429768927226608547)
            ·
              refine ⟨125398041644653390839912821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83598694429768927226608547 125398041644653390839912821)
              ·
                refine ⟨11756066404186255391241827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125398041644653390839912821 11756066404186255391241827)
                ·
                  refine ⟨17634099606279383086862741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11756066404186255391241827 17634099606279383086862741)
                  ·
                    refine ⟨826598419044346082196691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17634099606279383086862741 826598419044346082196691)
                    ·
                      rfl

theorem cell23_4829384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_4829384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829384 prefixEnd_4829384 := by exact prefixLift 4829384
  have htrace : WordTrace (prefixWord ++ tailWord_4829384) baseStart_4829384 baseEnd_4829384 := by
    simpa [prefixWord, tailWord_4829384, baseEnd_4829384] using wordTrace_append hprefix tailTrace_4829384
  have hstable : (prefixWord ++ tailWord_4829384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829384).length < 2 ^ (prefixWord ++ tailWord_4829384).sum := by decide
  have hdescent : baseEnd_4829384 < baseStart_4829384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829388 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 3, 5]
def baseStart_4829388 : Nat := 118140960795 + 4829388 * 2 ^ 59
def prefixEnd_4829388 : Nat := 4983230072969 + 3 ^ 40 * 4829388 * 2
def baseEnd_4829388 : Nat := 826599103685218743646685

theorem tailTrace_4829388 : CollatzResearch.WordTrace tailWord_4829388 prefixEnd_4829388 826599103685218743646685 := by
  unfold tailWord_4829388
  simp only [CollatzResearch.WordTrace]
  refine ⟨88071125513979772325160409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117428167351973029766880545 88071125513979772325160409)
  ·
    refine ⟨66053344135484829243870307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88071125513979772325160409 66053344135484829243870307)
    ·
      refine ⟨99080016203227243865805461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66053344135484829243870307 99080016203227243865805461)
      ·
        refine ⟨4644375759526277056209631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99080016203227243865805461 4644375759526277056209631)
        ·
          refine ⟨6966563639289415584314447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4644375759526277056209631 6966563639289415584314447)
          ·
            refine ⟨10449845458934123376471671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6966563639289415584314447 10449845458934123376471671)
            ·
              refine ⟨15674768188401185064707507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10449845458934123376471671 15674768188401185064707507)
              ·
                refine ⟨23512152282601777597061261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15674768188401185064707507 23512152282601777597061261)
                ·
                  refine ⟨8817057105975666598897973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23512152282601777597061261 8817057105975666598897973)
                  ·
                    refine ⟨826599103685218743646685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8817057105975666598897973 826599103685218743646685)
                    ·
                      rfl

theorem cell23_4829388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_4829388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829388 prefixEnd_4829388 := by exact prefixLift 4829388
  have htrace : WordTrace (prefixWord ++ tailWord_4829388) baseStart_4829388 baseEnd_4829388 := by
    simpa [prefixWord, tailWord_4829388, baseEnd_4829388] using wordTrace_append hprefix tailTrace_4829388
  have hstable : (prefixWord ++ tailWord_4829388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829388).length < 2 ^ (prefixWord ++ tailWord_4829388).sum := by decide
  have hdescent : baseEnd_4829388 < baseStart_4829388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829405 : List Nat := [1, 4, 3, 2, 1, 2, 3, 1, 1, 5]
def baseStart_4829405 : Nat := 118140960795 + 4829405 * 2 ^ 59
def prefixEnd_4829405 : Nat := 4983230072969 + 3 ^ 40 * 4829405 * 2
def baseEnd_4829405 : Nat := 826602013408927554809159

theorem tailTrace_4829405 : CollatzResearch.WordTrace tailWord_4829405 prefixEnd_4829405 826602013408927554809159 := by
  unfold tailWord_4829405
  simp only [CollatzResearch.WordTrace]
  refine ⟨176142871068897956553689669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117428580712598637702459779 176142871068897956553689669)
  ·
    refine ⟨33026788325418366853816813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176142871068897956553689669 33026788325418366853816813)
    ·
      refine ⟨12385045622031887570181305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33026788325418366853816813 12385045622031887570181305)
      ·
        refine ⟨9288784216523915677635979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12385045622031887570181305 9288784216523915677635979)
        ·
          refine ⟨13933176324785873516453969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9288784216523915677635979 13933176324785873516453969)
          ·
            refine ⟨10449882243589405137340477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13933176324785873516453969 10449882243589405137340477)
            ·
              refine ⟨3918705841346026926502679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10449882243589405137340477 3918705841346026926502679)
              ·
                refine ⟨5878058762019040389754019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3918705841346026926502679 5878058762019040389754019)
                ·
                  refine ⟨8817088143028560584631029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5878058762019040389754019 8817088143028560584631029)
                  ·
                    refine ⟨826602013408927554809159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8817088143028560584631029 826602013408927554809159)
                    ·
                      rfl

theorem cell23_4829405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_4829405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829405 prefixEnd_4829405 := by exact prefixLift 4829405
  have htrace : WordTrace (prefixWord ++ tailWord_4829405) baseStart_4829405 baseEnd_4829405 := by
    simpa [prefixWord, tailWord_4829405, baseEnd_4829405] using wordTrace_append hprefix tailTrace_4829405
  have hstable : (prefixWord ++ tailWord_4829405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829405).length < 2 ^ (prefixWord ++ tailWord_4829405).sum := by decide
  have hdescent : baseEnd_4829405 < baseStart_4829405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829408 : List Nat := [2, 1, 1, 3, 1, 3, 5, 1, 1, 1, 4]
def baseStart_4829408 : Nat := 118140960795 + 4829408 * 2 ^ 59
def prefixEnd_4829408 : Nat := 4983230072969 + 3 ^ 40 * 4829408 * 2
def baseEnd_4829408 : Nat := 2479807580668746152689963

theorem tailTrace_4829408 : CollatzResearch.WordTrace tailWord_4829408 prefixEnd_4829408 2479807580668746152689963 := by
  unfold tailWord_4829408
  simp only [CollatzResearch.WordTrace]
  refine ⟨88071490243943544033024439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117428653658591392044032585 88071490243943544033024439)
  ·
    refine ⟨132107235365915316049536659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88071490243943544033024439 132107235365915316049536659)
    ·
      refine ⟨198160853048872974074304989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132107235365915316049536659 198160853048872974074304989)
      ·
        refine ⟨74310319893327365277864371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198160853048872974074304989 74310319893327365277864371)
        ·
          refine ⟨111465479839991047916796557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74310319893327365277864371 111465479839991047916796557)
          ·
            refine ⟨41799554939996642968798709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111465479839991047916796557 41799554939996642968798709)
            ·
              refine ⟨3918708275624685278324879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41799554939996642968798709 3918708275624685278324879)
              ·
                refine ⟨5878062413437027917487319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3918708275624685278324879 5878062413437027917487319)
                ·
                  refine ⟨8817093620155541876230979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5878062413437027917487319 8817093620155541876230979)
                  ·
                    refine ⟨13225640430233312814346469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8817093620155541876230979 13225640430233312814346469)
                    ·
                      refine ⟨2479807580668746152689963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13225640430233312814346469 2479807580668746152689963)
                      ·
                        rfl

theorem cell23_4829408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_4829408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829408 prefixEnd_4829408 := by exact prefixLift 4829408
  have htrace : WordTrace (prefixWord ++ tailWord_4829408) baseStart_4829408 baseEnd_4829408 := by
    simpa [prefixWord, tailWord_4829408, baseEnd_4829408] using wordTrace_append hprefix tailTrace_4829408
  have hstable : (prefixWord ++ tailWord_4829408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829408).length < 2 ^ (prefixWord ++ tailWord_4829408).sum := by decide
  have hdescent : baseEnd_4829408 < baseStart_4829408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829418 : List Nat := [3, 1, 3, 1, 1, 2, 4, 2, 2, 4]
def baseStart_4829418 : Nat := 118140960795 + 4829418 * 2 ^ 59
def prefixEnd_4829418 : Nat := 4983230072969 + 3 ^ 40 * 4829418 * 2
def baseEnd_4829418 : Nat := 826604238491763704521639

theorem tailTrace_4829418 : CollatzResearch.WordTrace tailWord_4829418 prefixEnd_4829418 826604238491763704521639 := by
  unfold tailWord_4829418
  simp only [CollatzResearch.WordTrace]
  refine ⟨44035836304462714943478227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117428896811900573182608605 44035836304462714943478227)
  ·
    refine ⟨66053754456694072415217341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44035836304462714943478227 66053754456694072415217341)
    ·
      refine ⟨24770157921260277155706503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66053754456694072415217341 24770157921260277155706503)
      ·
        refine ⟨37155236881890415733559755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24770157921260277155706503 37155236881890415733559755)
        ·
          refine ⟨55732855322835623600339633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37155236881890415733559755 55732855322835623600339633)
          ·
            refine ⟨41799641492126717700254725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55732855322835623600339633 41799641492126717700254725)
            ·
              refine ⟨7837432779773759568797761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41799641492126717700254725 7837432779773759568797761)
              ·
                refine ⟨5878074584830319676598321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7837432779773759568797761 5878074584830319676598321)
                ·
                  refine ⟨4408555938622739757448741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5878074584830319676598321 4408555938622739757448741)
                  ·
                    refine ⟨826604238491763704521639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4408555938622739757448741 826604238491763704521639)
                    ·
                      rfl

theorem cell23_4829418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_4829418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829418 prefixEnd_4829418 := by exact prefixLift 4829418
  have htrace : WordTrace (prefixWord ++ tailWord_4829418) baseStart_4829418 baseEnd_4829418 := by
    simpa [prefixWord, tailWord_4829418, baseEnd_4829418] using wordTrace_append hprefix tailTrace_4829418
  have hstable : (prefixWord ++ tailWord_4829418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829418).length < 2 ^ (prefixWord ++ tailWord_4829418).sum := by decide
  have hdescent : baseEnd_4829418 < baseStart_4829418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829438 : List Nat := [4, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_4829438 : Nat := 118140960795 + 4829438 * 2 ^ 59
def prefixEnd_4829438 : Nat := 4983230072969 + 3 ^ 40 * 4829438 * 2
def baseEnd_4829438 : Nat := 2479822985088381035314825

theorem tailTrace_4829438 : CollatzResearch.WordTrace tailWord_4829438 prefixEnd_4829438 2479822985088381035314825 := by
  unfold tailWord_4829438
  simp only [CollatzResearch.WordTrace]
  refine ⟨22018009334722300398705121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117429383118518935459760645 22018009334722300398705121)
  ·
    refine ⟨16513507001041725299028841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22018009334722300398705121 16513507001041725299028841)
    ·
      refine ⟨12385130250781293974271631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16513507001041725299028841 12385130250781293974271631)
      ·
        refine ⟨18577695376171940961407447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12385130250781293974271631 18577695376171940961407447)
        ·
          refine ⟨27866543064257911442111171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18577695376171940961407447 27866543064257911442111171)
          ·
            refine ⟨41799814596386867163166757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27866543064257911442111171 41799814596386867163166757)
            ·
              refine ⟨7837465236822537593093767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41799814596386867163166757 7837465236822537593093767)
              ·
                refine ⟨11756197855233806389640651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7837465236822537593093767 11756197855233806389640651)
                ·
                  refine ⟨17634296782850709584460977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11756197855233806389640651 17634296782850709584460977)
                  ·
                    refine ⟨13225722587138032188345733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17634296782850709584460977 13225722587138032188345733)
                    ·
                      refine ⟨2479822985088381035314825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13225722587138032188345733 2479822985088381035314825)
                      ·
                        rfl

theorem cell23_4829438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_4829438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829438 prefixEnd_4829438 := by exact prefixLift 4829438
  have htrace : WordTrace (prefixWord ++ tailWord_4829438) baseStart_4829438 baseEnd_4829438 := by
    simpa [prefixWord, tailWord_4829438, baseEnd_4829438] using wordTrace_append hprefix tailTrace_4829438
  have hstable : (prefixWord ++ tailWord_4829438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829438).length < 2 ^ (prefixWord ++ tailWord_4829438).sum := by decide
  have hdescent : baseEnd_4829438 < baseStart_4829438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829442 : List Nat := [3, 4, 1, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_4829442 : Nat := 118140960795 + 4829442 * 2 ^ 59
def prefixEnd_4829442 : Nat := 4983230072969 + 3 ^ 40 * 4829442 * 2
def baseEnd_4829442 : Nat := 2479825039010999019664807

theorem tailTrace_4829442 : CollatzResearch.WordTrace tailWord_4829442 prefixEnd_4829442 2479825039010999019664807 := by
  unfold tailWord_4829442
  simp only [CollatzResearch.WordTrace]
  refine ⟨44036055142440977968196645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117429480379842607915191053 44036055142440977968196645)
  ·
    refine ⟨8256760339207683369036871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44036055142440977968196645 8256760339207683369036871)
    ·
      refine ⟨12385140508811525053555307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8256760339207683369036871 12385140508811525053555307)
      ·
        refine ⟨18577710763217287580332961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12385140508811525053555307 18577710763217287580332961)
        ·
          refine ⟨13933283072412965685249721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18577710763217287580332961 13933283072412965685249721)
          ·
            refine ⟨10449962304309724263937291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13933283072412965685249721 10449962304309724263937291)
            ·
              refine ⟨15674943456464586395905937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10449962304309724263937291 15674943456464586395905937)
              ·
                refine ⟨11756207592348439796929453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15674943456464586395905937 11756207592348439796929453)
                ·
                  refine ⟨4408577847130664923848545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11756207592348439796929453 4408577847130664923848545)
                  ·
                    refine ⟨3306433385347998692886409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4408577847130664923848545 3306433385347998692886409)
                    ·
                      refine ⟨2479825039010999019664807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3306433385347998692886409 2479825039010999019664807)
                      ·
                        rfl

theorem cell23_4829442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_4829442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829442 prefixEnd_4829442 := by exact prefixLift 4829442
  have htrace : WordTrace (prefixWord ++ tailWord_4829442) baseStart_4829442 baseEnd_4829442 := by
    simpa [prefixWord, tailWord_4829442, baseEnd_4829442] using wordTrace_append hprefix tailTrace_4829442
  have hstable : (prefixWord ++ tailWord_4829442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829442).length < 2 ^ (prefixWord ++ tailWord_4829442).sum := by decide
  have hdescent : baseEnd_4829442 < baseStart_4829442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829502 : List Nat := [4, 2, 1, 2, 1, 3, 2, 2, 1, 3, 2]
def baseStart_4829502 : Nat := 118140960795 + 4829502 * 2 ^ 59
def prefixEnd_4829502 : Nat := 4983230072969 + 3 ^ 40 * 4829502 * 2
def baseEnd_4829502 : Nat := 2479855847850268784914531

theorem tailTrace_4829502 : CollatzResearch.WordTrace tailWord_4829502 prefixEnd_4829502 2479855847850268784914531 := by
  unfold tailWord_4829502
  simp only [CollatzResearch.WordTrace]
  refine ⟨22018301118693317764996345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117430939299697694746647173 22018301118693317764996345)
  ·
    refine ⟨16513725839019988323747259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22018301118693317764996345 16513725839019988323747259)
    ·
      refine ⟨24770588758529982485620889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16513725839019988323747259 24770588758529982485620889)
      ·
        refine ⟨18577941568897486864215667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24770588758529982485620889 18577941568897486864215667)
        ·
          refine ⟨27866912353346230296323501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18577941568897486864215667 27866912353346230296323501)
          ·
            refine ⟨10450092132504836361121313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27866912353346230296323501 10450092132504836361121313)
            ·
              refine ⟨7837569099378627270840985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10450092132504836361121313 7837569099378627270840985)
              ·
                refine ⟨5878176824533970453130739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7837569099378627270840985 5878176824533970453130739)
                ·
                  refine ⟨8817265236800955679696109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5878176824533970453130739 8817265236800955679696109)
                  ·
                    refine ⟨3306474463800358379886041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8817265236800955679696109 3306474463800358379886041)
                    ·
                      refine ⟨2479855847850268784914531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3306474463800358379886041 2479855847850268784914531)
                      ·
                        rfl

theorem cell23_4829502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_4829502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829502 prefixEnd_4829502 := by exact prefixLift 4829502
  have htrace : WordTrace (prefixWord ++ tailWord_4829502) baseStart_4829502 baseEnd_4829502 := by
    simpa [prefixWord, tailWord_4829502, baseEnd_4829502] using wordTrace_append hprefix tailTrace_4829502
  have hstable : (prefixWord ++ tailWord_4829502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829502).length < 2 ^ (prefixWord ++ tailWord_4829502).sum := by decide
  have hdescent : baseEnd_4829502 < baseStart_4829502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829504 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 9]
def baseStart_4829504 : Nat := 118140960795 + 4829504 * 2 ^ 59
def prefixEnd_4829504 : Nat := 4983230072969 + 3 ^ 40 * 4829504 * 2
def baseEnd_4829504 : Nat := 275539652756841975232169

theorem tailTrace_4829504 : CollatzResearch.WordTrace tailWord_4829504 prefixEnd_4829504 275539652756841975232169 := by
  unfold tailWord_4829504
  simp only [CollatzResearch.WordTrace]
  refine ⟨88073240947769648230771783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117430987930359530974362377 88073240947769648230771783)
  ·
    refine ⟨132109861421654472346157675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88073240947769648230771783 132109861421654472346157675)
    ·
      refine ⟨198164792132481708519236513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132109861421654472346157675 198164792132481708519236513)
      ·
        refine ⟨148623594099361281389427385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198164792132481708519236513 148623594099361281389427385)
        ·
          refine ⟨111467695574520961042070539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148623594099361281389427385 111467695574520961042070539)
          ·
            refine ⟨167201543361781441563105809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111467695574520961042070539 167201543361781441563105809)
            ·
              refine ⟨125401157521336081172329357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167201543361781441563105809 125401157521336081172329357)
              ·
                refine ⟨47025434070501030439623509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125401157521336081172329357 47025434070501030439623509)
                ·
                  refine ⟨275539652756841975232169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47025434070501030439623509 275539652756841975232169)
                  ·
                    rfl

theorem cell23_4829504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 9].length) (baseStart_4829504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829504 prefixEnd_4829504 := by exact prefixLift 4829504
  have htrace : WordTrace (prefixWord ++ tailWord_4829504) baseStart_4829504 baseEnd_4829504 := by
    simpa [prefixWord, tailWord_4829504, baseEnd_4829504] using wordTrace_append hprefix tailTrace_4829504
  have hstable : (prefixWord ++ tailWord_4829504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829504).length < 2 ^ (prefixWord ++ tailWord_4829504).sum := by decide
  have hdescent : baseEnd_4829504 < baseStart_4829504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829538 : List Nat := [3, 3, 2, 1, 1, 2, 3, 1, 7]
def baseStart_4829538 : Nat := 118140960795 + 4829538 * 2 ^ 59
def prefixEnd_4829538 : Nat := 4983230072969 + 3 ^ 40 * 4829538 * 2
def baseEnd_4829538 : Nat := 275541592572647849340485

theorem tailTrace_4829538 : CollatzResearch.WordTrace tailWord_4829538 prefixEnd_4829538 275541592572647849340485 := by
  unfold tailWord_4829538
  simp only [CollatzResearch.WordTrace]
  refine ⟨44036930494354030067070317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117431814651610746845520845 44036930494354030067070317)
  ·
    refine ⟨16513848935382761275151369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44036930494354030067070317 16513848935382761275151369)
    ·
      refine ⟨12385386701537070956363527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16513848935382761275151369 12385386701537070956363527)
      ·
        refine ⟨18578080052305606434545291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12385386701537070956363527 18578080052305606434545291)
        ·
          refine ⟨27867120078458409651817937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18578080052305606434545291 27867120078458409651817937)
          ·
            refine ⟨20900340058843807238863453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27867120078458409651817937 20900340058843807238863453)
            ·
              refine ⟨7837627522066427714573795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20900340058843807238863453 7837627522066427714573795)
              ·
                refine ⟨11756441283099641571860693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7837627522066427714573795 11756441283099641571860693)
                ·
                  refine ⟨275541592572647849340485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11756441283099641571860693 275541592572647849340485)
                  ·
                    rfl

theorem cell23_4829538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_4829538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829538 prefixEnd_4829538 := by exact prefixLift 4829538
  have htrace : WordTrace (prefixWord ++ tailWord_4829538) baseStart_4829538 baseEnd_4829538 := by
    simpa [prefixWord, tailWord_4829538, baseEnd_4829538] using wordTrace_append hprefix tailTrace_4829538
  have hstable : (prefixWord ++ tailWord_4829538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829538).length < 2 ^ (prefixWord ++ tailWord_4829538).sum := by decide
  have hdescent : baseEnd_4829538 < baseStart_4829538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829625 : List Nat := [1, 2, 1, 4, 3, 1, 3, 1, 2, 2, 3]
def baseStart_4829625 : Nat := 118140960795 + 4829625 * 2 ^ 59
def prefixEnd_4829625 : Nat := 4983230072969 + 3 ^ 40 * 4829625 * 2
def baseEnd_4829625 : Nat := 2479919005970771803676465

theorem tailTrace_4829625 : CollatzResearch.WordTrace tailWord_4829625 prefixEnd_4829625 2479919005970771803676465 := by
  unfold tailWord_4829625
  simp only [CollatzResearch.WordTrace]
  refine ⟨176150895128100934126698329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117433930085400622751132219 176150895128100934126698329)
  ·
    refine ⟨132113171346075700595023747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176150895128100934126698329 132113171346075700595023747)
    ·
      refine ⟨198169757019113550892535621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132113171346075700595023747 198169757019113550892535621)
      ·
        refine ⟨37156829441083790792350429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198169757019113550892535621 37156829441083790792350429)
        ·
          refine ⟨13933811040406421547131411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37156829441083790792350429 13933811040406421547131411)
          ·
            refine ⟨20900716560609632320697117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13933811040406421547131411 20900716560609632320697117)
            ·
              refine ⟨7837768710228612120261419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20900716560609632320697117 7837768710228612120261419)
              ·
                refine ⟨11756653065342918180392129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7837768710228612120261419 11756653065342918180392129)
                ·
                  refine ⟨8817489799007188635294097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11756653065342918180392129 8817489799007188635294097)
                  ·
                    refine ⟨6613117349255391476470573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8817489799007188635294097 6613117349255391476470573)
                    ·
                      refine ⟨2479919005970771803676465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6613117349255391476470573 2479919005970771803676465)
                      ·
                        rfl

theorem cell23_4829625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_4829625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829625 prefixEnd_4829625 := by exact prefixLift 4829625
  have htrace : WordTrace (prefixWord ++ tailWord_4829625) baseStart_4829625 baseEnd_4829625 := by
    simpa [prefixWord, tailWord_4829625, baseEnd_4829625] using wordTrace_append hprefix tailTrace_4829625
  have hstable : (prefixWord ++ tailWord_4829625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829625).length < 2 ^ (prefixWord ++ tailWord_4829625).sum := by decide
  have hdescent : baseEnd_4829625 < baseStart_4829625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829648 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 5, 5, 2]
def baseStart_4829648 : Nat := 118140960795 + 4829648 * 2 ^ 59
def prefixEnd_4829648 : Nat := 4983230072969 + 3 ^ 40 * 4829648 * 2
def baseEnd_4829648 : Nat := 2479930816025825213688859

theorem tailTrace_4829648 : CollatzResearch.WordTrace tailWord_4829648 prefixEnd_4829648 2479930816025825213688859 := by
  unfold tailWord_4829648
  simp only [CollatzResearch.WordTrace]
  refine ⟨88075867003508804527392799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117434489338011739369857065 88075867003508804527392799)
  ·
    refine ⟨132113800505263206791089199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88075867003508804527392799 132113800505263206791089199)
    ·
      refine ⟨198170700757894810186633799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132113800505263206791089199 198170700757894810186633799)
      ·
        refine ⟨297256051136842215279950699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198170700757894810186633799 297256051136842215279950699)
        ·
          refine ⟨445884076705263322919926049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297256051136842215279950699 445884076705263322919926049)
          ·
            refine ⟨334413057528947492189944537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 445884076705263322919926049 334413057528947492189944537)
            ·
              refine ⟨250809793146710619142458403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334413057528947492189944537 250809793146710619142458403)
              ·
                refine ⟨376214689720065928713687605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250809793146710619142458403 376214689720065928713687605)
                ·
                  refine ⟨35270127161256180816908213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 376214689720065928713687605 35270127161256180816908213)
                  ·
                    refine ⟨3306574421367766951585145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35270127161256180816908213 3306574421367766951585145)
                    ·
                      refine ⟨2479930816025825213688859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3306574421367766951585145 2479930816025825213688859)
                      ·
                        rfl

theorem cell23_4829648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5, 5, 2].length) (baseStart_4829648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829648 prefixEnd_4829648 := by exact prefixLift 4829648
  have htrace : WordTrace (prefixWord ++ tailWord_4829648) baseStart_4829648 baseEnd_4829648 := by
    simpa [prefixWord, tailWord_4829648, baseEnd_4829648] using wordTrace_append hprefix tailTrace_4829648
  have hstable : (prefixWord ++ tailWord_4829648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829648).length < 2 ^ (prefixWord ++ tailWord_4829648).sum := by decide
  have hdescent : baseEnd_4829648 < baseStart_4829648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829688 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 6, 4]
def baseStart_4829688 : Nat := 118140960795 + 4829688 * 2 ^ 59
def prefixEnd_4829688 : Nat := 4983230072969 + 3 ^ 40 * 4829688 * 2
def baseEnd_4829688 : Nat := 826650451750668352396225

theorem tailTrace_4829688 : CollatzResearch.WordTrace tailWord_4829688 prefixEnd_4829688 826650451750668352396225 := by
  unfold tailWord_4829688
  simp only [CollatzResearch.WordTrace]
  refine ⟨88076596463436347943120859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117435461951248463924161145 88076596463436347943120859)
  ·
    refine ⟨132114894695154521914681289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88076596463436347943120859 132114894695154521914681289)
    ·
      refine ⟨99086171021365891436010967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132114894695154521914681289 99086171021365891436010967)
      ·
        refine ⟨148629256532048837154016451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99086171021365891436010967 148629256532048837154016451)
        ·
          refine ⟨222943884798073255731024677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148629256532048837154016451 222943884798073255731024677)
          ·
            refine ⟨41801978399638735449567127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 222943884798073255731024677 41801978399638735449567127)
            ·
              refine ⟨62702967599458103174350691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41801978399638735449567127 62702967599458103174350691)
              ·
                refine ⟨94054451399187154761526037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62702967599458103174350691 94054451399187154761526037)
                ·
                  refine ⟨4408802409336897879446533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94054451399187154761526037 4408802409336897879446533)
                  ·
                    refine ⟨826650451750668352396225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4408802409336897879446533 826650451750668352396225)
                    ·
                      rfl

theorem cell23_4829688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_4829688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829688 prefixEnd_4829688 := by exact prefixLift 4829688
  have htrace : WordTrace (prefixWord ++ tailWord_4829688) baseStart_4829688 baseEnd_4829688 := by
    simpa [prefixWord, tailWord_4829688, baseEnd_4829688] using wordTrace_append hprefix tailTrace_4829688
  have hstable : (prefixWord ++ tailWord_4829688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829688).length < 2 ^ (prefixWord ++ tailWord_4829688).sum := by decide
  have hdescent : baseEnd_4829688 < baseStart_4829688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829691 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 6]
def baseStart_4829691 : Nat := 118140960795 + 4829691 * 2 ^ 59
def prefixEnd_4829691 : Nat := 4983230072969 + 3 ^ 40 * 4829691 * 2
def baseEnd_4829691 : Nat := 2479952895693968545451161

theorem tailTrace_4829691 : CollatzResearch.WordTrace tailWord_4829691 prefixEnd_4829691 2479952895693968545451161 := by
  unfold tailWord_4829691
  simp only [CollatzResearch.WordTrace]
  refine ⟨176153302345861827398600927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117435534897241218265733951 176153302345861827398600927)
  ·
    refine ⟨264229953518792741097901391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176153302345861827398600927 264229953518792741097901391)
    ·
      refine ⟨396344930278189111646852087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264229953518792741097901391 396344930278189111646852087)
      ·
        refine ⟨594517395417283667470278131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396344930278189111646852087 594517395417283667470278131)
        ·
          refine ⟨891776093125925501205417197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 594517395417283667470278131 891776093125925501205417197)
          ·
            refine ⟨334416034922222062952031449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 891776093125925501205417197 334416034922222062952031449)
            ·
              refine ⟨250812026191666547214023587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334416034922222062952031449 250812026191666547214023587)
              ·
                refine ⟨376218039287499820821035381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250812026191666547214023587 376218039287499820821035381)
                ·
                  refine ⟨35270441183203108201972067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 376218039287499820821035381 35270441183203108201972067)
                  ·
                    refine ⟨52905661774804662302958101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35270441183203108201972067 52905661774804662302958101)
                    ·
                      refine ⟨2479952895693968545451161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52905661774804662302958101 2479952895693968545451161)
                      ·
                        rfl

theorem cell23_4829691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 6].length) (baseStart_4829691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829691 prefixEnd_4829691 := by exact prefixLift 4829691
  have htrace : WordTrace (prefixWord ++ tailWord_4829691) baseStart_4829691 baseEnd_4829691 := by
    simpa [prefixWord, tailWord_4829691, baseEnd_4829691] using wordTrace_append hprefix tailTrace_4829691
  have hstable : (prefixWord ++ tailWord_4829691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829691).length < 2 ^ (prefixWord ++ tailWord_4829691).sum := by decide
  have hdescent : baseEnd_4829691 < baseStart_4829691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829701 : List Nat := [1, 3, 1, 1, 2, 2, 13]
def baseStart_4829701 : Nat := 118140960795 + 4829701 * 2 ^ 59
def prefixEnd_4829701 : Nat := 4983230072969 + 3 ^ 40 * 4829701 * 2
def baseEnd_4829701 : Nat := 30616765808648314892915

theorem tailTrace_4829701 : CollatzResearch.WordTrace tailWord_4829701 prefixEnd_4829701 30616765808648314892915 := by
  unfold tailWord_4829701
  simp only [CollatzResearch.WordTrace]
  refine ⟨176153667075825599106464957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117435778050550399404309971 176153667075825599106464957)
  ·
    refine ⟨66057625153434599664924359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176153667075825599106464957 66057625153434599664924359)
    ·
      refine ⟨99086437730151899497386539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66057625153434599664924359 99086437730151899497386539)
      ·
        refine ⟨148629656595227849246079809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99086437730151899497386539 148629656595227849246079809)
        ·
          refine ⟨111472242446420886934559857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148629656595227849246079809 111472242446420886934559857)
          ·
            refine ⟨83604181834815665200919893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111472242446420886934559857 83604181834815665200919893)
            ·
              refine ⟨30616765808648314892915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 83604181834815665200919893 30616765808648314892915)
              ·
                rfl

theorem cell23_4829701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 13].length) (baseStart_4829701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829701 prefixEnd_4829701 := by exact prefixLift 4829701
  have htrace : WordTrace (prefixWord ++ tailWord_4829701) baseStart_4829701 baseEnd_4829701 := by
    simpa [prefixWord, tailWord_4829701, baseEnd_4829701] using wordTrace_append hprefix tailTrace_4829701
  have hstable : (prefixWord ++ tailWord_4829701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829701).length < 2 ^ (prefixWord ++ tailWord_4829701).sum := by decide
  have hdescent : baseEnd_4829701 < baseStart_4829701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829708 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 1, 1, 6]
def baseStart_4829708 : Nat := 118140960795 + 4829708 * 2 ^ 59
def prefixEnd_4829708 : Nat := 4983230072969 + 3 ^ 40 * 4829708 * 2
def baseEnd_4829708 : Nat := 2479961624865094978938583

theorem tailTrace_4829708 : CollatzResearch.WordTrace tailWord_4829708 prefixEnd_4829708 2479961624865094978938583 := by
  unfold tailWord_4829708
  simp only [CollatzResearch.WordTrace]
  refine ⟨88076961193400119650984889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117435948257866826201313185 88076961193400119650984889)
  ·
    refine ⟨66057720895050089738238667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88076961193400119650984889 66057720895050089738238667)
    ·
      refine ⟨99086581342575134607358001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66057720895050089738238667 99086581342575134607358001)
      ·
        refine ⟨74314936006931350955518501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99086581342575134607358001 74314936006931350955518501)
        ·
          refine ⟨13934050501299628304159719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74314936006931350955518501 13934050501299628304159719)
          ·
            refine ⟨20901075751949442456239579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13934050501299628304159719 20901075751949442456239579)
            ·
              refine ⟨31351613627924163684359369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20901075751949442456239579 31351613627924163684359369)
              ·
                refine ⟨23513710220943122763269527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31351613627924163684359369 23513710220943122763269527)
                ·
                  refine ⟨35270565331414684144904291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23513710220943122763269527 35270565331414684144904291)
                  ·
                    refine ⟨52905847997122026217356437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35270565331414684144904291 52905847997122026217356437)
                    ·
                      refine ⟨2479961624865094978938583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52905847997122026217356437 2479961624865094978938583)
                      ·
                        rfl

theorem cell23_4829708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_4829708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829708 prefixEnd_4829708 := by exact prefixLift 4829708
  have htrace : WordTrace (prefixWord ++ tailWord_4829708) baseStart_4829708 baseEnd_4829708 := by
    simpa [prefixWord, tailWord_4829708, baseEnd_4829708] using wordTrace_append hprefix tailTrace_4829708
  have hstable : (prefixWord ++ tailWord_4829708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829708).length < 2 ^ (prefixWord ++ tailWord_4829708).sum := by decide
  have hdescent : baseEnd_4829708 < baseStart_4829708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829711 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 7]
def baseStart_4829711 : Nat := 118140960795 + 4829711 * 2 ^ 59
def prefixEnd_4829711 : Nat := 4983230072969 + 3 ^ 40 * 4829711 * 2
def baseEnd_4829711 : Nat := 2479963165307058467201069

theorem tailTrace_4829711 : CollatzResearch.WordTrace tailWord_4829711 prefixEnd_4829711 2479963165307058467201069 := by
  unfold tailWord_4829711
  simp only [CollatzResearch.WordTrace]
  refine ⟨176154031805789370814328987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117436021203859580542885991 176154031805789370814328987)
  ·
    refine ⟨264231047708684056221493481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176154031805789370814328987 264231047708684056221493481)
    ·
      refine ⟨198173285781513042166120111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264231047708684056221493481 198173285781513042166120111)
      ·
        refine ⟨297259928672269563249180167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198173285781513042166120111 297259928672269563249180167)
        ·
          refine ⟨445889893008404344873770251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297259928672269563249180167 445889893008404344873770251)
          ·
            refine ⟨668834839512606517310655377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445889893008404344873770251 668834839512606517310655377)
            ·
              refine ⟨501626129634454887982991533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 668834839512606517310655377 501626129634454887982991533)
              ·
                refine ⟨188109798612920582993621825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 501626129634454887982991533 188109798612920582993621825)
                ·
                  refine ⟨141082348959690437245216369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188109798612920582993621825 141082348959690437245216369)
                  ·
                    refine ⟨105811761719767827933912277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 141082348959690437245216369 105811761719767827933912277)
                    ·
                      refine ⟨2479963165307058467201069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105811761719767827933912277 2479963165307058467201069)
                      ·
                        rfl

theorem cell23_4829711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_4829711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829711 prefixEnd_4829711 := by exact prefixLift 4829711
  have htrace : WordTrace (prefixWord ++ tailWord_4829711) baseStart_4829711 baseEnd_4829711 := by
    simpa [prefixWord, tailWord_4829711, baseEnd_4829711] using wordTrace_append hprefix tailTrace_4829711
  have hstable : (prefixWord ++ tailWord_4829711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829711).length < 2 ^ (prefixWord ++ tailWord_4829711).sum := by decide
  have hdescent : baseEnd_4829711 < baseStart_4829711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829722 : List Nat := [3, 1, 1, 3, 1, 1, 6, 1, 2, 4]
def baseStart_4829722 : Nat := 118140960795 + 4829722 * 2 ^ 59
def prefixEnd_4829722 : Nat := 4983230072969 + 3 ^ 40 * 4829722 * 2
def baseEnd_4829722 : Nat := 826656271198085974721173

theorem tailTrace_4829722 : CollatzResearch.WordTrace tailWord_4829722 prefixEnd_4829722 826656271198085974721173 := by
  unfold tailWord_4829722
  simp only [CollatzResearch.WordTrace]
  refine ⟨44038608252187379923244855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117436288672499679795319613 44038608252187379923244855)
  ·
    refine ⟨66057912378281069884867283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44038608252187379923244855 66057912378281069884867283)
    ·
      refine ⟨99086868567421604827300925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66057912378281069884867283 99086868567421604827300925)
      ·
        refine ⟨37157575712783101810237847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99086868567421604827300925 37157575712783101810237847)
        ·
          refine ⟨55736363569174652715356771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37157575712783101810237847 55736363569174652715356771)
          ·
            refine ⟨83604545353761979073035157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55736363569174652715356771 83604545353761979073035157)
            ·
              refine ⟨3918963063457592769048523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83604545353761979073035157 3918963063457592769048523)
              ·
                refine ⟨5878444595186389153572785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3918963063457592769048523 5878444595186389153572785)
                ·
                  refine ⟨4408833446389791865179589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5878444595186389153572785 4408833446389791865179589)
                  ·
                    refine ⟨826656271198085974721173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4408833446389791865179589 826656271198085974721173)
                    ·
                      rfl

theorem cell23_4829722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 2, 4].length) (baseStart_4829722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829722 prefixEnd_4829722 := by exact prefixLift 4829722
  have htrace : WordTrace (prefixWord ++ tailWord_4829722) baseStart_4829722 baseEnd_4829722 := by
    simpa [prefixWord, tailWord_4829722, baseEnd_4829722] using wordTrace_append hprefix tailTrace_4829722
  have hstable : (prefixWord ++ tailWord_4829722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829722).length < 2 ^ (prefixWord ++ tailWord_4829722).sum := by decide
  have hdescent : baseEnd_4829722 < baseStart_4829722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829742 : List Nat := [4, 1, 3, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_4829742 : Nat := 118140960795 + 4829742 * 2 ^ 59
def prefixEnd_4829742 : Nat := 4983230072969 + 3 ^ 40 * 4829742 * 2
def baseEnd_4829742 : Nat := 2479979083207347845913427

theorem tailTrace_4829742 : CollatzResearch.WordTrace tailWord_4829742 prefixEnd_4829742 2479979083207347845913427 := by
  unfold tailWord_4829742
  simp only [CollatzResearch.WordTrace]
  refine ⟨22019395308584632888588435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117436774979118042072471653 22019395308584632888588435)
  ·
    refine ⟨33029092962876949332882653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22019395308584632888588435 33029092962876949332882653)
    ·
      refine ⟨12385909861078855999830995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33029092962876949332882653 12385909861078855999830995)
      ·
        refine ⟨18578864791618283999746493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12385909861078855999830995 18578864791618283999746493)
        ·
          refine ⟨6967074296856856499904935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18578864791618283999746493 6967074296856856499904935)
          ·
            refine ⟨10450611445285284749857403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6967074296856856499904935 10450611445285284749857403)
            ·
              refine ⟨15675917167927927124786105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10450611445285284749857403 15675917167927927124786105)
              ·
                refine ⟨11756937875945945343589579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15675917167927927124786105 11756937875945945343589579)
                ·
                  refine ⟨17635406813918918015384369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11756937875945945343589579 17635406813918918015384369)
                  ·
                    refine ⟨13226555110439188511538277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17635406813918918015384369 13226555110439188511538277)
                    ·
                      refine ⟨2479979083207347845913427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13226555110439188511538277 2479979083207347845913427)
                      ·
                        rfl

theorem cell23_4829742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_4829742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829742 prefixEnd_4829742 := by exact prefixLift 4829742
  have htrace : WordTrace (prefixWord ++ tailWord_4829742) baseStart_4829742 baseEnd_4829742 := by
    simpa [prefixWord, tailWord_4829742, baseEnd_4829742] using wordTrace_append hprefix tailTrace_4829742
  have hstable : (prefixWord ++ tailWord_4829742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829742).length < 2 ^ (prefixWord ++ tailWord_4829742).sum := by decide
  have hdescent : baseEnd_4829742 < baseStart_4829742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829745 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 6, 1, 3]
def baseStart_4829745 : Nat := 118140960795 + 4829745 * 2 ^ 59
def prefixEnd_4829745 : Nat := 4983230072969 + 3 ^ 40 * 4829745 * 2
def baseEnd_4829745 : Nat := 2479980623649311334175913

theorem tailTrace_4829745 : CollatzResearch.WordTrace tailWord_4829745 prefixEnd_4829745 2479980623649311334175913 := by
  unfold tailWord_4829745
  simp only [CollatzResearch.WordTrace]
  refine ⟨176155271887666194621066689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117436847925110796414044459 176155271887666194621066689)
  ·
    refine ⟨132116453915749645965800017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176155271887666194621066689 132116453915749645965800017)
    ·
      refine ⟨99087340436812234474350013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132116453915749645965800017 99087340436812234474350013)
      ·
        refine ⟨37157752663804587927881255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99087340436812234474350013 37157752663804587927881255)
        ·
          refine ⟨55736628995706881891821883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37157752663804587927881255 55736628995706881891821883)
          ·
            refine ⟨83604943493560322837732825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55736628995706881891821883 83604943493560322837732825)
            ·
              refine ⟨62703707620170242128299619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83604943493560322837732825 62703707620170242128299619)
              ·
                refine ⟨94055561430255363192449429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62703707620170242128299619 94055561430255363192449429)
                ·
                  refine ⟨4408854442043220149646067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94055561430255363192449429 4408854442043220149646067)
                  ·
                    refine ⟨6613281663064830224469101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4408854442043220149646067 6613281663064830224469101)
                    ·
                      refine ⟨2479980623649311334175913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6613281663064830224469101 2479980623649311334175913)
                      ·
                        rfl

theorem cell23_4829745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_4829745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829745 prefixEnd_4829745 := by exact prefixLift 4829745
  have htrace : WordTrace (prefixWord ++ tailWord_4829745) baseStart_4829745 baseEnd_4829745 := by
    simpa [prefixWord, tailWord_4829745, baseEnd_4829745] using wordTrace_append hprefix tailTrace_4829745
  have hstable : (prefixWord ++ tailWord_4829745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829745).length < 2 ^ (prefixWord ++ tailWord_4829745).sum := by decide
  have hdescent : baseEnd_4829745 < baseStart_4829745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829802 : List Nat := [3, 1, 3, 2, 1, 1, 1, 4, 1, 4, 2]
def baseStart_4829802 : Nat := 118140960795 + 4829802 * 2 ^ 59
def prefixEnd_4829802 : Nat := 4983230072969 + 3 ^ 40 * 4829802 * 2
def baseEnd_4829802 : Nat := 2480009892046617611163151

theorem tailTrace_4829802 : CollatzResearch.WordTrace tailWord_4829802 prefixEnd_4829802 2480009892046617611163151 := by
  unfold tailWord_4829802
  simp only [CollatzResearch.WordTrace]
  refine ⟨44039337712114923338972915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117438233898973128903927773 44039337712114923338972915)
  ·
    refine ⟨66059006568172385008459373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44039337712114923338972915 66059006568172385008459373)
    ·
      refine ⟨24772127463064644378172265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66059006568172385008459373 24772127463064644378172265)
      ·
        refine ⟨18579095597298483283629199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24772127463064644378172265 18579095597298483283629199)
        ·
          refine ⟨27868643395947724925443799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18579095597298483283629199 27868643395947724925443799)
          ·
            refine ⟨41802965093921587388165699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27868643395947724925443799 41802965093921587388165699)
            ·
              refine ⟨62704447640882381082248549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41802965093921587388165699 62704447640882381082248549)
              ·
                refine ⟨11757083932665446452921603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62704447640882381082248549 11757083932665446452921603)
                ·
                  refine ⟨17635625898998169679382405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11757083932665446452921603 17635625898998169679382405)
                  ·
                    refine ⟨3306679856062156814884201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17635625898998169679382405 3306679856062156814884201)
                    ·
                      refine ⟨2480009892046617611163151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3306679856062156814884201 2480009892046617611163151)
                      ·
                        rfl

theorem cell23_4829802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_4829802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829802 prefixEnd_4829802 := by exact prefixLift 4829802
  have htrace : WordTrace (prefixWord ++ tailWord_4829802) baseStart_4829802 baseEnd_4829802 := by
    simpa [prefixWord, tailWord_4829802, baseEnd_4829802] using wordTrace_append hprefix tailTrace_4829802
  have hstable : (prefixWord ++ tailWord_4829802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829802).length < 2 ^ (prefixWord ++ tailWord_4829802).sum := by decide
  have hdescent : baseEnd_4829802 < baseStart_4829802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829806 : List Nat := [4, 1, 2, 2, 2, 1, 4, 1, 1, 3, 2]
def baseStart_4829806 : Nat := 118140960795 + 4829806 * 2 ^ 59
def prefixEnd_4829806 : Nat := 4983230072969 + 3 ^ 40 * 4829806 * 2
def baseEnd_4829806 : Nat := 2480011945969235595513133

theorem tailTrace_4829806 : CollatzResearch.WordTrace tailWord_4829806 prefixEnd_4829806 2480011945969235595513133 := by
  unfold tailWord_4829806
  simp only [CollatzResearch.WordTrace]
  refine ⟨22019687092555650254879659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117438331160296801359358181 22019687092555650254879659)
  ·
    refine ⟨33029530638833475382319489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22019687092555650254879659 33029530638833475382319489)
    ·
      refine ⟨24772147979125106536739617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33029530638833475382319489 24772147979125106536739617)
      ·
        refine ⟨18579110984343829902554713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24772147979125106536739617 18579110984343829902554713)
        ·
          refine ⟨13934333238257872426916035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18579110984343829902554713 13934333238257872426916035)
          ·
            refine ⟨20901499857386808640374053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13934333238257872426916035 20901499857386808640374053)
            ·
              refine ⟨3919031223260026620070135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20901499857386808640374053 3919031223260026620070135)
              ·
                refine ⟨5878546834890039930105203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3919031223260026620070135 5878546834890039930105203)
                ·
                  refine ⟨8817820252335059895157805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5878546834890039930105203 8817820252335059895157805)
                  ·
                    refine ⟨3306682594625647460684177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8817820252335059895157805 3306682594625647460684177)
                    ·
                      refine ⟨2480011945969235595513133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3306682594625647460684177 2480011945969235595513133)
                      ·
                        rfl

theorem cell23_4829806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_4829806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829806 prefixEnd_4829806 := by exact prefixLift 4829806
  have htrace : WordTrace (prefixWord ++ tailWord_4829806) baseStart_4829806 baseEnd_4829806 := by
    simpa [prefixWord, tailWord_4829806, baseEnd_4829806] using wordTrace_append hprefix tailTrace_4829806
  have hstable : (prefixWord ++ tailWord_4829806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829806).length < 2 ^ (prefixWord ++ tailWord_4829806).sum := by decide
  have hdescent : baseEnd_4829806 < baseStart_4829806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829813 : List Nat := [1, 3, 4, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_4829813 : Nat := 118140960795 + 4829813 * 2 ^ 59
def prefixEnd_4829813 : Nat := 4983230072969 + 3 ^ 40 * 4829813 * 2
def baseEnd_4829813 : Nat := 2480015540333817068125601

theorem tailTrace_4829813 : CollatzResearch.WordTrace tailWord_4829813 prefixEnd_4829813 2480015540333817068125601 := by
  unfold tailWord_4829813
  simp only [CollatzResearch.WordTrace]
  refine ⟨176157752051419842234542093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117438501367613228156361395 176157752051419842234542093)
  ·
    refine ⟨66059157019282440837953285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176157752051419842234542093 66059157019282440837953285)
    ·
      refine ⟨12386091941115457657116241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66059157019282440837953285 12386091941115457657116241)
      ·
        refine ⟨9289568955836593242837181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12386091941115457657116241 9289568955836593242837181)
        ·
          refine ⟨3483588358438722466063943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9289568955836593242837181 3483588358438722466063943)
          ·
            refine ⟨5225382537658083699095915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3483588358438722466063943 5225382537658083699095915)
            ·
              refine ⟨7838073806487125548643873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5225382537658083699095915 7838073806487125548643873)
              ·
                refine ⟨5878555354865344161482905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7838073806487125548643873 5878555354865344161482905)
                ·
                  refine ⟨4408916516149008121112179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5878555354865344161482905 4408916516149008121112179)
                  ·
                    refine ⟨6613374774223512181668269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4408916516149008121112179 6613374774223512181668269)
                    ·
                      refine ⟨2480015540333817068125601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6613374774223512181668269 2480015540333817068125601)
                      ·
                        rfl

theorem cell23_4829813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_4829813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829813 prefixEnd_4829813 := by exact prefixLift 4829813
  have htrace : WordTrace (prefixWord ++ tailWord_4829813) baseStart_4829813 baseEnd_4829813 := by
    simpa [prefixWord, tailWord_4829813, baseEnd_4829813] using wordTrace_append hprefix tailTrace_4829813
  have hstable : (prefixWord ++ tailWord_4829813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829813).length < 2 ^ (prefixWord ++ tailWord_4829813).sum := by decide
  have hdescent : baseEnd_4829813 < baseStart_4829813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829825 : List Nat := [1, 2, 4, 2, 1, 1, 4, 1, 7]
def baseStart_4829825 : Nat := 118140960795 + 4829825 * 2 ^ 59
def prefixEnd_4829825 : Nat := 4983230072969 + 3 ^ 40 * 4829825 * 2
def baseEnd_4829825 : Nat := 275557966900185669019505

theorem tailTrace_4829825 : CollatzResearch.WordTrace tailWord_4829825 prefixEnd_4829825 275557966900185669019505 := by
  unfold tailWord_4829825
  simp only [CollatzResearch.WordTrace]
  refine ⟨176158189727376368283978929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117438793151584245522652619 176158189727376368283978929)
  ·
    refine ⟨132118642295532276212984197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176158189727376368283978929 132118642295532276212984197)
    ·
      refine ⟨24772245430412301789934537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132118642295532276212984197 24772245430412301789934537)
      ·
        refine ⟨18579184072809226342450903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24772245430412301789934537 18579184072809226342450903)
        ·
          refine ⟨27868776109213839513676355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18579184072809226342450903 27868776109213839513676355)
          ·
            refine ⟨41803164163820759270514533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27868776109213839513676355 41803164163820759270514533)
            ·
              refine ⟨7838093280716392363221475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41803164163820759270514533 7838093280716392363221475)
              ·
                refine ⟨11757139921074588544832213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7838093280716392363221475 11757139921074588544832213)
                ·
                  refine ⟨275557966900185669019505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11757139921074588544832213 275557966900185669019505)
                  ·
                    rfl

theorem cell23_4829825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 7].length) (baseStart_4829825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829825 prefixEnd_4829825 := by exact prefixLift 4829825
  have htrace : WordTrace (prefixWord ++ tailWord_4829825) baseStart_4829825 baseEnd_4829825 := by
    simpa [prefixWord, tailWord_4829825, baseEnd_4829825] using wordTrace_append hprefix tailTrace_4829825
  have hstable : (prefixWord ++ tailWord_4829825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829825).length < 2 ^ (prefixWord ++ tailWord_4829825).sum := by decide
  have hdescent : baseEnd_4829825 < baseStart_4829825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829875 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 4]
def baseStart_4829875 : Nat := 118140960795 + 4829875 * 2 ^ 59
def prefixEnd_4829875 : Nat := 4983230072969 + 3 ^ 40 * 4829875 * 2
def baseEnd_4829875 : Nat := 2480047376134395825550315

theorem tailTrace_4829875 : CollatzResearch.WordTrace tailWord_4829875 prefixEnd_4829875 2480047376134395825550315 := by
  unfold tailWord_4829875
  simp only [CollatzResearch.WordTrace]
  refine ⟨176160013377195226823299079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117440008918130151215532719 176160013377195226823299079)
  ·
    refine ⟨264240020065792840234948619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176160013377195226823299079 264240020065792840234948619)
    ·
      refine ⟨396360030098689260352422929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264240020065792840234948619 396360030098689260352422929)
      ·
        refine ⟨297270022574016945264317197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 396360030098689260352422929 297270022574016945264317197)
        ·
          refine ⟨111476258465256354474118949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297270022574016945264317197 111476258465256354474118949)
          ·
            refine ⟨20901798462235566463897303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111476258465256354474118949 20901798462235566463897303)
            ·
              refine ⟨31352697693353349695845955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20901798462235566463897303 31352697693353349695845955)
              ·
                refine ⟨47029046540030024543768933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31352697693353349695845955 47029046540030024543768933)
                ·
                  refine ⟨8817946226255629601956675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47029046540030024543768933 8817946226255629601956675)
                  ·
                    refine ⟨13226919339383444402935013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8817946226255629601956675 13226919339383444402935013)
                    ·
                      refine ⟨2480047376134395825550315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13226919339383444402935013 2480047376134395825550315)
                      ·
                        rfl

theorem cell23_4829875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 4].length) (baseStart_4829875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829875 prefixEnd_4829875 := by exact prefixLift 4829875
  have htrace : WordTrace (prefixWord ++ tailWord_4829875) baseStart_4829875 baseEnd_4829875 := by
    simpa [prefixWord, tailWord_4829875, baseEnd_4829875] using wordTrace_append hprefix tailTrace_4829875
  have hstable : (prefixWord ++ tailWord_4829875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829875).length < 2 ^ (prefixWord ++ tailWord_4829875).sum := by decide
  have hdescent : baseEnd_4829875 < baseStart_4829875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829895 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 3]
def baseStart_4829895 : Nat := 118140960795 + 4829895 * 2 ^ 59
def prefixEnd_4829895 : Nat := 4983230072969 + 3 ^ 40 * 4829895 * 2
def baseEnd_4829895 : Nat := 2480057645747485747300223

theorem tailTrace_4829895 : CollatzResearch.WordTrace tailWord_4829895 prefixEnd_4829895 2480057645747485747300223 := by
  unfold tailWord_4829895
  simp only [CollatzResearch.WordTrace]
  refine ⟨176160742837122770239027139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117440495224748513492684759 176160742837122770239027139)
  ·
    refine ⟨264241114255684155358540709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176160742837122770239027139 264241114255684155358540709)
    ·
      refine ⟨49545208922940779129726383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 264241114255684155358540709 49545208922940779129726383)
      ·
        refine ⟨74317813384411168694589575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49545208922940779129726383 74317813384411168694589575)
        ·
          refine ⟨111476720076616753041884363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74317813384411168694589575 111476720076616753041884363)
          ·
            refine ⟨167215080114925129562826545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111476720076616753041884363 167215080114925129562826545)
            ·
              refine ⟨125411310086193847172119909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167215080114925129562826545 125411310086193847172119909)
              ·
                refine ⟨23514620641161346344772483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125411310086193847172119909 23514620641161346344772483)
                ·
                  refine ⟨35271930961742019517158725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23514620641161346344772483 35271930961742019517158725)
                  ·
                    refine ⟨6613487055326628659467261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35271930961742019517158725 6613487055326628659467261)
                    ·
                      refine ⟨2480057645747485747300223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6613487055326628659467261 2480057645747485747300223)
                      ·
                        rfl

theorem cell23_4829895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_4829895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829895 prefixEnd_4829895 := by exact prefixLift 4829895
  have htrace : WordTrace (prefixWord ++ tailWord_4829895) baseStart_4829895 baseEnd_4829895 := by
    simpa [prefixWord, tailWord_4829895, baseEnd_4829895] using wordTrace_append hprefix tailTrace_4829895
  have hstable : (prefixWord ++ tailWord_4829895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829895).length < 2 ^ (prefixWord ++ tailWord_4829895).sum := by decide
  have hdescent : baseEnd_4829895 < baseStart_4829895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829912 : List Nat := [2, 1, 2, 2, 3, 2, 1, 3, 2, 2, 3]
def baseStart_4829912 : Nat := 118140960795 + 4829912 * 2 ^ 59
def prefixEnd_4829912 : Nat := 4983230072969 + 3 ^ 40 * 4829912 * 2
def baseEnd_4829912 : Nat := 2480066374918612180787645

theorem tailTrace_4829912 : CollatzResearch.WordTrace tailWord_4829912 prefixEnd_4829912 2480066374918612180787645 := by
  unfold tailWord_4829912
  simp only [CollatzResearch.WordTrace]
  refine ⟨88080681439030591071197995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117440908585374121428263993 88080681439030591071197995)
  ·
    refine ⟨132121022158545886606796993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88080681439030591071197995 132121022158545886606796993)
    ·
      refine ⟨99090766618909414955097745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132121022158545886606796993 99090766618909414955097745)
      ·
        refine ⟨74318074964182061216323309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99090766618909414955097745 74318074964182061216323309)
        ·
          refine ⟨27869278111568272956121241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74318074964182061216323309 27869278111568272956121241)
          ·
            refine ⟨20901958583676204717090931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27869278111568272956121241 20901958583676204717090931)
            ·
              refine ⟨31352937875514307075636397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20901958583676204717090931 31352937875514307075636397)
              ·
                refine ⟨11757351703317865153363649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31352937875514307075636397 11757351703317865153363649)
                ·
                  refine ⟨8818013777488398865022737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11757351703317865153363649 8818013777488398865022737)
                  ·
                    refine ⟨6613510333116299148767053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8818013777488398865022737 6613510333116299148767053)
                    ·
                      refine ⟨2480066374918612180787645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6613510333116299148767053 2480066374918612180787645)
                      ·
                        rfl

theorem cell23_4829912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_4829912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829912 prefixEnd_4829912 := by exact prefixLift 4829912
  have htrace : WordTrace (prefixWord ++ tailWord_4829912) baseStart_4829912 baseEnd_4829912 := by
    simpa [prefixWord, tailWord_4829912, baseEnd_4829912] using wordTrace_append hprefix tailTrace_4829912
  have hstable : (prefixWord ++ tailWord_4829912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829912).length < 2 ^ (prefixWord ++ tailWord_4829912).sum := by decide
  have hdescent : baseEnd_4829912 < baseStart_4829912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829959 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 5, 1, 3]
def baseStart_4829959 : Nat := 118140960795 + 4829959 * 2 ^ 59
def prefixEnd_4829959 : Nat := 4983230072969 + 3 ^ 40 * 4829959 * 2
def baseEnd_4829959 : Nat := 2480090508509373496899929

theorem tailTrace_4829959 : CollatzResearch.WordTrace tailWord_4829959 prefixEnd_4829959 2480090508509373496899929 := by
  unfold tailWord_4829959
  simp only [CollatzResearch.WordTrace]
  refine ⟨176163077108890909169356931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117442051405927272779571287 176163077108890909169356931)
  ·
    refine ⟨264244615663336363754035397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176163077108890909169356931 264244615663336363754035397)
    ·
      refine ⟨49545865436875568203881637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 264244615663336363754035397 49545865436875568203881637)
      ·
        refine ⟨9289849769414169038227807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49545865436875568203881637 9289849769414169038227807)
        ·
          refine ⟨13934774654121253557341711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9289849769414169038227807 13934774654121253557341711)
          ·
            refine ⟨20902161981181880336012567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13934774654121253557341711 20902161981181880336012567)
            ·
              refine ⟨31353242971772820504018851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20902161981181880336012567 31353242971772820504018851)
              ·
                refine ⟨47029864457659230756028277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31353242971772820504018851 47029864457659230756028277)
                ·
                  refine ⟨4409049792905552883377651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47029864457659230756028277 4409049792905552883377651)
                  ·
                    refine ⟨6613574689358329325066477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4409049792905552883377651 6613574689358329325066477)
                    ·
                      refine ⟨2480090508509373496899929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6613574689358329325066477 2480090508509373496899929)
                      ·
                        rfl

theorem cell23_4829959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_4829959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829959 prefixEnd_4829959 := by exact prefixLift 4829959
  have htrace : WordTrace (prefixWord ++ tailWord_4829959) baseStart_4829959 baseEnd_4829959 := by
    simpa [prefixWord, tailWord_4829959, baseEnd_4829959] using wordTrace_append hprefix tailTrace_4829959
  have hstable : (prefixWord ++ tailWord_4829959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829959).length < 2 ^ (prefixWord ++ tailWord_4829959).sum := by decide
  have hdescent : baseEnd_4829959 < baseStart_4829959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829962 : List Nat := [3, 1, 2, 2, 1, 2, 2, 4, 1, 5]
def baseStart_4829962 : Nat := 118140960795 + 4829962 * 2 ^ 59
def prefixEnd_4829962 : Nat := 4983230072969 + 3 ^ 40 * 4829962 * 2
def baseEnd_4829962 : Nat := 826697349650445661720805

theorem tailTrace_4829962 : CollatzResearch.WordTrace tailWord_4829962 prefixEnd_4829962 826697349650445661720805 := by
  unfold tailWord_4829962
  simp only [CollatzResearch.WordTrace]
  refine ⟨44040796631970010170429035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117442124351920027121144093 44040796631970010170429035)
  ·
    refine ⟨66061194947955015255643553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44040796631970010170429035 66061194947955015255643553)
    ·
      refine ⟨49545896210966261441732665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66061194947955015255643553 49545896210966261441732665)
      ·
        refine ⟨37159422158224696081299499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49545896210966261441732665 37159422158224696081299499)
        ·
          refine ⟨55739133237337044121949249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37159422158224696081299499 55739133237337044121949249)
          ·
            refine ⟨41804349928002783091461937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55739133237337044121949249 41804349928002783091461937)
            ·
              refine ⟨31353262446002087318596453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41804349928002783091461937 31353262446002087318596453)
              ·
                refine ⟨5878736708625391372236835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31353262446002087318596453 5878736708625391372236835)
                ·
                  refine ⟨8818105062938087058355253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5878736708625391372236835 8818105062938087058355253)
                  ·
                    refine ⟨826697349650445661720805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8818105062938087058355253 826697349650445661720805)
                    ·
                      rfl

theorem cell23_4829962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_4829962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829962 prefixEnd_4829962 := by exact prefixLift 4829962
  have htrace : WordTrace (prefixWord ++ tailWord_4829962) baseStart_4829962 baseEnd_4829962 := by
    simpa [prefixWord, tailWord_4829962, baseEnd_4829962] using wordTrace_append hprefix tailTrace_4829962
  have hstable : (prefixWord ++ tailWord_4829962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829962).length < 2 ^ (prefixWord ++ tailWord_4829962).sum := by decide
  have hdescent : baseEnd_4829962 < baseStart_4829962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829969 : List Nat := [1, 2, 2, 1, 1, 3, 5, 1, 2, 3, 2]
def baseStart_4829969 : Nat := 118140960795 + 4829969 * 2 ^ 59
def prefixEnd_4829969 : Nat := 4983230072969 + 3 ^ 40 * 4829969 * 2
def baseEnd_4829969 : Nat := 2480095643315918457774883

theorem tailTrace_4829969 : CollatzResearch.WordTrace tailWord_4829969 prefixEnd_4829969 2480095643315918457774883 := by
  unfold tailWord_4829969
  simp only [CollatzResearch.WordTrace]
  refine ⟨176163441838854680877220961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117442294559236453918147307 176163441838854680877220961)
  ·
    refine ⟨132122581379141010657915721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176163441838854680877220961 132122581379141010657915721)
    ·
      refine ⟨99091936034355757993436791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132122581379141010657915721 99091936034355757993436791)
      ·
        refine ⟨148637904051533636990155187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99091936034355757993436791 148637904051533636990155187)
        ·
          refine ⟨222956856077300455485232781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148637904051533636990155187 222956856077300455485232781)
          ·
            refine ⟨83608821028987670806962293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222956856077300455485232781 83608821028987670806962293)
            ·
              refine ⟨7838326971467594138152715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83608821028987670806962293 7838326971467594138152715)
              ·
                refine ⟨11757490457201391207229073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7838326971467594138152715 11757490457201391207229073)
                ·
                  refine ⟨8818117842901043405421805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11757490457201391207229073 8818117842901043405421805)
                  ·
                    refine ⟨3306794191087891277033177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8818117842901043405421805 3306794191087891277033177)
                    ·
                      refine ⟨2480095643315918457774883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3306794191087891277033177 2480095643315918457774883)
                      ·
                        rfl

theorem cell23_4829969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 3, 2].length) (baseStart_4829969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829969 prefixEnd_4829969 := by exact prefixLift 4829969
  have htrace : WordTrace (prefixWord ++ tailWord_4829969) baseStart_4829969 baseEnd_4829969 := by
    simpa [prefixWord, tailWord_4829969, baseEnd_4829969] using wordTrace_append hprefix tailTrace_4829969
  have hstable : (prefixWord ++ tailWord_4829969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829969).length < 2 ^ (prefixWord ++ tailWord_4829969).sum := by decide
  have hdescent : baseEnd_4829969 < baseStart_4829969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4829995 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 4]
def baseStart_4829995 : Nat := 118140960795 + 4829995 * 2 ^ 59
def prefixEnd_4829995 : Nat := 4983230072969 + 3 ^ 40 * 4829995 * 2
def baseEnd_4829995 : Nat := 2480108993812935356049763

theorem tailTrace_4829995 : CollatzResearch.WordTrace tailWord_4829995 prefixEnd_4829995 2480108993812935356049763 := by
  unfold tailWord_4829995
  simp only [CollatzResearch.WordTrace]
  refine ⟨176164390136760487317667439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117442926757840324878444959 176164390136760487317667439)
  ·
    refine ⟨264246585205140730976501159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176164390136760487317667439 264246585205140730976501159)
    ·
      refine ⟨396369877807711096464751739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264246585205140730976501159 396369877807711096464751739)
      ·
        refine ⟨594554816711566644697127609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396369877807711096464751739 594554816711566644697127609)
        ·
          refine ⟨445916112533674983522845707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 594554816711566644697127609 445916112533674983522845707)
          ·
            refine ⟨668874168800512475284268561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445916112533674983522845707 668874168800512475284268561)
            ·
              refine ⟨501655626600384356463201421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 668874168800512475284268561 501655626600384356463201421)
              ·
                refine ⟨188120859975144133673700533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 501655626600384356463201421 188120859975144133673700533)
                ·
                  refine ⟨17636330622669762531909425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 188120859975144133673700533 17636330622669762531909425)
                  ·
                    refine ⟨13227247967002321898932069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17636330622669762531909425 13227247967002321898932069)
                    ·
                      refine ⟨2480108993812935356049763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13227247967002321898932069 2480108993812935356049763)
                      ·
                        rfl

theorem cell23_4829995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 4].length) (baseStart_4829995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4829995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4829995 prefixEnd_4829995 := by exact prefixLift 4829995
  have htrace : WordTrace (prefixWord ++ tailWord_4829995) baseStart_4829995 baseEnd_4829995 := by
    simpa [prefixWord, tailWord_4829995, baseEnd_4829995] using wordTrace_append hprefix tailTrace_4829995
  have hstable : (prefixWord ++ tailWord_4829995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4829995).length < 2 ^ (prefixWord ++ tailWord_4829995).sum := by decide
  have hdescent : baseEnd_4829995 < baseStart_4829995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4829995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830002 : List Nat := [3, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_4830002 : Nat := 118140960795 + 4830002 * 2 ^ 59
def prefixEnd_4830002 : Nat := 4983230072969 + 3 ^ 40 * 4830002 * 2
def baseEnd_4830002 : Nat := 2480112588177516828662231

theorem tailTrace_4830002 : CollatzResearch.WordTrace tailWord_4830002 prefixEnd_4830002 2480112588177516828662231 := by
  unfold tailWord_4830002
  simp only [CollatzResearch.WordTrace]
  refine ⟨44041161361933781878293065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117443096965156751675448173 44041161361933781878293065)
  ·
    refine ⟨33030871021450336408719799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44041161361933781878293065 33030871021450336408719799)
    ·
      refine ⟨49546306532175504613079699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33030871021450336408719799 49546306532175504613079699)
      ·
        refine ⟨74319459798263256919619549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49546306532175504613079699 74319459798263256919619549)
        ·
          refine ⟨27869797424348721344857331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74319459798263256919619549 27869797424348721344857331)
          ·
            refine ⟨41804696136523082017285997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27869797424348721344857331 41804696136523082017285997)
            ·
              refine ⟨15676761051196155756482249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41804696136523082017285997 15676761051196155756482249)
              ·
                refine ⟨11757570788397116817361687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15676761051196155756482249 11757570788397116817361687)
                ·
                  refine ⟨17636356182595675226042531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11757570788397116817361687 17636356182595675226042531)
                  ·
                    refine ⟨26454534273893512839063797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17636356182595675226042531 26454534273893512839063797)
                    ·
                      refine ⟨2480112588177516828662231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26454534273893512839063797 2480112588177516828662231)
                      ·
                        rfl

theorem cell23_4830002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_4830002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830002 prefixEnd_4830002 := by exact prefixLift 4830002
  have htrace : WordTrace (prefixWord ++ tailWord_4830002) baseStart_4830002 baseEnd_4830002 := by
    simpa [prefixWord, tailWord_4830002, baseEnd_4830002] using wordTrace_append hprefix tailTrace_4830002
  have hstable : (prefixWord ++ tailWord_4830002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830002).length < 2 ^ (prefixWord ++ tailWord_4830002).sum := by decide
  have hdescent : baseEnd_4830002 < baseStart_4830002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830019 : List Nat := [1, 1, 1, 3, 1, 4, 4, 2, 1, 2, 3]
def baseStart_4830019 : Nat := 118140960795 + 4830019 * 2 ^ 59
def prefixEnd_4830019 : Nat := 4983230072969 + 3 ^ 40 * 4830019 * 2
def baseEnd_4830019 : Nat := 2480121317348643262149653

theorem tailTrace_4830019 : CollatzResearch.WordTrace tailWord_4830019 prefixEnd_4830019 2480121317348643262149653 := by
  unfold tailWord_4830019
  simp only [CollatzResearch.WordTrace]
  refine ⟨176165265488673539416541111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117443510325782359611027407 176165265488673539416541111)
  ·
    refine ⟨264247898233010309124811667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176165265488673539416541111 264247898233010309124811667)
    ·
      refine ⟨396371847349515463687217501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264247898233010309124811667 396371847349515463687217501)
      ·
        refine ⟨148639442756068298882706563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 396371847349515463687217501 148639442756068298882706563)
        ·
          refine ⟨222959164134102448324059845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148639442756068298882706563 222959164134102448324059845)
          ·
            refine ⟨41804843275144209060761221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 222959164134102448324059845 41804843275144209060761221)
            ·
              refine ⟨7838408114089539198892729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41804843275144209060761221 7838408114089539198892729)
              ·
                refine ⟨5878806085567154399169547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7838408114089539198892729 5878806085567154399169547)
                ·
                  refine ⟨8818209128350731598754321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5878806085567154399169547 8818209128350731598754321)
                  ·
                    refine ⟨6613656846263048699065741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8818209128350731598754321 6613656846263048699065741)
                    ·
                      refine ⟨2480121317348643262149653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6613656846263048699065741 2480121317348643262149653)
                      ·
                        rfl

theorem cell23_4830019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 2, 3].length) (baseStart_4830019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830019 prefixEnd_4830019 := by exact prefixLift 4830019
  have htrace : WordTrace (prefixWord ++ tailWord_4830019) baseStart_4830019 baseEnd_4830019 := by
    simpa [prefixWord, tailWord_4830019, baseEnd_4830019] using wordTrace_append hprefix tailTrace_4830019
  have hstable : (prefixWord ++ tailWord_4830019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830019).length < 2 ^ (prefixWord ++ tailWord_4830019).sum := by decide
  have hdescent : baseEnd_4830019 < baseStart_4830019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830032 : List Nat := [2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 3]
def baseStart_4830032 : Nat := 118140960795 + 4830032 * 2 ^ 59
def prefixEnd_4830032 : Nat := 4983230072969 + 3 ^ 40 * 4830032 * 2
def baseEnd_4830032 : Nat := 2480127992597151711287093

theorem tailTrace_4830032 : CollatzResearch.WordTrace tailWord_4830032 prefixEnd_4830032 2480127992597151711287093 := by
  unfold tailWord_4830032
  simp only [CollatzResearch.WordTrace]
  refine ⟨88082869818813221318382175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117443826425084295091176233 88082869818813221318382175)
  ·
    refine ⟨132124304728219831977573263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88082869818813221318382175 132124304728219831977573263)
    ·
      refine ⟨198186457092329747966359895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132124304728219831977573263 198186457092329747966359895)
      ·
        refine ⟨297279685638494621949539843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198186457092329747966359895 297279685638494621949539843)
        ·
          refine ⟨445919528457741932924309765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297279685638494621949539843 445919528457741932924309765)
          ·
            refine ⟨83609911585826612423308081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 445919528457741932924309765 83609911585826612423308081)
            ·
              refine ⟨62707433689369959317481061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83609911585826612423308081 62707433689369959317481061)
              ·
                refine ⟨11757643816756867372027699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62707433689369959317481061 11757643816756867372027699)
                ·
                  refine ⟨17636465725135301058041549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11757643816756867372027699 17636465725135301058041549)
                  ·
                    refine ⟨6613674646925737896765581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17636465725135301058041549 6613674646925737896765581)
                    ·
                      refine ⟨2480127992597151711287093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6613674646925737896765581 2480127992597151711287093)
                      ·
                        rfl

theorem cell23_4830032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 3].length) (baseStart_4830032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830032 prefixEnd_4830032 := by exact prefixLift 4830032
  have htrace : WordTrace (prefixWord ++ tailWord_4830032) baseStart_4830032 baseEnd_4830032 := by
    simpa [prefixWord, tailWord_4830032, baseEnd_4830032] using wordTrace_append hprefix tailTrace_4830032
  have hstable : (prefixWord ++ tailWord_4830032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830032).length < 2 ^ (prefixWord ++ tailWord_4830032).sum := by decide
  have hdescent : baseEnd_4830032 < baseStart_4830032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830050 : List Nat := [3, 3, 2, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_4830050 : Nat := 118140960795 + 4830050 * 2 ^ 59
def prefixEnd_4830050 : Nat := 4983230072969 + 3 ^ 40 * 4830050 * 2
def baseEnd_4830050 : Nat := 2480137235248932640862011

theorem tailTrace_4830050 : CollatzResearch.WordTrace tailWord_4830050 prefixEnd_4830050 2480137235248932640862011 := by
  unfold tailWord_4830050
  simp only [CollatzResearch.WordTrace]
  refine ⟨44041599037890307927729901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117444264101040821140613069 44041599037890307927729901)
  ·
    refine ⟨16515599639208865472898713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44041599037890307927729901 16515599639208865472898713)
    ·
      refine ⟨12386699729406649104674035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16515599639208865472898713 12386699729406649104674035)
      ·
        refine ⟨18580049594109973657011053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12386699729406649104674035 18580049594109973657011053)
        ·
          refine ⟨6967518597791240121379145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18580049594109973657011053 6967518597791240121379145)
          ·
            refine ⟨5225638948343430091034359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6967518597791240121379145 5225638948343430091034359)
            ·
              refine ⟨7838458422515145136551539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5225638948343430091034359 7838458422515145136551539)
              ·
                refine ⟨11757687633772717704827309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7838458422515145136551539 11757687633772717704827309)
                ·
                  refine ⟨4409132862664769139310241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11757687633772717704827309 4409132862664769139310241)
                  ·
                    refine ⟨3306849646998576854482681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4409132862664769139310241 3306849646998576854482681)
                    ·
                      refine ⟨2480137235248932640862011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3306849646998576854482681 2480137235248932640862011)
                      ·
                        rfl

theorem cell23_4830050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_4830050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830050 prefixEnd_4830050 := by exact prefixLift 4830050
  have htrace : WordTrace (prefixWord ++ tailWord_4830050) baseStart_4830050 baseEnd_4830050 := by
    simpa [prefixWord, tailWord_4830050, baseEnd_4830050] using wordTrace_append hprefix tailTrace_4830050
  have hstable : (prefixWord ++ tailWord_4830050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830050).length < 2 ^ (prefixWord ++ tailWord_4830050).sum := by decide
  have hdescent : baseEnd_4830050 < baseStart_4830050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830089 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 3, 4, 2]
def baseStart_4830089 : Nat := 118140960795 + 4830089 * 2 ^ 59
def prefixEnd_4830089 : Nat := 4983230072969 + 3 ^ 40 * 4830089 * 2
def baseEnd_4830089 : Nat := 2480157260994457988274331

theorem tailTrace_4830089 : CollatzResearch.WordTrace tailWord_4830089 prefixEnd_4830089 2480157260994457988274331 := by
  unfold tailWord_4830089
  simp only [CollatzResearch.WordTrace]
  refine ⟨176167818598419941371589321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117445212398946627581059547 176167818598419941371589321)
  ·
    refine ⟨132125863948814956028691991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176167818598419941371589321 132125863948814956028691991)
    ·
      refine ⟨198188795923222434043037987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132125863948814956028691991 198188795923222434043037987)
      ·
        refine ⟨297283193884833651064556981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198188795923222434043037987 297283193884833651064556981)
        ·
          refine ⟨27870299426703154787302217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 297283193884833651064556981 27870299426703154787302217)
          ·
            refine ⟨20902724570027366090476663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27870299426703154787302217 20902724570027366090476663)
            ·
              refine ⟨31354086855041049135714995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20902724570027366090476663 31354086855041049135714995)
              ·
                refine ⟨47031130282561573703572493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31354086855041049135714995 47031130282561573703572493)
                ·
                  refine ⟨17636673855960590138839685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47031130282561573703572493 17636673855960590138839685)
                  ·
                    refine ⟨3306876347992610651032441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17636673855960590138839685 3306876347992610651032441)
                    ·
                      refine ⟨2480157260994457988274331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3306876347992610651032441 2480157260994457988274331)
                      ·
                        rfl

theorem cell23_4830089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 4, 2].length) (baseStart_4830089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830089 prefixEnd_4830089 := by exact prefixLift 4830089
  have htrace : WordTrace (prefixWord ++ tailWord_4830089) baseStart_4830089 baseEnd_4830089 := by
    simpa [prefixWord, tailWord_4830089, baseEnd_4830089] using wordTrace_append hprefix tailTrace_4830089
  have hstable : (prefixWord ++ tailWord_4830089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830089).length < 2 ^ (prefixWord ++ tailWord_4830089).sum := by decide
  have hdescent : baseEnd_4830089 < baseStart_4830089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830092 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 2, 1, 5]
def baseStart_4830092 : Nat := 118140960795 + 4830092 * 2 ^ 59
def prefixEnd_4830092 : Nat := 4983230072969 + 3 ^ 40 * 4830092 * 2
def baseEnd_4830092 : Nat := 2480158801436421476536817

theorem tailTrace_4830092 : CollatzResearch.WordTrace tailWord_4830092 prefixEnd_4830092 2480158801436421476536817 := by
  unfold tailWord_4830092
  simp only [CollatzResearch.WordTrace]
  refine ⟨88083964008704536441974265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117445285344939381922632353 88083964008704536441974265)
  ·
    refine ⟨66062973006528402331480699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88083964008704536441974265 66062973006528402331480699)
    ·
      refine ⟨99094459509792603497221049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66062973006528402331480699 99094459509792603497221049)
      ·
        refine ⟨74320844632344452622915787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99094459509792603497221049 74320844632344452622915787)
        ·
          refine ⟨111481266948516678934373681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74320844632344452622915787 111481266948516678934373681)
          ·
            refine ⟨83610950211387509200780261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111481266948516678934373681 83610950211387509200780261)
            ·
              refine ⟨15677053164635157975146299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83610950211387509200780261 15677053164635157975146299)
              ·
                refine ⟨23515579746952736962719449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15677053164635157975146299 23515579746952736962719449)
                ·
                  refine ⟨17636684810214552722039587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23515579746952736962719449 17636684810214552722039587)
                  ·
                    refine ⟨26455027215321829083059381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17636684810214552722039587 26455027215321829083059381)
                    ·
                      refine ⟨2480158801436421476536817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26455027215321829083059381 2480158801436421476536817)
                      ·
                        rfl

theorem cell23_4830092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_4830092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830092 prefixEnd_4830092 := by exact prefixLift 4830092
  have htrace : WordTrace (prefixWord ++ tailWord_4830092) baseStart_4830092 baseEnd_4830092 := by
    simpa [prefixWord, tailWord_4830092, baseEnd_4830092] using wordTrace_append hprefix tailTrace_4830092
  have hstable : (prefixWord ++ tailWord_4830092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830092).length < 2 ^ (prefixWord ++ tailWord_4830092).sum := by decide
  have hdescent : baseEnd_4830092 < baseStart_4830092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830129 : List Nat := [1, 2, 2, 4, 3, 1, 1, 2, 7]
def baseStart_4830129 : Nat := 118140960795 + 4830129 * 2 ^ 59
def prefixEnd_4830129 : Nat := 4983230072969 + 3 ^ 40 * 4830129 * 2
def baseEnd_4830129 : Nat := 275575311135626425752683

theorem tailTrace_4830129 : CollatzResearch.WordTrace tailWord_4830129 prefixEnd_4830129 275575311135626425752683 := by
  unfold tailWord_4830129
  simp only [CollatzResearch.WordTrace]
  refine ⟨176169277518275028203045441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117446185012183352135363627 176169277518275028203045441)
  ·
    refine ⟨132126958138706271152284081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176169277518275028203045441 132126958138706271152284081)
    ·
      refine ⟨99095218604029703364213061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132126958138706271152284081 99095218604029703364213061)
      ·
        refine ⟨18580353488255569380789949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99095218604029703364213061 18580353488255569380789949)
        ·
          refine ⟨6967632558095838517796231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18580353488255569380789949 6967632558095838517796231)
          ·
            refine ⟨10451448837143757776694347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6967632558095838517796231 10451448837143757776694347)
            ·
              refine ⟨15677173255715636665041521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10451448837143757776694347 15677173255715636665041521)
              ·
                refine ⟨11757879941786727498781141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15677173255715636665041521 11757879941786727498781141)
                ·
                  refine ⟨275575311135626425752683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11757879941786727498781141 275575311135626425752683)
                  ·
                    rfl

theorem cell23_4830129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 7].length) (baseStart_4830129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830129 prefixEnd_4830129 := by exact prefixLift 4830129
  have htrace : WordTrace (prefixWord ++ tailWord_4830129) baseStart_4830129 baseEnd_4830129 := by
    simpa [prefixWord, tailWord_4830129, baseEnd_4830129] using wordTrace_append hprefix tailTrace_4830129
  have hstable : (prefixWord ++ tailWord_4830129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830129).length < 2 ^ (prefixWord ++ tailWord_4830129).sum := by decide
  have hdescent : baseEnd_4830129 < baseStart_4830129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830192 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 4]
def baseStart_4830192 : Nat := 118140960795 + 4830192 * 2 ^ 59
def prefixEnd_4830192 : Nat := 4983230072969 + 3 ^ 40 * 4830192 * 2
def baseEnd_4830192 : Nat := 2480210149501871085286357

theorem tailTrace_4830192 : CollatzResearch.WordTrace tailWord_4830192 prefixEnd_4830192 2480210149501871085286357 := by
  unfold tailWord_4830192
  simp only [CollatzResearch.WordTrace]
  refine ⟨88085787658523394981294415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117447716878031193308392553 88085787658523394981294415)
  ·
    refine ⟨132128681487785092471941623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88085787658523394981294415 132128681487785092471941623)
    ·
      refine ⟨198193022231677638707912435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132128681487785092471941623 198193022231677638707912435)
      ·
        refine ⟨297289533347516458061868653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198193022231677638707912435 297289533347516458061868653)
        ·
          refine ⟨111483575005318671773200745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297289533347516458061868653 111483575005318671773200745)
          ·
            refine ⟨83612681253989003829900559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111483575005318671773200745 83612681253989003829900559)
            ·
              refine ⟨125419021880983505744850839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83612681253989003829900559 125419021880983505744850839)
              ·
                refine ⟨188128532821475258617276259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125419021880983505744850839 188128532821475258617276259)
                ·
                  refine ⟨282192799232212887925914389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188128532821475258617276259 282192799232212887925914389)
                  ·
                    refine ⟨13227787464009979121527237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 282192799232212887925914389 13227787464009979121527237)
                    ·
                      refine ⟨2480210149501871085286357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13227787464009979121527237 2480210149501871085286357)
                      ·
                        rfl

theorem cell23_4830192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_4830192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830192 prefixEnd_4830192 := by exact prefixLift 4830192
  have htrace : WordTrace (prefixWord ++ tailWord_4830192) baseStart_4830192 baseEnd_4830192 := by
    simpa [prefixWord, tailWord_4830192, baseEnd_4830192] using wordTrace_append hprefix tailTrace_4830192
  have hstable : (prefixWord ++ tailWord_4830192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830192).length < 2 ^ (prefixWord ++ tailWord_4830192).sum := by decide
  have hdescent : baseEnd_4830192 < baseStart_4830192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830197 : List Nat := [1, 3, 5, 2, 2, 1, 1, 3, 5]
def baseStart_4830197 : Nat := 118140960795 + 4830197 * 2 ^ 59
def prefixEnd_4830197 : Nat := 4983230072969 + 3 ^ 40 * 4830197 * 2
def baseEnd_4830197 : Nat := 275579190767238173969315

theorem tailTrace_4830197 : CollatzResearch.WordTrace tailWord_4830197 prefixEnd_4830197 275579190767238173969315 := by
  unfold tailWord_4830197
  simp only [CollatzResearch.WordTrace]
  refine ⟨176171757682028675816520845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117447838454685783877680563 176171757682028675816520845)
  ·
    refine ⟨66064409130760753431195317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176171757682028675816520845 66064409130760753431195317)
    ·
      refine ⟨6193538356008820634174561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66064409130760753431195317 6193538356008820634174561)
      ·
        refine ⟨4645153767006615475630921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6193538356008820634174561 4645153767006615475630921)
        ·
          refine ⟨3483865325254961606723191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4645153767006615475630921 3483865325254961606723191)
          ·
            refine ⟨5225797987882442410084787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3483865325254961606723191 5225797987882442410084787)
            ·
              refine ⟨7838696981823663615127181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5225797987882442410084787 7838696981823663615127181)
              ·
                refine ⟨2939511368183873855672693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7838696981823663615127181 2939511368183873855672693)
                ·
                  refine ⟨275579190767238173969315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2939511368183873855672693 275579190767238173969315)
                  ·
                    rfl

theorem cell23_4830197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 5].length) (baseStart_4830197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830197 prefixEnd_4830197 := by exact prefixLift 4830197
  have htrace : WordTrace (prefixWord ++ tailWord_4830197) baseStart_4830197 baseEnd_4830197 := by
    simpa [prefixWord, tailWord_4830197, baseEnd_4830197] using wordTrace_append hprefix tailTrace_4830197
  have hstable : (prefixWord ++ tailWord_4830197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830197).length < 2 ^ (prefixWord ++ tailWord_4830197).sum := by decide
  have hdescent : baseEnd_4830197 < baseStart_4830197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830216 : List Nat := [2, 1, 3, 2, 1, 4, 1, 2, 2, 2, 3]
def baseStart_4830216 : Nat := 118140960795 + 4830216 * 2 ^ 59
def prefixEnd_4830216 : Nat := 4983230072969 + 3 ^ 40 * 4830216 * 2
def baseEnd_4830216 : Nat := 2480222473037578991386247

theorem tailTrace_4830216 : CollatzResearch.WordTrace tailWord_4830216 prefixEnd_4830216 2480222473037578991386247 := by
  unfold tailWord_4830216
  simp only [CollatzResearch.WordTrace]
  refine ⟨88086225334479921030731251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117448300445973228040975001 88086225334479921030731251)
  ·
    refine ⟨132129338001719881546096877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88086225334479921030731251 132129338001719881546096877)
    ·
      refine ⟨49548501750644955579786329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132129338001719881546096877 49548501750644955579786329)
      ·
        refine ⟨37161376312983716684839747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49548501750644955579786329 37161376312983716684839747)
        ·
          refine ⟨55742064469475575027259621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37161376312983716684839747 55742064469475575027259621)
          ·
            refine ⟨10451637088026670317611179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55742064469475575027259621 10451637088026670317611179)
            ·
              refine ⟨15677455632040005476416769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10451637088026670317611179 15677455632040005476416769)
              ·
                refine ⟨11758091724030004107312577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15677455632040005476416769 11758091724030004107312577)
                ·
                  refine ⟨8818568793022503080484433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11758091724030004107312577 8818568793022503080484433)
                  ·
                    refine ⟨6613926594766877310363325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8818568793022503080484433 6613926594766877310363325)
                    ·
                      refine ⟨2480222473037578991386247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6613926594766877310363325 2480222473037578991386247)
                      ·
                        rfl

theorem cell23_4830216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_4830216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830216 prefixEnd_4830216 := by exact prefixLift 4830216
  have htrace : WordTrace (prefixWord ++ tailWord_4830216) baseStart_4830216 baseEnd_4830216 := by
    simpa [prefixWord, tailWord_4830216, baseEnd_4830216] using wordTrace_append hprefix tailTrace_4830216
  have hstable : (prefixWord ++ tailWord_4830216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830216).length < 2 ^ (prefixWord ++ tailWord_4830216).sum := by decide
  have hdescent : baseEnd_4830216 < baseStart_4830216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830236 : List Nat := [2, 2, 3, 1, 4, 1, 1, 3, 6]
def baseStart_4830236 : Nat := 118140960795 + 4830236 * 2 ^ 59
def prefixEnd_4830236 : Nat := 4983230072969 + 3 ^ 40 * 4830236 * 2
def baseEnd_4830236 : Nat := 275581415850074323681795

theorem tailTrace_4830236 : CollatzResearch.WordTrace tailWord_4830236 prefixEnd_4830236 275581415850074323681795 := by
  unfold tailWord_4830236
  simp only [CollatzResearch.WordTrace]
  refine ⟨88086590064443692738595281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117448786752591590318127041 88086590064443692738595281)
  ·
    refine ⟨66064942548332769553946461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88086590064443692738595281 66064942548332769553946461)
    ·
      refine ⟨24774353455624788582729923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66064942548332769553946461 24774353455624788582729923)
      ·
        refine ⟨37161530183437182874094885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24774353455624788582729923 37161530183437182874094885)
        ·
          refine ⟨6967786909394471788892791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37161530183437182874094885 6967786909394471788892791)
          ·
            refine ⟨10451680364091707683339187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6967786909394471788892791 10451680364091707683339187)
            ·
              refine ⟨15677520546137561525008781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10451680364091707683339187 15677520546137561525008781)
              ·
                refine ⟨5879070204801585571878293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15677520546137561525008781 5879070204801585571878293)
                ·
                  refine ⟨275581415850074323681795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5879070204801585571878293 275581415850074323681795)
                  ·
                    rfl

theorem cell23_4830236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 6].length) (baseStart_4830236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830236 prefixEnd_4830236 := by exact prefixLift 4830236
  have htrace : WordTrace (prefixWord ++ tailWord_4830236) baseStart_4830236 baseEnd_4830236 := by
    simpa [prefixWord, tailWord_4830236, baseEnd_4830236] using wordTrace_append hprefix tailTrace_4830236
  have hstable : (prefixWord ++ tailWord_4830236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830236).length < 2 ^ (prefixWord ++ tailWord_4830236).sum := by decide
  have hdescent : baseEnd_4830236 < baseStart_4830236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830263 : List Nat := [1, 1, 3, 1, 2, 2, 1, 7, 1, 1, 3]
def baseStart_4830263 : Nat := 118140960795 + 4830263 * 2 ^ 59
def prefixEnd_4830263 : Nat := 4983230072969 + 3 ^ 40 * 4830263 * 2
def baseEnd_4830263 : Nat := 2480246606628340307498531

theorem tailTrace_4830263 : CollatzResearch.WordTrace tailWord_4830263 prefixEnd_4830263 2480246606628340307498531 := by
  unfold tailWord_4830263
  simp only [CollatzResearch.WordTrace]
  refine ⟨176174164899789569088423443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117449443266526379392282295 176174164899789569088423443)
  ·
    refine ⟨264261247349684353632635165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176174164899789569088423443 264261247349684353632635165)
    ·
      refine ⟨99097967756131632612238187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264261247349684353632635165 99097967756131632612238187)
      ·
        refine ⟨148646951634197448918357281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99097967756131632612238187 148646951634197448918357281)
        ·
          refine ⟨111485213725648086688767961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148646951634197448918357281 111485213725648086688767961)
          ·
            refine ⟨83613910294236065016575971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111485213725648086688767961 83613910294236065016575971)
            ·
              refine ⟨125420865441354097524863957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83613910294236065016575971 125420865441354097524863957)
              ·
                refine ⟨2939551533781736660738999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 125420865441354097524863957 2939551533781736660738999)
                ·
                  refine ⟨4409327300672604991108499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2939551533781736660738999 4409327300672604991108499)
                  ·
                    refine ⟨6613990951008907486662749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4409327300672604991108499 6613990951008907486662749)
                    ·
                      refine ⟨2480246606628340307498531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6613990951008907486662749 2480246606628340307498531)
                      ·
                        rfl

theorem cell23_4830263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 1, 1, 3].length) (baseStart_4830263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830263 prefixEnd_4830263 := by exact prefixLift 4830263
  have htrace : WordTrace (prefixWord ++ tailWord_4830263) baseStart_4830263 baseEnd_4830263 := by
    simpa [prefixWord, tailWord_4830263, baseEnd_4830263] using wordTrace_append hprefix tailTrace_4830263
  have hstable : (prefixWord ++ tailWord_4830263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830263).length < 2 ^ (prefixWord ++ tailWord_4830263).sum := by decide
  have hdescent : baseEnd_4830263 < baseStart_4830263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830289 : List Nat := [1, 2, 2, 1, 3, 1, 2, 4, 1, 1, 5]
def baseStart_4830289 : Nat := 118140960795 + 4830289 * 2 ^ 59
def prefixEnd_4830289 : Nat := 4983230072969 + 3 ^ 40 * 4830289 * 2
def baseEnd_4830289 : Nat := 2480259957125357205773411

theorem tailTrace_4830289 : CollatzResearch.WordTrace tailWord_4830289 prefixEnd_4830289 2480259957125357205773411 := by
  unfold tailWord_4830289
  simp only [CollatzResearch.WordTrace]
  refine ⟨176175113197695375528869921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117450075465130250352579947 176175113197695375528869921)
  ·
    refine ⟨132131334898271531646652441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176175113197695375528869921 132131334898271531646652441)
    ·
      refine ⟨99098501173703648734989331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132131334898271531646652441 99098501173703648734989331)
      ·
        refine ⟨148647751760555473102483997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99098501173703648734989331 148647751760555473102483997)
        ·
          refine ⟨55742906910208302413431499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148647751760555473102483997 55742906910208302413431499)
          ·
            refine ⟨83614360365312453620147249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55742906910208302413431499 83614360365312453620147249)
            ·
              refine ⟨62710770273984340215110437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83614360365312453620147249 62710770273984340215110437)
              ·
                refine ⟨11758269426372063790333207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62710770273984340215110437 11758269426372063790333207)
                ·
                  refine ⟨17637404139558095685499811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11758269426372063790333207 17637404139558095685499811)
                  ·
                    refine ⟨26456106209337143528249717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17637404139558095685499811 26456106209337143528249717)
                    ·
                      refine ⟨2480259957125357205773411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26456106209337143528249717 2480259957125357205773411)
                      ·
                        rfl

theorem cell23_4830289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_4830289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830289 prefixEnd_4830289 := by exact prefixLift 4830289
  have htrace : WordTrace (prefixWord ++ tailWord_4830289) baseStart_4830289 baseEnd_4830289 := by
    simpa [prefixWord, tailWord_4830289, baseEnd_4830289] using wordTrace_append hprefix tailTrace_4830289
  have hstable : (prefixWord ++ tailWord_4830289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830289).length < 2 ^ (prefixWord ++ tailWord_4830289).sum := by decide
  have hdescent : baseEnd_4830289 < baseStart_4830289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830296 : List Nat := [2, 1, 2, 2, 1, 3, 1, 5, 2, 4]
def baseStart_4830296 : Nat := 118140960795 + 4830296 * 2 ^ 59
def prefixEnd_4830296 : Nat := 4983230072969 + 3 ^ 40 * 4830296 * 2
def baseEnd_4830296 : Nat := 826754517163312892795293

theorem tailTrace_4830296 : CollatzResearch.WordTrace tailWord_4830296 prefixEnd_4830296 826754517163312892795293 := by
  unfold tailWord_4830296
  simp only [CollatzResearch.WordTrace]
  refine ⟨88087684254335007862187371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117450245672446677149583161 88087684254335007862187371)
  ·
    refine ⟨132131526381502511793281057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88087684254335007862187371 132131526381502511793281057)
    ·
      refine ⟨99098644786126883844960793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132131526381502511793281057 99098644786126883844960793)
      ·
        refine ⟨74323983589595162883720595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99098644786126883844960793 74323983589595162883720595)
        ·
          refine ⟨111485975384392744325580893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74323983589595162883720595 111485975384392744325580893)
          ·
            refine ⟨41807240769147279122092835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111485975384392744325580893 41807240769147279122092835)
            ·
              refine ⟨62710861153720918683139253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41807240769147279122092835 62710861153720918683139253)
              ·
                refine ⟨5879143233161336126544305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62710861153720918683139253 5879143233161336126544305)
                ·
                  refine ⟨4409357424871002094908229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5879143233161336126544305 4409357424871002094908229)
                  ·
                    refine ⟨826754517163312892795293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4409357424871002094908229 826754517163312892795293)
                    ·
                      rfl

theorem cell23_4830296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_4830296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830296 prefixEnd_4830296 := by exact prefixLift 4830296
  have htrace : WordTrace (prefixWord ++ tailWord_4830296) baseStart_4830296 baseEnd_4830296 := by
    simpa [prefixWord, tailWord_4830296, baseEnd_4830296] using wordTrace_append hprefix tailTrace_4830296
  have hstable : (prefixWord ++ tailWord_4830296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830296).length < 2 ^ (prefixWord ++ tailWord_4830296).sum := by decide
  have hdescent : baseEnd_4830296 < baseStart_4830296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830303 : List Nat := [1, 1, 2, 3, 1, 1, 5, 2, 3, 2, 2]
def baseStart_4830303 : Nat := 118140960795 + 4830303 * 2 ^ 59
def prefixEnd_4830303 : Nat := 4983230072969 + 3 ^ 40 * 4830303 * 2
def baseEnd_4830303 : Nat := 2480267145854520150998347

theorem tailTrace_4830303 : CollatzResearch.WordTrace tailWord_4830303 prefixEnd_4830303 2480267145854520150998347 := by
  unfold tailWord_4830303
  simp only [CollatzResearch.WordTrace]
  refine ⟨176175623819644655919879563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117450415879763103946586375 176175623819644655919879563)
  ·
    refine ⟨264263435729466983879819345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176175623819644655919879563 264263435729466983879819345)
    ·
      refine ⟨198197576797100237909864509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264263435729466983879819345 198197576797100237909864509)
      ·
        refine ⟨74324091298912589216199191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198197576797100237909864509 74324091298912589216199191)
        ·
          refine ⟨111486136948368883824298787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74324091298912589216199191 111486136948368883824298787)
          ·
            refine ⟨167229205422553325736448181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111486136948368883824298787 167229205422553325736448181)
            ·
              refine ⟨15677738008364374287792017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 167229205422553325736448181 15677738008364374287792017)
              ·
                refine ⟨11758303506273280715844013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15677738008364374287792017 11758303506273280715844013)
                ·
                  refine ⟨4409363814852480268441505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11758303506273280715844013 4409363814852480268441505)
                  ·
                    refine ⟨3307022861139360201331129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4409363814852480268441505 3307022861139360201331129)
                    ·
                      refine ⟨2480267145854520150998347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3307022861139360201331129 2480267145854520150998347)
                      ·
                        rfl

theorem cell23_4830303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_4830303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830303 prefixEnd_4830303 := by exact prefixLift 4830303
  have htrace : WordTrace (prefixWord ++ tailWord_4830303) baseStart_4830303 baseEnd_4830303 := by
    simpa [prefixWord, tailWord_4830303, baseEnd_4830303] using wordTrace_append hprefix tailTrace_4830303
  have hstable : (prefixWord ++ tailWord_4830303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830303).length < 2 ^ (prefixWord ++ tailWord_4830303).sum := by decide
  have hdescent : baseEnd_4830303 < baseStart_4830303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830337 : List Nat := [1, 2, 4, 2, 2, 1, 2, 4, 1, 2, 2]
def baseStart_4830337 : Nat := 118140960795 + 4830337 * 2 ^ 59
def prefixEnd_4830337 : Nat := 4983230072969 + 3 ^ 40 * 4830337 * 2
def baseEnd_4830337 : Nat := 2480284604196773017973191

theorem tailTrace_4830337 : CollatzResearch.WordTrace tailWord_4830337 prefixEnd_4830337 2480284604196773017973191 := by
  unfold tailWord_4830337
  simp only [CollatzResearch.WordTrace]
  refine ⟨176176863901521479726617265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117451242601014319817744843 176176863901521479726617265)
  ·
    refine ⟨132132647926141109794962949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176176863901521479726617265 132132647926141109794962949)
    ·
      refine ⟨24774871486151458086555553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132132647926141109794962949 24774871486151458086555553)
      ·
        refine ⟨18581153614613593564916665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24774871486151458086555553 18581153614613593564916665)
        ·
          refine ⟨13935865210960195173687499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18581153614613593564916665 13935865210960195173687499)
          ·
            refine ⟨20903797816440292760531249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13935865210960195173687499 20903797816440292760531249)
            ·
              refine ⟨15677848362330219570398437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20903797816440292760531249 15677848362330219570398437)
              ·
                refine ⟨2939596567936916169449707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15677848362330219570398437 2939596567936916169449707)
                ·
                  refine ⟨4409394851905374254174561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2939596567936916169449707 4409394851905374254174561)
                  ·
                    refine ⟨3307046138929030690630921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4409394851905374254174561 3307046138929030690630921)
                    ·
                      refine ⟨2480284604196773017973191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3307046138929030690630921 2480284604196773017973191)
                      ·
                        rfl

theorem cell23_4830337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_4830337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830337 prefixEnd_4830337 := by exact prefixLift 4830337
  have htrace : WordTrace (prefixWord ++ tailWord_4830337) baseStart_4830337 baseEnd_4830337 := by
    simpa [prefixWord, tailWord_4830337, baseEnd_4830337] using wordTrace_append hprefix tailTrace_4830337
  have hstable : (prefixWord ++ tailWord_4830337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830337).length < 2 ^ (prefixWord ++ tailWord_4830337).sum := by decide
  have hdescent : baseEnd_4830337 < baseStart_4830337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830404 : List Nat := [2, 3, 3, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_4830404 : Nat := 118140960795 + 4830404 * 2 ^ 59
def prefixEnd_4830404 : Nat := 4983230072969 + 3 ^ 40 * 4830404 * 2
def baseEnd_4830404 : Nat := 2480319007400624255835383

theorem tailTrace_4830404 : CollatzResearch.WordTrace tailWord_4830404 prefixEnd_4830404 2480319007400624255835383 := by
  unfold tailWord_4830404
  simp only [CollatzResearch.WordTrace]
  refine ⟨88089653796139375084653133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117452871728185833446204177 88089653796139375084653133)
  ·
    refine ⟨33033620173552265656744925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88089653796139375084653133 33033620173552265656744925)
    ·
      refine ⟨12387607565082099621279347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33033620173552265656744925 12387607565082099621279347)
      ·
        refine ⟨18581411347623149431919021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12387607565082099621279347 18581411347623149431919021)
        ·
          refine ⟨6968029255358681036969633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18581411347623149431919021 6968029255358681036969633)
          ·
            refine ⟨5226021941519010777727225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6968029255358681036969633 5226021941519010777727225)
            ·
              refine ⟨3919516456139258083295419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5226021941519010777727225 3919516456139258083295419)
              ·
                refine ⟨5879274684208887124943129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3919516456139258083295419 5879274684208887124943129)
                ·
                  refine ⟨4409456013156665343707347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5879274684208887124943129 4409456013156665343707347)
                  ·
                    refine ⟨6614184019734998015561021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4409456013156665343707347 6614184019734998015561021)
                    ·
                      refine ⟨2480319007400624255835383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6614184019734998015561021 2480319007400624255835383)
                      ·
                        rfl

theorem cell23_4830404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_4830404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830404 prefixEnd_4830404 := by exact prefixLift 4830404
  have htrace : WordTrace (prefixWord ++ tailWord_4830404) baseStart_4830404 baseEnd_4830404 := by
    simpa [prefixWord, tailWord_4830404, baseEnd_4830404] using wordTrace_append hprefix tailTrace_4830404
  have hstable : (prefixWord ++ tailWord_4830404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830404).length < 2 ^ (prefixWord ++ tailWord_4830404).sum := by decide
  have hdescent : baseEnd_4830404 < baseStart_4830404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830414 : List Nat := [4, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2]
def baseStart_4830414 : Nat := 118140960795 + 4830414 * 2 ^ 59
def prefixEnd_4830414 : Nat := 4983230072969 + 3 ^ 40 * 4830414 * 2
def baseEnd_4830414 : Nat := 2480324142207169216710337

theorem tailTrace_4830414 : CollatzResearch.WordTrace tailWord_4830414 prefixEnd_4830414 2480324142207169216710337 := by
  unfold tailWord_4830414
  simp only [CollatzResearch.WordTrace]
  refine ⟨22022459040280315234646287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117453114881495014584780197 22022459040280315234646287)
  ·
    refine ⟨33033688560420472851969431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22022459040280315234646287 33033688560420472851969431)
    ·
      refine ⟨49550532840630709277954147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33033688560420472851969431 49550532840630709277954147)
      ·
        refine ⟨74325799260946063916931221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49550532840630709277954147 74325799260946063916931221)
        ·
          refine ⟨3484021840356846746106151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74325799260946063916931221 3484021840356846746106151)
          ·
            refine ⟨5226032760535270119159227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3484021840356846746106151 5226032760535270119159227)
            ·
              refine ⟨7839049140802905178738841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5226032760535270119159227 7839049140802905178738841)
              ·
                refine ⟨5879286855602178884054131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7839049140802905178738841 5879286855602178884054131)
                ·
                  refine ⟨8818930283403268326081197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5879286855602178884054131 8818930283403268326081197)
                  ·
                    refine ⟨3307098856276225622280449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8818930283403268326081197 3307098856276225622280449)
                    ·
                      refine ⟨2480324142207169216710337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3307098856276225622280449 2480324142207169216710337)
                      ·
                        rfl

theorem cell23_4830414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_4830414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830414 prefixEnd_4830414 := by exact prefixLift 4830414
  have htrace : WordTrace (prefixWord ++ tailWord_4830414) baseStart_4830414 baseEnd_4830414 := by
    simpa [prefixWord, tailWord_4830414, baseEnd_4830414] using wordTrace_append hprefix tailTrace_4830414
  have hstable : (prefixWord ++ tailWord_4830414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830414).length < 2 ^ (prefixWord ++ tailWord_4830414).sum := by decide
  have hdescent : baseEnd_4830414 < baseStart_4830414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830426 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3]
def baseStart_4830426 : Nat := 118140960795 + 4830426 * 2 ^ 59
def prefixEnd_4830426 : Nat := 4983230072969 + 3 ^ 40 * 4830426 * 2
def baseEnd_4830426 : Nat := 2480330303975023169760281

theorem tailTrace_4830426 : CollatzResearch.WordTrace tailWord_4830426 prefixEnd_4830426 2480330303975023169760281 := by
  unfold tailWord_4830426
  simp only [CollatzResearch.WordTrace]
  refine ⟨44045027499549761981651783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117453406665466031951071421 44045027499549761981651783)
  ·
    refine ⟨66067541249324642972477675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44045027499549761981651783 66067541249324642972477675)
    ·
      refine ⟨99101311873986964458716513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66067541249324642972477675 99101311873986964458716513)
      ·
        refine ⟨74325983905490223344037385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99101311873986964458716513 74325983905490223344037385)
        ·
          refine ⟨55744487929117667508028039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74325983905490223344037385 55744487929117667508028039)
          ·
            refine ⟨83616731893676501262042059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55744487929117667508028039 83616731893676501262042059)
            ·
              refine ⟨125425097840514751893063089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83616731893676501262042059 125425097840514751893063089)
              ·
                refine ⟨94068823380386063919797317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125425097840514751893063089 94068823380386063919797317)
                ·
                  refine ⟨17637904383822386984961997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94068823380386063919797317 17637904383822386984961997)
                  ·
                    refine ⟨6614214143933395119360749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17637904383822386984961997 6614214143933395119360749)
                    ·
                      refine ⟨2480330303975023169760281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6614214143933395119360749 2480330303975023169760281)
                      ·
                        rfl

theorem cell23_4830426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_4830426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830426 prefixEnd_4830426 := by exact prefixLift 4830426
  have htrace : WordTrace (prefixWord ++ tailWord_4830426) baseStart_4830426 baseEnd_4830426 := by
    simpa [prefixWord, tailWord_4830426, baseEnd_4830426] using wordTrace_append hprefix tailTrace_4830426
  have hstable : (prefixWord ++ tailWord_4830426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830426).length < 2 ^ (prefixWord ++ tailWord_4830426).sum := by decide
  have hdescent : baseEnd_4830426 < baseStart_4830426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830450 : List Nat := [3, 2, 1, 3, 3, 1, 1, 4, 5]
def baseStart_4830450 : Nat := 118140960795 + 4830450 * 2 ^ 59
def prefixEnd_4830450 : Nat := 4983230072969 + 3 ^ 40 * 4830450 * 2
def baseEnd_4830450 : Nat := 275593625278970119540019

theorem tailTrace_4830450 : CollatzResearch.WordTrace tailWord_4830450 prefixEnd_4830450 275593625278970119540019 := by
  unfold tailWord_4830450
  simp only [CollatzResearch.WordTrace]
  refine ⟨44045246337528025006370201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117453990233408066683653869 44045246337528025006370201)
  ·
    refine ⟨33033934753146018754777651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44045246337528025006370201 33033934753146018754777651)
    ·
      refine ⟨49550902129719028132166477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33033934753146018754777651 49550902129719028132166477)
      ·
        refine ⟨18581588298644635549562429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49550902129719028132166477 18581588298644635549562429)
        ·
          refine ⟨6968095611991738331085911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18581588298644635549562429 6968095611991738331085911)
          ·
            refine ⟨10452143417987607496628867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6968095611991738331085911 10452143417987607496628867)
            ·
              refine ⟨15678215126981411244943301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10452143417987607496628867 15678215126981411244943301)
              ·
                refine ⟨2939665336309014608426869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15678215126981411244943301 2939665336309014608426869)
                ·
                  refine ⟨275593625278970119540019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2939665336309014608426869 275593625278970119540019)
                  ·
                    rfl

theorem cell23_4830450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_4830450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830450 prefixEnd_4830450 := by exact prefixLift 4830450
  have htrace : WordTrace (prefixWord ++ tailWord_4830450) baseStart_4830450 baseEnd_4830450 := by
    simpa [prefixWord, tailWord_4830450, baseEnd_4830450] using wordTrace_append hprefix tailTrace_4830450
  have hstable : (prefixWord ++ tailWord_4830450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830450).length < 2 ^ (prefixWord ++ tailWord_4830450).sum := by decide
  have hdescent : baseEnd_4830450 < baseStart_4830450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830553 : List Nat := [1, 2, 1, 2, 2, 2, 4, 3, 1, 5]
def baseStart_4830553 : Nat := 118140960795 + 4830553 * 2 ^ 59
def prefixEnd_4830553 : Nat := 4983230072969 + 3 ^ 40 * 4830553 * 2
def baseEnd_4830553 : Nat := 826798505339381390957399

theorem tailTrace_4830553 : CollatzResearch.WordTrace tailWord_4830553 prefixEnd_4830553 826798505339381390957399 := by
  unfold tailWord_4830553
  simp only [CollatzResearch.WordTrace]
  refine ⟨176184742068738948616480313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117456494712492632410986875 176184742068738948616480313)
  ·
    refine ⟨132138556551554211462360235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176184742068738948616480313 132138556551554211462360235)
    ·
      refine ⟨198207834827331317193540353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132138556551554211462360235 198207834827331317193540353)
      ·
        refine ⟨148655876120498487895155265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198207834827331317193540353 148655876120498487895155265)
        ·
          refine ⟨111491907090373865921366449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148655876120498487895155265 111491907090373865921366449)
          ·
            refine ⟨83618930317780399441024837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111491907090373865921366449 83618930317780399441024837)
            ·
              refine ⟨15678549434583824895192157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83618930317780399441024837 15678549434583824895192157)
              ·
                refine ⟨5879456037968934335697059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15678549434583824895192157 5879456037968934335697059)
                ·
                  refine ⟨8819184056953401503545589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5879456037968934335697059 8819184056953401503545589)
                  ·
                    refine ⟨826798505339381390957399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8819184056953401503545589 826798505339381390957399)
                    ·
                      rfl

theorem cell23_4830553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 5].length) (baseStart_4830553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830553 prefixEnd_4830553 := by exact prefixLift 4830553
  have htrace : WordTrace (prefixWord ++ tailWord_4830553) baseStart_4830553 baseEnd_4830553 := by
    simpa [prefixWord, tailWord_4830553, baseEnd_4830553] using wordTrace_append hprefix tailTrace_4830553
  have hstable : (prefixWord ++ tailWord_4830553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830553).length < 2 ^ (prefixWord ++ tailWord_4830553).sum := by decide
  have hdescent : baseEnd_4830553 < baseStart_4830553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830560 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 4, 3, 2]
def baseStart_4830560 : Nat := 118140960795 + 4830560 * 2 ^ 59
def prefixEnd_4830560 : Nat := 4983230072969 + 3 ^ 40 * 4830560 * 2
def baseEnd_4830560 : Nat := 2480399110382725645484665

theorem tailTrace_4830560 : CollatzResearch.WordTrace tailWord_4830560 prefixEnd_4830560 2480399110382725645484665 := by
  unfold tailWord_4830560
  simp only [CollatzResearch.WordTrace]
  refine ⟨88092498689856794405992567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117456664919809059207990089 88092498689856794405992567)
  ·
    refine ⟨132138748034785191608988851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88092498689856794405992567 132138748034785191608988851)
    ·
      refine ⟨198208122052177787413483277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132138748034785191608988851 198208122052177787413483277)
      ·
        refine ⟨74328045769566670280056229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198208122052177787413483277 74328045769566670280056229)
        ·
          refine ⟨13936508581793750677510543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74328045769566670280056229 13936508581793750677510543)
          ·
            refine ⟨20904762872690626016265815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13936508581793750677510543 20904762872690626016265815)
            ·
              refine ⟨31357144309035939024398723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20904762872690626016265815 31357144309035939024398723)
              ·
                refine ⟨47035716463553908536598085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31357144309035939024398723 47035716463553908536598085)
                ·
                  refine ⟨8819196836916357850612141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47035716463553908536598085 8819196836916357850612141)
                  ·
                    refine ⟨3307198813843634193979553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8819196836916357850612141 3307198813843634193979553)
                    ·
                      refine ⟨2480399110382725645484665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3307198813843634193979553 2480399110382725645484665)
                      ·
                        rfl

theorem cell23_4830560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_4830560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830560 prefixEnd_4830560 := by exact prefixLift 4830560
  have htrace : WordTrace (prefixWord ++ tailWord_4830560) baseStart_4830560 baseEnd_4830560 := by
    simpa [prefixWord, tailWord_4830560, baseEnd_4830560] using wordTrace_append hprefix tailTrace_4830560
  have hstable : (prefixWord ++ tailWord_4830560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830560).length < 2 ^ (prefixWord ++ tailWord_4830560).sum := by decide
  have hdescent : baseEnd_4830560 < baseStart_4830560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830574 : List Nat := [4, 1, 2, 4, 1, 2, 2, 1, 6]
def baseStart_4830574 : Nat := 118140960795 + 4830574 * 2 ^ 59
def prefixEnd_4830574 : Nat := 4983230072969 + 3 ^ 40 * 4830574 * 2
def baseEnd_4830574 : Nat := 275600699901320954523289

theorem tailTrace_4830574 : CollatzResearch.WordTrace tailWord_4830574 prefixEnd_4830574 275600699901320954523289 := by
  unfold tailWord_4830574
  simp only [CollatzResearch.WordTrace]
  refine ⟨22023188500207858650374347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117457005334441912801996517 22023188500207858650374347)
  ·
    refine ⟨33034782750311787975561521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22023188500207858650374347 33034782750311787975561521)
    ·
      refine ⟨24776087062733840981671141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33034782750311787975561521 24776087062733840981671141)
      ·
        refine ⟨4645516324262595184063339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24776087062733840981671141 4645516324262595184063339)
        ·
          refine ⟨6968274486393892776095009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4645516324262595184063339 6968274486393892776095009)
          ·
            refine ⟨5226205864795419582071257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6968274486393892776095009 5226205864795419582071257)
            ·
              refine ⟨3919654398596564686553443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5226205864795419582071257 3919654398596564686553443)
              ·
                refine ⟨5879481597894847029830165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3919654398596564686553443 5879481597894847029830165)
                ·
                  refine ⟨275600699901320954523289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5879481597894847029830165 275600699901320954523289)
                  ·
                    rfl

theorem cell23_4830574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_4830574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830574 prefixEnd_4830574 := by exact prefixLift 4830574
  have htrace : WordTrace (prefixWord ++ tailWord_4830574) baseStart_4830574 baseEnd_4830574 := by
    simpa [prefixWord, tailWord_4830574, baseEnd_4830574] using wordTrace_append hprefix tailTrace_4830574
  have hstable : (prefixWord ++ tailWord_4830574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830574).length < 2 ^ (prefixWord ++ tailWord_4830574).sum := by decide
  have hdescent : baseEnd_4830574 < baseStart_4830574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830594 : List Nat := [3, 4, 2, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_4830594 : Nat := 118140960795 + 4830594 * 2 ^ 59
def prefixEnd_4830594 : Nat := 4983230072969 + 3 ^ 40 * 4830594 * 2
def baseEnd_4830594 : Nat := 2480416568724978512459509

theorem tailTrace_4830594 : CollatzResearch.WordTrace tailWord_4830594 prefixEnd_4830594 2480416568724978512459509 := by
  unfold tailWord_4830594
  simp only [CollatzResearch.WordTrace]
  refine ⟨44046559365397603154680709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117457491641060275079148557 44046559365397603154680709)
  ·
    refine ⟨8258729881012050591502633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44046559365397603154680709 8258729881012050591502633)
    ·
      refine ⟨6194047410759037943626975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8258729881012050591502633 6194047410759037943626975)
      ·
        refine ⟨9291071116138556915440463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6194047410759037943626975 9291071116138556915440463)
        ·
          refine ⟨13936606674207835373160695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9291071116138556915440463 13936606674207835373160695)
          ·
            refine ⟨20904910011311753059741043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13936606674207835373160695 20904910011311753059741043)
            ·
              refine ⟨31357365016967629589611565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20904910011311753059741043 31357365016967629589611565)
              ·
                refine ⟨11759011881362861096104337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31357365016967629589611565 11759011881362861096104337)
                ·
                  refine ⟨8819258911022145822078253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11759011881362861096104337 8819258911022145822078253)
                  ·
                    refine ⟨3307222091633304683279345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8819258911022145822078253 3307222091633304683279345)
                    ·
                      refine ⟨2480416568724978512459509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3307222091633304683279345 2480416568724978512459509)
                      ·
                        rfl

theorem cell23_4830594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_4830594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830594 prefixEnd_4830594 := by exact prefixLift 4830594
  have htrace : WordTrace (prefixWord ++ tailWord_4830594) baseStart_4830594 baseEnd_4830594 := by
    simpa [prefixWord, tailWord_4830594, baseEnd_4830594] using wordTrace_append hprefix tailTrace_4830594
  have hstable : (prefixWord ++ tailWord_4830594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830594).length < 2 ^ (prefixWord ++ tailWord_4830594).sum := by decide
  have hdescent : baseEnd_4830594 < baseStart_4830594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830603 : List Nat := [1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 4]
def baseStart_4830603 : Nat := 118140960795 + 4830603 * 2 ^ 59
def prefixEnd_4830603 : Nat := 4983230072969 + 3 ^ 40 * 4830603 * 2
def baseEnd_4830603 : Nat := 2480421190050868977246967

theorem tailTrace_4830603 : CollatzResearch.WordTrace tailWord_4830603 prefixEnd_4830603 2480421190050868977246967 := by
  unfold tailWord_4830603
  simp only [CollatzResearch.WordTrace]
  refine ⟨176186565718557807155800463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117457710479038538103866975 176186565718557807155800463)
  ·
    refine ⟨264279848577836710733700695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176186565718557807155800463 264279848577836710733700695)
    ·
      refine ⟨396419772866755066100551043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264279848577836710733700695 396419772866755066100551043)
      ·
        refine ⟨594629659300132599150826565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396419772866755066100551043 594629659300132599150826565)
        ·
          refine ⟨111493061118774862340779981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 594629659300132599150826565 111493061118774862340779981)
          ·
            refine ⟨41809897919540573377792493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111493061118774862340779981 41809897919540573377792493)
            ·
              refine ⟨15678711719827715016672185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41809897919540573377792493 15678711719827715016672185)
              ·
                refine ⟨11759033789870786262504139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15678711719827715016672185 11759033789870786262504139)
                ·
                  refine ⟨17638550684806179393756209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11759033789870786262504139 17638550684806179393756209)
                  ·
                    refine ⟨13228913013604634545317157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17638550684806179393756209 13228913013604634545317157)
                    ·
                      refine ⟨2480421190050868977246967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13228913013604634545317157 2480421190050868977246967)
                      ·
                        rfl

theorem cell23_4830603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 4].length) (baseStart_4830603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830603 prefixEnd_4830603 := by exact prefixLift 4830603
  have htrace : WordTrace (prefixWord ++ tailWord_4830603) baseStart_4830603 baseEnd_4830603 := by
    simpa [prefixWord, tailWord_4830603, baseEnd_4830603] using wordTrace_append hprefix tailTrace_4830603
  have hstable : (prefixWord ++ tailWord_4830603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830603).length < 2 ^ (prefixWord ++ tailWord_4830603).sum := by decide
  have hdescent : baseEnd_4830603 < baseStart_4830603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830624 : List Nat := [2, 1, 1, 4, 1, 2, 3, 4, 1, 2, 2]
def baseStart_4830624 : Nat := 118140960795 + 4830624 * 2 ^ 59
def prefixEnd_4830624 : Nat := 4983230072969 + 3 ^ 40 * 4830624 * 2
def baseEnd_4830624 : Nat := 2480431973144613395084371

theorem tailTrace_4830624 : CollatzResearch.WordTrace tailWord_4830624 prefixEnd_4830624 2480431973144613395084371 := by
  unfold tailWord_4830624
  simp only [CollatzResearch.WordTrace]
  refine ⟨88093665825740863871157463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117458221100987818494876617 88093665825740863871157463)
  ·
    refine ⟨132140498738611295806736195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88093665825740863871157463 132140498738611295806736195)
    ·
      refine ⟨198210748107916943710104293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132140498738611295806736195 198210748107916943710104293)
      ·
        refine ⟨37164515270234426945644555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198210748107916943710104293 37164515270234426945644555)
        ·
          refine ⟨55746772905351640418466833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37164515270234426945644555 55746772905351640418466833)
          ·
            refine ⟨41810079679013730313850125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55746772905351640418466833 41810079679013730313850125)
            ·
              refine ⟨15678779879630148867693797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41810079679013730313850125 15678779879630148867693797)
              ·
                refine ⟨2939771227430652912692587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15678779879630148867693797 2939771227430652912692587)
                ·
                  refine ⟨4409656841145979369038881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2939771227430652912692587 4409656841145979369038881)
                  ·
                    refine ⟨3307242630859484526779161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4409656841145979369038881 3307242630859484526779161)
                    ·
                      refine ⟨2480431973144613395084371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3307242630859484526779161 2480431973144613395084371)
                      ·
                        rfl

theorem cell23_4830624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_4830624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830624 prefixEnd_4830624 := by exact prefixLift 4830624
  have htrace : WordTrace (prefixWord ++ tailWord_4830624) baseStart_4830624 baseEnd_4830624 := by
    simpa [prefixWord, tailWord_4830624, baseEnd_4830624] using wordTrace_append hprefix tailTrace_4830624
  have hstable : (prefixWord ++ tailWord_4830624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830624).length < 2 ^ (prefixWord ++ tailWord_4830624).sum := by decide
  have hdescent : baseEnd_4830624 < baseStart_4830624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830637 : List Nat := [1, 5, 2, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_4830637 : Nat := 118140960795 + 4830637 * 2 ^ 59
def prefixEnd_4830637 : Nat := 4983230072969 + 3 ^ 40 * 4830637 * 2
def baseEnd_4830637 : Nat := 2480438648393121844221811

theorem tailTrace_4830637 : CollatzResearch.WordTrace tailWord_4830637 prefixEnd_4830637 2480438648393121844221811 := by
  unfold tailWord_4830637
  simp only [CollatzResearch.WordTrace]
  refine ⟨176187805800434630962538165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117458537200289753975025443 176187805800434630962538165)
  ·
    refine ⟨16517606793790746652737953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176187805800434630962538165 16517606793790746652737953)
    ·
      refine ⟨12388205095343059989553465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16517606793790746652737953 12388205095343059989553465)
      ·
        refine ⟨9291153821507294992165099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12388205095343059989553465 9291153821507294992165099)
        ·
          refine ⟨13936730732260942488247649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9291153821507294992165099 13936730732260942488247649)
          ·
            refine ⟨10452548049195706866185737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13936730732260942488247649 10452548049195706866185737)
            ·
              refine ⟨7839411036896780149639303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10452548049195706866185737 7839411036896780149639303)
              ·
                refine ⟨11759116555345170224458955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7839411036896780149639303 11759116555345170224458955)
                ·
                  refine ⟨17638674833017755336688433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11759116555345170224458955 17638674833017755336688433)
                  ·
                    refine ⟨13229006124763316502516325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17638674833017755336688433 13229006124763316502516325)
                    ·
                      refine ⟨2480438648393121844221811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13229006124763316502516325 2480438648393121844221811)
                      ·
                        rfl

theorem cell23_4830637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_4830637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830637 prefixEnd_4830637 := by exact prefixLift 4830637
  have htrace : WordTrace (prefixWord ++ tailWord_4830637) baseStart_4830637 baseEnd_4830637 := by
    simpa [prefixWord, tailWord_4830637, baseEnd_4830637] using wordTrace_append hprefix tailTrace_4830637
  have hstable : (prefixWord ++ tailWord_4830637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830637).length < 2 ^ (prefixWord ++ tailWord_4830637).sum := by decide
  have hdescent : baseEnd_4830637 < baseStart_4830637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830653 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_4830653 : Nat := 118140960795 + 4830653 * 2 ^ 59
def prefixEnd_4830653 : Nat := 4983230072969 + 3 ^ 40 * 4830653 * 2
def baseEnd_4830653 : Nat := 2480446864083593781621737

theorem tailTrace_4830653 : CollatzResearch.WordTrace tailWord_4830653 prefixEnd_4830653 2480446864083593781621737 := by
  unfold tailWord_4830653
  simp only [CollatzResearch.WordTrace]
  refine ⟨176188389368376665695120613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117458926245584443796747075 176188389368376665695120613)
  ·
    refine ⟨33035323006570624817835115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176188389368376665695120613 33035323006570624817835115)
    ·
      refine ⟨49552984509855937226752673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33035323006570624817835115 49552984509855937226752673)
      ·
        refine ⟨37164738382391952920064505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49552984509855937226752673 37164738382391952920064505)
        ·
          refine ⟨27873553786793964690048379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37164738382391952920064505 27873553786793964690048379)
          ·
            refine ⟨41810330680190947035072569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27873553786793964690048379 41810330680190947035072569)
            ·
              refine ⟨31357748010143210276304427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41810330680190947035072569 31357748010143210276304427)
              ·
                refine ⟨47036622015214815414456641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31357748010143210276304427 47036622015214815414456641)
                ·
                  refine ⟨35277466511411111560842481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47036622015214815414456641 35277466511411111560842481)
                  ·
                    refine ⟨26458099883558333670631861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35277466511411111560842481 26458099883558333670631861)
                    ·
                      refine ⟨2480446864083593781621737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26458099883558333670631861 2480446864083593781621737)
                      ·
                        rfl

theorem cell23_4830653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_4830653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830653 prefixEnd_4830653 := by exact prefixLift 4830653
  have htrace : WordTrace (prefixWord ++ tailWord_4830653) baseStart_4830653 baseEnd_4830653 := by
    simpa [prefixWord, tailWord_4830653, baseEnd_4830653] using wordTrace_append hprefix tailTrace_4830653
  have hstable : (prefixWord ++ tailWord_4830653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830653).length < 2 ^ (prefixWord ++ tailWord_4830653).sum := by decide
  have hdescent : baseEnd_4830653 < baseStart_4830653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830658 : List Nat := [3, 5, 2, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_4830658 : Nat := 118140960795 + 4830658 * 2 ^ 59
def prefixEnd_4830658 : Nat := 4983230072969 + 3 ^ 40 * 4830658 * 2
def baseEnd_4830658 : Nat := 2480449431486866262059215

theorem tailTrace_4830658 : CollatzResearch.WordTrace tailWord_4830658 prefixEnd_4830658 2480449431486866262059215 := by
  unfold tailWord_4830658
  simp only [CollatzResearch.WordTrace]
  refine ⟨44047142933339637887263157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117459047822239034366035085 44047142933339637887263157)
  ·
    refine ⟨4129419650000591051930921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44047142933339637887263157 4129419650000591051930921)
    ·
      refine ⟨3097064737500443288948191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4129419650000591051930921 3097064737500443288948191)
      ·
        refine ⟨4645597106250664933422287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3097064737500443288948191 4645597106250664933422287)
        ·
          refine ⟨6968395659375997400133431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4645597106250664933422287 6968395659375997400133431)
          ·
            refine ⟨10452593489063996100200147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6968395659375997400133431 10452593489063996100200147)
            ·
              refine ⟨15678890233595994150300221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10452593489063996100200147 15678890233595994150300221)
              ·
                refine ⟨5879583837598497806362583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15678890233595994150300221 5879583837598497806362583)
                ·
                  refine ⟨8819375756397746709543875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5879583837598497806362583 8819375756397746709543875)
                  ·
                    refine ⟨13229063634596620064315813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8819375756397746709543875 13229063634596620064315813)
                    ·
                      refine ⟨2480449431486866262059215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13229063634596620064315813 2480449431486866262059215)
                      ·
                        rfl

theorem cell23_4830658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_4830658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830658 prefixEnd_4830658 := by exact prefixLift 4830658
  have htrace : WordTrace (prefixWord ++ tailWord_4830658) baseStart_4830658 baseEnd_4830658 := by
    simpa [prefixWord, tailWord_4830658, baseEnd_4830658] using wordTrace_append hprefix tailTrace_4830658
  have hstable : (prefixWord ++ tailWord_4830658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830658).length < 2 ^ (prefixWord ++ tailWord_4830658).sum := by decide
  have hdescent : baseEnd_4830658 < baseStart_4830658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830680 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 3, 4, 2]
def baseStart_4830680 : Nat := 118140960795 + 4830680 * 2 ^ 59
def prefixEnd_4830680 : Nat := 4983230072969 + 3 ^ 40 * 4830680 * 2
def baseEnd_4830680 : Nat := 2480460728061265175984113

theorem tailTrace_4830680 : CollatzResearch.WordTrace tailWord_4830680 prefixEnd_4830680 2480460728061265175984113 := by
  unfold tailWord_4830680
  simp only [CollatzResearch.WordTrace]
  refine ⟨88094687069639424653176747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117459582759519232870902329 88094687069639424653176747)
  ·
    refine ⟨132142030604459136979765121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88094687069639424653176747 132142030604459136979765121)
    ·
      refine ⟨99106522953344352734823841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132142030604459136979765121 99106522953344352734823841)
      ·
        refine ⟨74329892215008264551117881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99106522953344352734823841 74329892215008264551117881)
        ·
          refine ⟨55747419161256198413338411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74329892215008264551117881 55747419161256198413338411)
          ·
            refine ⟨83621128741884297620007617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55747419161256198413338411 83621128741884297620007617)
            ·
              refine ⟨62715846556413223215005713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83621128741884297620007617 62715846556413223215005713)
              ·
                refine ⟨47036884917309917411254285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62715846556413223215005713 47036884917309917411254285)
                ·
                  refine ⟨17638831843991219029220357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47036884917309917411254285 17638831843991219029220357)
                  ·
                    refine ⟨3307280970748353567978817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17638831843991219029220357 3307280970748353567978817)
                    ·
                      refine ⟨2480460728061265175984113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3307280970748353567978817 2480460728061265175984113)
                      ·
                        rfl

theorem cell23_4830680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_4830680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830680 prefixEnd_4830680 := by exact prefixLift 4830680
  have htrace : WordTrace (prefixWord ++ tailWord_4830680) baseStart_4830680 baseEnd_4830680 := by
    simpa [prefixWord, tailWord_4830680, baseEnd_4830680] using wordTrace_append hprefix tailTrace_4830680
  have hstable : (prefixWord ++ tailWord_4830680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830680).length < 2 ^ (prefixWord ++ tailWord_4830680).sum := by decide
  have hdescent : baseEnd_4830680 < baseStart_4830680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830701 : List Nat := [1, 5, 1, 3, 2, 1, 2, 2, 1, 3, 2]
def baseStart_4830701 : Nat := 118140960795 + 4830701 * 2 ^ 59
def prefixEnd_4830701 : Nat := 4983230072969 + 3 ^ 40 * 4830701 * 2
def baseEnd_4830701 : Nat := 2480471511155009593821517

theorem tailTrace_4830701 : CollatzResearch.WordTrace tailWord_4830701 prefixEnd_4830701 2480471511155009593821517 := by
  unfold tailWord_4830701
  simp only [CollatzResearch.WordTrace]
  refine ⟨176190140072202769892867957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117460093381468513261911971 176190140072202769892867957)
  ·
    refine ⟨16517825631769009677456371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176190140072202769892867957 16517825631769009677456371)
    ·
      refine ⟨24776738447653514516184557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16517825631769009677456371 24776738447653514516184557)
      ·
        refine ⟨9291276917870067943569209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24776738447653514516184557 9291276917870067943569209)
        ·
          refine ⟨6968457688402550957676907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9291276917870067943569209 6968457688402550957676907)
          ·
            refine ⟨10452686532603826436515361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6968457688402550957676907 10452686532603826436515361)
            ·
              refine ⟨7839514899452869827386521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10452686532603826436515361 7839514899452869827386521)
              ·
                refine ⟨5879636174589652370539891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7839514899452869827386521 5879636174589652370539891)
                ·
                  refine ⟨8819454261884478555809837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5879636174589652370539891 8819454261884478555809837)
                  ·
                    refine ⟨3307295348206679458428689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8819454261884478555809837 3307295348206679458428689)
                    ·
                      refine ⟨2480471511155009593821517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3307295348206679458428689 2480471511155009593821517)
                      ·
                        rfl

theorem cell23_4830701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_4830701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830701 prefixEnd_4830701 := by exact prefixLift 4830701
  have htrace : WordTrace (prefixWord ++ tailWord_4830701) baseStart_4830701 baseEnd_4830701 := by
    simpa [prefixWord, tailWord_4830701, baseEnd_4830701] using wordTrace_append hprefix tailTrace_4830701
  have hstable : (prefixWord ++ tailWord_4830701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830701).length < 2 ^ (prefixWord ++ tailWord_4830701).sum := by decide
  have hdescent : baseEnd_4830701 < baseStart_4830701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830703 : List Nat := [1, 1, 2, 1, 4, 1, 4, 2, 7]
def baseStart_4830703 : Nat := 118140960795 + 4830703 * 2 ^ 59
def prefixEnd_4830703 : Nat := 4983230072969 + 3 ^ 40 * 4830703 * 2
def baseEnd_4830703 : Nat := 275608059790702065110723

theorem tailTrace_4830703 : CollatzResearch.WordTrace tailWord_4830703 prefixEnd_4830703 275608059790702065110723 := by
  unfold tailWord_4830703
  simp only [CollatzResearch.WordTrace]
  refine ⟨176190213018195524234440763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117460142012130349489627175 176190213018195524234440763)
  ·
    refine ⟨264285319527293286351661145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176190213018195524234440763 264285319527293286351661145)
    ·
      refine ⟨198213989645469964763745859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264285319527293286351661145 198213989645469964763745859)
      ·
        refine ⟨297320984468204947145618789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198213989645469964763745859 297320984468204947145618789)
        ·
          refine ⟨55747684587788427589803523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 297320984468204947145618789 55747684587788427589803523)
          ·
            refine ⟨83621526881682641384705285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55747684587788427589803523 83621526881682641384705285)
            ·
              refine ⟨15679036290315495259632241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83621526881682641384705285 15679036290315495259632241)
              ·
                refine ⟨11759277217736621444724181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15679036290315495259632241 11759277217736621444724181)
                ·
                  refine ⟨275608059790702065110723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11759277217736621444724181 275608059790702065110723)
                  ·
                    rfl

theorem cell23_4830703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 7].length) (baseStart_4830703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830703 prefixEnd_4830703 := by exact prefixLift 4830703
  have htrace : WordTrace (prefixWord ++ tailWord_4830703) baseStart_4830703 baseEnd_4830703 := by
    simpa [prefixWord, tailWord_4830703, baseEnd_4830703] using wordTrace_append hprefix tailTrace_4830703
  have hstable : (prefixWord ++ tailWord_4830703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830703).length < 2 ^ (prefixWord ++ tailWord_4830703).sum := by decide
  have hdescent : baseEnd_4830703 < baseStart_4830703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830737 : List Nat := [1, 2, 2, 1, 1, 2, 7, 2, 5]
def baseStart_4830737 : Nat := 118140960795 + 4830737 * 2 ^ 59
def prefixEnd_4830737 : Nat := 4983230072969 + 3 ^ 40 * 4830737 * 2
def baseEnd_4830737 : Nat := 275609999606507939219039

theorem tailTrace_4830737 : CollatzResearch.WordTrace tailWord_4830737 prefixEnd_4830737 275609999606507939219039 := by
  unfold tailWord_4830737
  simp only [CollatzResearch.WordTrace]
  refine ⟨176191453100072348041178465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117460968733381565360785643 176191453100072348041178465)
  ·
    refine ⟨132143589825054261030883849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176191453100072348041178465 132143589825054261030883849)
    ·
      refine ⟨99107692368790695773162887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132143589825054261030883849 99107692368790695773162887)
      ·
        refine ⟨148661538553186043659744331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99107692368790695773162887 148661538553186043659744331)
        ·
          refine ⟨222992307829779065489616497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148661538553186043659744331 222992307829779065489616497)
          ·
            refine ⟨167244230872334299117212373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222992307829779065489616497 167244230872334299117212373)
            ·
              refine ⟨3919786661070335135559665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 167244230872334299117212373 3919786661070335135559665)
              ·
                refine ⟨2939839995802751351669749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3919786661070335135559665 2939839995802751351669749)
                ·
                  refine ⟨275609999606507939219039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2939839995802751351669749 275609999606507939219039)
                  ·
                    rfl

theorem cell23_4830737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 5].length) (baseStart_4830737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830737 prefixEnd_4830737 := by exact prefixLift 4830737
  have htrace : WordTrace (prefixWord ++ tailWord_4830737) baseStart_4830737 baseEnd_4830737 := by
    simpa [prefixWord, tailWord_4830737, baseEnd_4830737] using wordTrace_append hprefix tailTrace_4830737
  have hstable : (prefixWord ++ tailWord_4830737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830737).length < 2 ^ (prefixWord ++ tailWord_4830737).sum := by decide
  have hdescent : baseEnd_4830737 < baseStart_4830737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830793 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 8]
def baseStart_4830793 : Nat := 118140960795 + 4830793 * 2 ^ 59
def prefixEnd_4830793 : Nat := 4983230072969 + 3 ^ 40 * 4830793 * 2
def baseEnd_4830793 : Nat := 275613194597247025985677

theorem tailTrace_4830793 : CollatzResearch.WordTrace tailWord_4830793 prefixEnd_4830793 275613194597247025985677 := by
  unfold tailWord_4830793
  simp only [CollatzResearch.WordTrace]
  refine ⟨176193495587869469605217033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117462330391912979736811355 176193495587869469605217033)
  ·
    refine ⟨132145121690902102203912775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176193495587869469605217033 132145121690902102203912775)
    ·
      refine ⟨198217682536353153305869163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132145121690902102203912775 198217682536353153305869163)
      ·
        refine ⟨297326523804529729958803745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198217682536353153305869163 297326523804529729958803745)
        ·
          refine ⟨222994892853397297469102809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297326523804529729958803745 222994892853397297469102809)
          ·
            refine ⟨167246169640047973101827107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222994892853397297469102809 167246169640047973101827107)
            ·
              refine ⟨250869254460071959652740661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167246169640047973101827107 250869254460071959652740661)
              ·
                refine ⟨23518992605631746217444437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 250869254460071959652740661 23518992605631746217444437)
                ·
                  refine ⟨275613194597247025985677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23518992605631746217444437 275613194597247025985677)
                  ·
                    rfl

theorem cell23_4830793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 8].length) (baseStart_4830793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830793 prefixEnd_4830793 := by exact prefixLift 4830793
  have htrace : WordTrace (prefixWord ++ tailWord_4830793) baseStart_4830793 baseEnd_4830793 := by
    simpa [prefixWord, tailWord_4830793, baseEnd_4830793] using wordTrace_append hprefix tailTrace_4830793
  have hstable : (prefixWord ++ tailWord_4830793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830793).length < 2 ^ (prefixWord ++ tailWord_4830793).sum := by decide
  have hdescent : baseEnd_4830793 < baseStart_4830793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830824 : List Nat := [2, 1, 4, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_4830824 : Nat := 118140960795 + 4830824 * 2 ^ 59
def prefixEnd_4830824 : Nat := 4983230072969 + 3 ^ 40 * 4830824 * 2
def baseEnd_4830824 : Nat := 2480534669275512612583451

theorem tailTrace_4830824 : CollatzResearch.WordTrace tailWord_4830824 prefixEnd_4830824 2480534669275512612583451 := by
  unfold tailWord_4830824
  simp only [CollatzResearch.WordTrace]
  refine ⟨88097313125378580949797763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117463084167171441266397017 88097313125378580949797763)
  ·
    refine ⟨132145969688067871424696645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88097313125378580949797763 132145969688067871424696645)
    ·
      refine ⟨24777369316512725892130621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132145969688067871424696645 24777369316512725892130621)
      ·
        refine ⟨9291513493692272209548983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24777369316512725892130621 9291513493692272209548983)
        ·
          refine ⟨13937270240538408314323475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9291513493692272209548983 13937270240538408314323475)
          ·
            refine ⟨20905905360807612471485213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13937270240538408314323475 20905905360807612471485213)
            ·
              refine ⟨7839714510302854676806955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20905905360807612471485213 7839714510302854676806955)
              ·
                refine ⟨11759571765454282015210433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7839714510302854676806955 11759571765454282015210433)
                ·
                  refine ⟨8819678824090711511407825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11759571765454282015210433 8819678824090711511407825)
                  ·
                    refine ⟨6614759118068033633555869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8819678824090711511407825 6614759118068033633555869)
                    ·
                      refine ⟨2480534669275512612583451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6614759118068033633555869 2480534669275512612583451)
                      ·
                        rfl

theorem cell23_4830824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_4830824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830824 prefixEnd_4830824 := by exact prefixLift 4830824
  have htrace : WordTrace (prefixWord ++ tailWord_4830824) baseStart_4830824 baseEnd_4830824 := by
    simpa [prefixWord, tailWord_4830824, baseEnd_4830824] using wordTrace_append hprefix tailTrace_4830824
  have hstable : (prefixWord ++ tailWord_4830824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830824).length < 2 ^ (prefixWord ++ tailWord_4830824).sum := by decide
  have hdescent : baseEnd_4830824 < baseStart_4830824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830877 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 1, 8, 2]
def baseStart_4830877 : Nat := 118140960795 + 4830877 * 2 ^ 59
def prefixEnd_4830877 : Nat := 4983230072969 + 3 ^ 40 * 4830877 * 2
def baseEnd_4830877 : Nat := 2480561883750200905220707

theorem tailTrace_4830877 : CollatzResearch.WordTrace tailWord_4830877 prefixEnd_4830877 2480561883750200905220707 := by
  unfold tailWord_4830877
  simp only [CollatzResearch.WordTrace]
  refine ⟨176196559319565151951274885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117464372879710101300849923 176196559319565151951274885)
  ·
    refine ⟨33036854872418465990864041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176196559319565151951274885 33036854872418465990864041)
    ·
      refine ⟨24777641154313849493148031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33036854872418465990864041 24777641154313849493148031)
      ·
        refine ⟨37166461731470774239722047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24777641154313849493148031 37166461731470774239722047)
        ·
          refine ⟨55749692597206161359583071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37166461731470774239722047 55749692597206161359583071)
          ·
            refine ⟨83624538895809242039374607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55749692597206161359583071 83624538895809242039374607)
            ·
              refine ⟨125436808343713863059061911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83624538895809242039374607 125436808343713863059061911)
              ·
                refine ⟨188155212515570794588592867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125436808343713863059061911 188155212515570794588592867)
                ·
                  refine ⟨282232818773356191882889301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188155212515570794588592867 282232818773356191882889301)
                  ·
                    refine ⟨3307415845000267873627609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 282232818773356191882889301 3307415845000267873627609)
                    ·
                      refine ⟨2480561883750200905220707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3307415845000267873627609 2480561883750200905220707)
                      ·
                        rfl

theorem cell23_4830877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_4830877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830877 prefixEnd_4830877 := by exact prefixLift 4830877
  have htrace : WordTrace (prefixWord ++ tailWord_4830877) baseStart_4830877 baseEnd_4830877 := by
    simpa [prefixWord, tailWord_4830877, baseEnd_4830877] using wordTrace_append hprefix tailTrace_4830877
  have hstable : (prefixWord ++ tailWord_4830877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830877).length < 2 ^ (prefixWord ++ tailWord_4830877).sum := by decide
  have hdescent : baseEnd_4830877 < baseStart_4830877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830920 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_4830920 : Nat := 118140960795 + 4830920 * 2 ^ 59
def prefixEnd_4830920 : Nat := 4983230072969 + 3 ^ 40 * 4830920 * 2
def baseEnd_4830920 : Nat := 2480583963418344236983009

theorem tailTrace_4830920 : CollatzResearch.WordTrace tailWord_4830920 prefixEnd_4830920 2480583963418344236983009 := by
  unfold tailWord_4830920
  simp only [CollatzResearch.WordTrace]
  refine ⟨88099063829204685147545107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117465418438939580196726809 88099063829204685147545107)
  ·
    refine ⟨132148595743807027721317661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88099063829204685147545107 132148595743807027721317661)
    ·
      refine ⟨49555723403927635395494123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132148595743807027721317661 49555723403927635395494123)
      ·
        refine ⟨74333585105891453093241185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49555723403927635395494123 74333585105891453093241185)
        ·
          refine ⟨55750188829418589819930889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74333585105891453093241185 55750188829418589819930889)
          ·
            refine ⟨41812641622063942364948167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55750188829418589819930889 41812641622063942364948167)
            ·
              refine ⟨62718962433095913547422251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41812641622063942364948167 62718962433095913547422251)
              ·
                refine ⟨94078443649643870321133377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62718962433095913547422251 94078443649643870321133377)
                ·
                  refine ⟨70558832737232902740850033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94078443649643870321133377 70558832737232902740850033)
                  ·
                    refine ⟨52919124552924677055637525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70558832737232902740850033 52919124552924677055637525)
                    ·
                      refine ⟨2480583963418344236983009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52919124552924677055637525 2480583963418344236983009)
                      ·
                        rfl

theorem cell23_4830920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_4830920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830920 prefixEnd_4830920 := by exact prefixLift 4830920
  have htrace : WordTrace (prefixWord ++ tailWord_4830920) baseStart_4830920 baseEnd_4830920 := by
    simpa [prefixWord, tailWord_4830920, baseEnd_4830920] using wordTrace_append hprefix tailTrace_4830920
  have hstable : (prefixWord ++ tailWord_4830920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830920).length < 2 ^ (prefixWord ++ tailWord_4830920).sum := by decide
  have hdescent : baseEnd_4830920 < baseStart_4830920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830941 : List Nat := [1, 4, 3, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_4830941 : Nat := 118140960795 + 4830941 * 2 ^ 59
def prefixEnd_4830941 : Nat := 4983230072969 + 3 ^ 40 * 4830941 * 2
def baseEnd_4830941 : Nat := 2480594746512088654820413

theorem tailTrace_4830941 : CollatzResearch.WordTrace tailWord_4830941 prefixEnd_4830941 2480594746512088654820413 := by
  unfold tailWord_4830941
  simp only [CollatzResearch.WordTrace]
  refine ⟨176198893591333290881604677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117465929060888860587736451 176198893591333290881604677)
  ·
    refine ⟨33037292548374992040300877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176198893591333290881604677 33037292548374992040300877)
    ·
      refine ⟨12388984705640622015112829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33037292548374992040300877 12388984705640622015112829)
      ·
        refine ⟨4645869264615233255667311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12388984705640622015112829 4645869264615233255667311)
        ·
          refine ⟨6968803896922849883500967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4645869264615233255667311 6968803896922849883500967)
          ·
            refine ⟨10453205845384274825251451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6968803896922849883500967 10453205845384274825251451)
            ·
              refine ⟨15679808768076412237877177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10453205845384274825251451 15679808768076412237877177)
              ·
                refine ⟨11759856576057309178407883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15679808768076412237877177 11759856576057309178407883)
                ·
                  refine ⟨17639784864085963767611825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11759856576057309178407883 17639784864085963767611825)
                  ·
                    refine ⟨13229838648064472825708869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17639784864085963767611825 13229838648064472825708869)
                    ·
                      refine ⟨2480594746512088654820413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13229838648064472825708869 2480594746512088654820413)
                      ·
                        rfl

theorem cell23_4830941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_4830941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830941 prefixEnd_4830941 := by exact prefixLift 4830941
  have htrace : WordTrace (prefixWord ++ tailWord_4830941) baseStart_4830941 baseEnd_4830941 := by
    simpa [prefixWord, tailWord_4830941, baseEnd_4830941] using wordTrace_append hprefix tailTrace_4830941
  have hstable : (prefixWord ++ tailWord_4830941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830941).length < 2 ^ (prefixWord ++ tailWord_4830941).sum := by decide
  have hdescent : baseEnd_4830941 < baseStart_4830941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4830961 : List Nat := [1, 2, 2, 2, 2, 4, 2, 2, 2, 1, 3]
def baseStart_4830961 : Nat := 118140960795 + 4830961 * 2 ^ 59
def prefixEnd_4830961 : Nat := 4983230072969 + 3 ^ 40 * 4830961 * 2
def baseEnd_4830961 : Nat := 2480605016125178576570321

theorem tailTrace_4830961 : CollatzResearch.WordTrace tailWord_4830961 prefixEnd_4830961 2480605016125178576570321 := by
  unfold tailWord_4830961
  simp only [CollatzResearch.WordTrace]
  refine ⟨176199623051260834297332737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117466415367507222864888491 176199623051260834297332737)
  ·
    refine ⟨132149717288445625722999553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176199623051260834297332737 132149717288445625722999553)
    ·
      refine ⟨99112287966334219292249665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132149717288445625722999553 99112287966334219292249665)
      ·
        refine ⟨74334215974750664469187249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99112287966334219292249665 74334215974750664469187249)
        ·
          refine ⟨55750661981062998351890437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74334215974750664469187249 55750661981062998351890437)
          ·
            refine ⟨10453249121449312190979457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55750661981062998351890437 10453249121449312190979457)
            ·
              refine ⟨7839936841086984143234593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10453249121449312190979457 7839936841086984143234593)
              ·
                refine ⟨5879952630815238107425945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7839936841086984143234593 5879952630815238107425945)
                ·
                  refine ⟨4409964473111428580569459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5879952630815238107425945 4409964473111428580569459)
                  ·
                    refine ⟨6614946709667142870854189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4409964473111428580569459 6614946709667142870854189)
                    ·
                      refine ⟨2480605016125178576570321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6614946709667142870854189 2480605016125178576570321)
                      ·
                        rfl

theorem cell23_4830961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_4830961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4830961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4830961 prefixEnd_4830961 := by exact prefixLift 4830961
  have htrace : WordTrace (prefixWord ++ tailWord_4830961) baseStart_4830961 baseEnd_4830961 := by
    simpa [prefixWord, tailWord_4830961, baseEnd_4830961] using wordTrace_append hprefix tailTrace_4830961
  have hstable : (prefixWord ++ tailWord_4830961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4830961).length < 2 ^ (prefixWord ++ tailWord_4830961).sum := by decide
  have hdescent : baseEnd_4830961 < baseStart_4830961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4830961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831034 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3]
def baseStart_4831034 : Nat := 118140960795 + 4831034 * 2 ^ 59
def prefixEnd_4831034 : Nat := 4983230072969 + 3 ^ 40 * 4831034 * 2
def baseEnd_4831034 : Nat := 2480642500212956790957485

theorem tailTrace_4831034 : CollatzResearch.WordTrace tailWord_4831034 prefixEnd_4831034 2480642500212956790957485 := by
  unfold tailWord_4831034
  simp only [CollatzResearch.WordTrace]
  refine ⟨44050571394999091941185039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117468190386664245176493437 44050571394999091941185039)
  ·
    refine ⟨66075857092498637911777559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44050571394999091941185039 66075857092498637911777559)
    ·
      refine ⟨99113785638747956867666339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66075857092498637911777559 99113785638747956867666339)
      ·
        refine ⟨148670678458121935301499509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99113785638747956867666339 148670678458121935301499509)
        ·
          refine ⟨13937876105448931434515579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148670678458121935301499509 13937876105448931434515579)
          ·
            refine ⟨20906814158173397151773369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13937876105448931434515579 20906814158173397151773369)
            ·
              refine ⟨15680110618630047863830027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20906814158173397151773369 15680110618630047863830027)
              ·
                refine ⟨23520165927945071795745041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15680110618630047863830027 23520165927945071795745041)
                ·
                  refine ⟨17640124445958803846808781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23520165927945071795745041 17640124445958803846808781)
                  ·
                    refine ⟨6615046667234551442553293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17640124445958803846808781 6615046667234551442553293)
                    ·
                      refine ⟨2480642500212956790957485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6615046667234551442553293 2480642500212956790957485)
                      ·
                        rfl

theorem cell23_4831034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_4831034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831034 prefixEnd_4831034 := by exact prefixLift 4831034
  have htrace : WordTrace (prefixWord ++ tailWord_4831034) baseStart_4831034 baseEnd_4831034 := by
    simpa [prefixWord, tailWord_4831034, baseEnd_4831034] using wordTrace_append hprefix tailTrace_4831034
  have hstable : (prefixWord ++ tailWord_4831034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831034).length < 2 ^ (prefixWord ++ tailWord_4831034).sum := by decide
  have hdescent : baseEnd_4831034 < baseStart_4831034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831147 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 4]
def baseStart_4831147 : Nat := 118140960795 + 4831147 * 2 ^ 59
def prefixEnd_4831147 : Nat := 4983230072969 + 3 ^ 40 * 4831147 * 2
def baseEnd_4831147 : Nat := 2480700523526914848844465

theorem tailTrace_4831147 : CollatzResearch.WordTrace tailWord_4831147 prefixEnd_4831147 2480700523526914848844465 := by
  unfold tailWord_4831147
  simp only [CollatzResearch.WordTrace]
  refine ⟨176206407028586988063603695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117470938019057992042402463 176206407028586988063603695)
  ·
    refine ⟨264309610542880482095405543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176206407028586988063603695 264309610542880482095405543)
    ·
      refine ⟨396464415814320723143108315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264309610542880482095405543 396464415814320723143108315)
      ·
        refine ⟨594696623721481084714662473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396464415814320723143108315 594696623721481084714662473)
        ·
          refine ⟨446022467791110813535996855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 594696623721481084714662473 446022467791110813535996855)
          ·
            refine ⟨669033701686666220303995283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446022467791110813535996855 669033701686666220303995283)
            ·
              refine ⟨1003550552529999330455992925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 669033701686666220303995283 1003550552529999330455992925)
              ·
                refine ⟨376331457198749748920997347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1003550552529999330455992925 376331457198749748920997347)
                ·
                  refine ⟨564497185798124623381496021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 376331457198749748920997347 564497185798124623381496021)
                  ·
                    refine ⟨13230402792143545860503813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 564497185798124623381496021 13230402792143545860503813)
                    ·
                      refine ⟨2480700523526914848844465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13230402792143545860503813 2480700523526914848844465)
                      ·
                        rfl

theorem cell23_4831147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 4].length) (baseStart_4831147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831147 prefixEnd_4831147 := by exact prefixLift 4831147
  have htrace : WordTrace (prefixWord ++ tailWord_4831147) baseStart_4831147 baseEnd_4831147 := by
    simpa [prefixWord, tailWord_4831147, baseEnd_4831147] using wordTrace_append hprefix tailTrace_4831147
  have hstable : (prefixWord ++ tailWord_4831147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831147).length < 2 ^ (prefixWord ++ tailWord_4831147).sum := by decide
  have hdescent : baseEnd_4831147 < baseStart_4831147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831241 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 7, 3, 2]
def baseStart_4831241 : Nat := 118140960795 + 4831241 * 2 ^ 59
def prefixEnd_4831241 : Nat := 4983230072969 + 3 ^ 40 * 4831241 * 2
def baseEnd_4831241 : Nat := 2480748790708437481069033

theorem tailTrace_4831241 : CollatzResearch.WordTrace tailWord_4831241 prefixEnd_4831241 2480748790708437481069033 := by
  unfold tailWord_4831241
  simp only [CollatzResearch.WordTrace]
  refine ⟨176209835490246442117525577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117473223660164294745017051 176209835490246442117525577)
  ·
    refine ⟨132157376617684831588144183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176209835490246442117525577 132157376617684831588144183)
    ·
      refine ⟨198236064926527247382216275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132157376617684831588144183 198236064926527247382216275)
      ·
        refine ⟨297354097389790871073324413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198236064926527247382216275 297354097389790871073324413)
        ·
          refine ⟨111507786521171576652496655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297354097389790871073324413 111507786521171576652496655)
          ·
            refine ⟨167261679781757364978744983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111507786521171576652496655 167261679781757364978744983)
            ·
              refine ⟨250892519672636047468117475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167261679781757364978744983 250892519672636047468117475)
              ·
                refine ⟨376338779508954071202176213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250892519672636047468117475 376338779508954071202176213)
                ·
                  refine ⟨8820440144741111043801005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 376338779508954071202176213 8820440144741111043801005)
                  ·
                    refine ⟨3307665054277916641425377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8820440144741111043801005 3307665054277916641425377)
                    ·
                      refine ⟨2480748790708437481069033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3307665054277916641425377 2480748790708437481069033)
                      ·
                        rfl

theorem cell23_4831241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 3, 2].length) (baseStart_4831241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831241 prefixEnd_4831241 := by exact prefixLift 4831241
  have htrace : WordTrace (prefixWord ++ tailWord_4831241) baseStart_4831241 baseEnd_4831241 := by
    simpa [prefixWord, tailWord_4831241, baseEnd_4831241] using wordTrace_append hprefix tailTrace_4831241
  have hstable : (prefixWord ++ tailWord_4831241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831241).length < 2 ^ (prefixWord ++ tailWord_4831241).sum := by decide
  have hdescent : baseEnd_4831241 < baseStart_4831241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831244 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 2, 2, 5]
def baseStart_4831244 : Nat := 118140960795 + 4831244 * 2 ^ 59
def prefixEnd_4831244 : Nat := 4983230072969 + 3 ^ 40 * 4831244 * 2
def baseEnd_4831244 : Nat := 2480750331150400969331519

theorem tailTrace_4831244 : CollatzResearch.WordTrace tailWord_4831244 prefixEnd_4831244 2480750331150400969331519 := by
  unfold tailWord_4831244
  simp only [CollatzResearch.WordTrace]
  refine ⟨88104972454617786814942393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117473296606157049086589857 88104972454617786814942393)
  ·
    refine ⟨66078729340963340111206795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88104972454617786814942393 66078729340963340111206795)
    ·
      refine ⟨99118094011445010166810193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66078729340963340111206795 99118094011445010166810193)
      ·
        refine ⟨74338570508583757625107645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99118094011445010166810193 74338570508583757625107645)
        ·
          refine ⟨27876963940718909109415367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74338570508583757625107645 27876963940718909109415367)
          ·
            refine ⟨41815445911078363664123051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27876963940718909109415367 41815445911078363664123051)
            ·
              refine ⟨62723168866617545496184577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41815445911078363664123051 62723168866617545496184577)
              ·
                refine ⟨47042376649963159122138433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62723168866617545496184577 47042376649963159122138433)
                ·
                  refine ⟨35281782487472369341603825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47042376649963159122138433 35281782487472369341603825)
                  ·
                    refine ⟨26461336865604277006202869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35281782487472369341603825 26461336865604277006202869)
                    ·
                      refine ⟨2480750331150400969331519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26461336865604277006202869 2480750331150400969331519)
                      ·
                        rfl

theorem cell23_4831244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_4831244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831244 prefixEnd_4831244 := by exact prefixLift 4831244
  have htrace : WordTrace (prefixWord ++ tailWord_4831244) baseStart_4831244 baseEnd_4831244 := by
    simpa [prefixWord, tailWord_4831244, baseEnd_4831244] using wordTrace_append hprefix tailTrace_4831244
  have hstable : (prefixWord ++ tailWord_4831244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831244).length < 2 ^ (prefixWord ++ tailWord_4831244).sum := by decide
  have hdescent : baseEnd_4831244 < baseStart_4831244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831265 : List Nat := [1, 2, 3, 2, 4, 1, 1, 3, 2, 1, 3]
def baseStart_4831265 : Nat := 118140960795 + 4831265 * 2 ^ 59
def prefixEnd_4831265 : Nat := 4983230072969 + 3 ^ 40 * 4831265 * 2
def baseEnd_4831265 : Nat := 2480761114244145387168923

theorem tailTrace_4831265 : CollatzResearch.WordTrace tailWord_4831265 prefixEnd_4831265 2480761114244145387168923 := by
  unfold tailWord_4831265
  simp only [CollatzResearch.WordTrace]
  refine ⟨176210710842159494216399249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117473807228106329477599499 176210710842159494216399249)
  ·
    refine ⟨132158033131619620662299437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176210710842159494216399249 132158033131619620662299437)
    ·
      refine ⟨49559262424357357748362289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132158033131619620662299437 49559262424357357748362289)
      ·
        refine ⟨37169446818268018311271717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49559262424357357748362289 37169446818268018311271717)
        ·
          refine ⟨6969271278425253433363447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37169446818268018311271717 6969271278425253433363447)
          ·
            refine ⟨10453906917637880150045171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6969271278425253433363447 10453906917637880150045171)
            ·
              refine ⟨15680860376456820225067757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10453906917637880150045171 15680860376456820225067757)
              ·
                refine ⟨5880322641171307584400409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15680860376456820225067757 5880322641171307584400409)
                ·
                  refine ⟨4410241980878480688300307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5880322641171307584400409 4410241980878480688300307)
                  ·
                    refine ⟨6615362971317721032450461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4410241980878480688300307 6615362971317721032450461)
                    ·
                      refine ⟨2480761114244145387168923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6615362971317721032450461 2480761114244145387168923)
                      ·
                        rfl

theorem cell23_4831265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_4831265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831265 prefixEnd_4831265 := by exact prefixLift 4831265
  have htrace : WordTrace (prefixWord ++ tailWord_4831265) baseStart_4831265 baseEnd_4831265 := by
    simpa [prefixWord, tailWord_4831265, baseEnd_4831265] using wordTrace_append hprefix tailTrace_4831265
  have hstable : (prefixWord ++ tailWord_4831265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831265).length < 2 ^ (prefixWord ++ tailWord_4831265).sum := by decide
  have hdescent : baseEnd_4831265 < baseStart_4831265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831305 : List Nat := [1, 2, 1, 1, 2, 2, 6, 2, 2, 2, 2]
def baseStart_4831305 : Nat := 118140960795 + 4831305 * 2 ^ 59
def prefixEnd_4831305 : Nat := 4983230072969 + 3 ^ 40 * 4831305 * 2
def baseEnd_4831305 : Nat := 2480781653470325230668739

theorem tailTrace_4831305 : CollatzResearch.WordTrace tailWord_4831305 prefixEnd_4831305 2480781653470325230668739 := by
  unfold tailWord_4831305
  simp only [CollatzResearch.WordTrace]
  refine ⟨176212169762014581047855369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117474779841343054031903579 176212169762014581047855369)
  ·
    refine ⟨132159127321510935785891527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176212169762014581047855369 132159127321510935785891527)
    ·
      refine ⟨198238690982266403678837291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132159127321510935785891527 198238690982266403678837291)
      ·
        refine ⟨297358036473399605518255937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198238690982266403678837291 297358036473399605518255937)
        ·
          refine ⟨223018527355049704138691953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297358036473399605518255937 223018527355049704138691953)
          ·
            refine ⟨167263895516287278104018965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223018527355049704138691953 167263895516287278104018965)
            ·
              refine ⟨7840495102325966161125889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 167263895516287278104018965 7840495102325966161125889)
              ·
                refine ⟨5880371326744474620844417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7840495102325966161125889 5880371326744474620844417)
                ·
                  refine ⟨4410278495058355965633313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5880371326744474620844417 4410278495058355965633313)
                  ·
                    refine ⟨3307708871293766974224985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4410278495058355965633313 3307708871293766974224985)
                    ·
                      refine ⟨2480781653470325230668739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3307708871293766974224985 2480781653470325230668739)
                      ·
                        rfl

theorem cell23_4831305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 2, 2].length) (baseStart_4831305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831305 prefixEnd_4831305 := by exact prefixLift 4831305
  have htrace : WordTrace (prefixWord ++ tailWord_4831305) baseStart_4831305 baseEnd_4831305 := by
    simpa [prefixWord, tailWord_4831305, baseEnd_4831305] using wordTrace_append hprefix tailTrace_4831305
  have hstable : (prefixWord ++ tailWord_4831305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831305).length < 2 ^ (prefixWord ++ tailWord_4831305).sum := by decide
  have hdescent : baseEnd_4831305 < baseStart_4831305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831311 : List Nat := [1, 1, 2, 1, 1, 2, 2, 8, 5]
def baseStart_4831311 : Nat := 118140960795 + 4831311 * 2 ^ 59
def prefixEnd_4831311 : Nat := 4983230072969 + 3 ^ 40 * 4831311 * 2
def baseEnd_4831311 : Nat := 275642748261583578577079

theorem tailTrace_4831311 : CollatzResearch.WordTrace tailWord_4831311 prefixEnd_4831311 275642748261583578577079 := by
  unfold tailWord_4831311
  simp only [CollatzResearch.WordTrace]
  refine ⟨176212388599992844072573787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117474925733328562715049191 176212388599992844072573787)
  ·
    refine ⟨264318582899989266108860681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176212388599992844072573787 264318582899989266108860681)
    ·
      refine ⟨198238937174991949581645511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264318582899989266108860681 198238937174991949581645511)
      ·
        refine ⟨297358405762487924372468267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198238937174991949581645511 297358405762487924372468267)
        ·
          refine ⟨446037608643731886558702401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297358405762487924372468267 446037608643731886558702401)
          ·
            refine ⟨334528206482798914919026801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446037608643731886558702401 334528206482798914919026801)
            ·
              refine ⟨250896154862099186189270101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334528206482798914919026801 250896154862099186189270101)
              ·
                refine ⟨2940189314790224838155509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 250896154862099186189270101 2940189314790224838155509)
                ·
                  refine ⟨275642748261583578577079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2940189314790224838155509 275642748261583578577079)
                  ·
                    rfl

theorem cell23_4831311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 5].length) (baseStart_4831311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831311 prefixEnd_4831311 := by exact prefixLift 4831311
  have htrace : WordTrace (prefixWord ++ tailWord_4831311) baseStart_4831311 baseEnd_4831311 := by
    simpa [prefixWord, tailWord_4831311, baseEnd_4831311] using wordTrace_append hprefix tailTrace_4831311
  have hstable : (prefixWord ++ tailWord_4831311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831311).length < 2 ^ (prefixWord ++ tailWord_4831311).sum := by decide
  have hdescent : baseEnd_4831311 < baseStart_4831311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831321 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 2, 3, 3]
def baseStart_4831321 : Nat := 118140960795 + 4831321 * 2 ^ 59
def prefixEnd_4831321 : Nat := 4983230072969 + 3 ^ 40 * 4831321 * 2
def baseEnd_4831321 : Nat := 2480789869160797168068665

theorem tailTrace_4831321 : CollatzResearch.WordTrace tailWord_4831321 prefixEnd_4831321 2480789869160797168068665 := by
  unfold tailWord_4831321
  simp only [CollatzResearch.WordTrace]
  refine ⟨176212753329956615780437817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117475168886637743853625211 176212753329956615780437817)
  ·
    refine ⟨132159564997467461835328363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176212753329956615780437817 132159564997467461835328363)
    ·
      refine ⟨198239347496201192752992545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132159564997467461835328363 198239347496201192752992545)
      ·
        refine ⟨148679510622150894564744409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198239347496201192752992545 148679510622150894564744409)
        ·
          refine ⟨111509632966613170923558307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148679510622150894564744409 111509632966613170923558307)
          ·
            refine ⟨167264449449919756385337461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111509632966613170923558307 167264449449919756385337461)
            ·
              refine ⟨15681042135929977161125387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 167264449449919756385337461 15681042135929977161125387)
              ·
                refine ⟨23521563203894965741688081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15681042135929977161125387 23521563203894965741688081)
                ·
                  refine ⟨17641172402921224306266061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23521563203894965741688081 17641172402921224306266061)
                  ·
                    refine ⟨6615439651095459114849773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17641172402921224306266061 6615439651095459114849773)
                    ·
                      refine ⟨2480789869160797168068665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6615439651095459114849773 2480789869160797168068665)
                      ·
                        rfl

theorem cell23_4831321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_4831321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831321 prefixEnd_4831321 := by exact prefixLift 4831321
  have htrace : WordTrace (prefixWord ++ tailWord_4831321) baseStart_4831321 baseEnd_4831321 := by
    simpa [prefixWord, tailWord_4831321, baseEnd_4831321] using wordTrace_append hprefix tailTrace_4831321
  have hstable : (prefixWord ++ tailWord_4831321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831321).length < 2 ^ (prefixWord ++ tailWord_4831321).sum := by decide
  have hdescent : baseEnd_4831321 < baseStart_4831321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831341 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_4831341 : Nat := 118140960795 + 4831341 * 2 ^ 59
def prefixEnd_4831341 : Nat := 4983230072969 + 3 ^ 40 * 4831341 * 2
def baseEnd_4831341 : Nat := 826933379591295696606191

theorem tailTrace_4831341 : CollatzResearch.WordTrace tailWord_4831341 prefixEnd_4831341 826933379591295696606191 := by
  unfold tailWord_4831341
  simp only [CollatzResearch.WordTrace]
  refine ⟨176213482789884159196165877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117475655193256106130777251 176213482789884159196165877)
  ·
    refine ⟨16520014011551639924640551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176213482789884159196165877 16520014011551639924640551)
    ·
      refine ⟨24780021017327459886960827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16520014011551639924640551 24780021017327459886960827)
      ·
        refine ⟨37170031525991189830441241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24780021017327459886960827 37170031525991189830441241)
        ·
          refine ⟨27877523644493392372830931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37170031525991189830441241 27877523644493392372830931)
          ·
            refine ⟨41816285466740088559246397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27877523644493392372830931 41816285466740088559246397)
            ·
              refine ⟨15681107050027533209717399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41816285466740088559246397 15681107050027533209717399)
              ·
                refine ⟨23521660575041299814576099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15681107050027533209717399 23521660575041299814576099)
                ·
                  refine ⟨35282490862561949721864149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23521660575041299814576099 35282490862561949721864149)
                  ·
                    refine ⟨826933379591295696606191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35282490862561949721864149 826933379591295696606191)
                    ·
                      rfl

theorem cell23_4831341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_4831341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831341 prefixEnd_4831341 := by exact prefixLift 4831341
  have htrace : WordTrace (prefixWord ++ tailWord_4831341) baseStart_4831341 baseEnd_4831341 := by
    simpa [prefixWord, tailWord_4831341, baseEnd_4831341] using wordTrace_append hprefix tailTrace_4831341
  have hstable : (prefixWord ++ tailWord_4831341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831341).length < 2 ^ (prefixWord ++ tailWord_4831341).sum := by decide
  have hdescent : baseEnd_4831341 < baseStart_4831341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831354 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 3, 10]
def baseStart_4831354 : Nat := 118140960795 + 4831354 * 2 ^ 59
def prefixEnd_4831354 : Nat := 4983230072969 + 3 ^ 40 * 4831354 * 2
def baseEnd_4831354 : Nat := 826935604674131846318671

theorem tailTrace_4831354 : CollatzResearch.WordTrace tailWord_4831354 prefixEnd_4831354 826935604674131846318671 := by
  unfold tailWord_4831354
  simp only [CollatzResearch.WordTrace]
  refine ⟨44053489234709265604097279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117475971292558041610926077 44053489234709265604097279)
  ·
    refine ⟨66080233852063898406145919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44053489234709265604097279 66080233852063898406145919)
    ·
      refine ⟨99120350778095847609218879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66080233852063898406145919 99120350778095847609218879)
      ·
        refine ⟨148680526167143771413828319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99120350778095847609218879 148680526167143771413828319)
        ·
          refine ⟨223020789250715657120742479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148680526167143771413828319 223020789250715657120742479)
          ·
            refine ⟨334531183876073485681113719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223020789250715657120742479 334531183876073485681113719)
            ·
              refine ⟨501796775814110228521670579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334531183876073485681113719 501796775814110228521670579)
              ·
                refine ⟨752695163721165342782505869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501796775814110228521670579 752695163721165342782505869)
                ·
                  refine ⟨282260686395437003543439701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 752695163721165342782505869 282260686395437003543439701)
                  ·
                    refine ⟨826935604674131846318671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 282260686395437003543439701 826935604674131846318671)
                    ·
                      rfl

theorem cell23_4831354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_4831354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831354 prefixEnd_4831354 := by exact prefixLift 4831354
  have htrace : WordTrace (prefixWord ++ tailWord_4831354) baseStart_4831354 baseEnd_4831354 := by
    simpa [prefixWord, tailWord_4831354, baseEnd_4831354] using wordTrace_append hprefix tailTrace_4831354
  have hstable : (prefixWord ++ tailWord_4831354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831354).length < 2 ^ (prefixWord ++ tailWord_4831354).sum := by decide
  have hdescent : baseEnd_4831354 < baseStart_4831354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831381 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 3, 4, 3]
def baseStart_4831381 : Nat := 118140960795 + 4831381 * 2 ^ 59
def prefixEnd_4831381 : Nat := 4983230072969 + 3 ^ 40 * 4831381 * 2
def baseEnd_4831381 : Nat := 2480820678000066933318389

theorem tailTrace_4831381 : CollatzResearch.WordTrace tailWord_4831381 prefixEnd_4831381 2480820678000066933318389 := by
  unfold tailWord_4831381
  simp only [CollatzResearch.WordTrace]
  refine ⟨176214941709739246027621997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117476627806492830685081331 176214941709739246027621997)
  ·
    refine ⟨66080603141152217260358249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176214941709739246027621997 66080603141152217260358249)
    ·
      refine ⟨49560452355864162945268687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66080603141152217260358249 49560452355864162945268687)
      ·
        refine ⟨74340678533796244417903031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49560452355864162945268687 74340678533796244417903031)
        ·
          refine ⟨111511017800694366626854547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74340678533796244417903031 111511017800694366626854547)
          ·
            refine ⟨167266526701041549940281821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111511017800694366626854547 167266526701041549940281821)
            ·
              refine ⟨62724947512890581227605683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167266526701041549940281821 62724947512890581227605683)
              ·
                refine ⟨94087421269335871841408525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62724947512890581227605683 94087421269335871841408525)
                ·
                  refine ⟨35282782976000951940528197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94087421269335871841408525 35282782976000951940528197)
                  ·
                    refine ⟨6615521808000178488849037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35282782976000951940528197 6615521808000178488849037)
                    ·
                      refine ⟨2480820678000066933318389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6615521808000178488849037 2480820678000066933318389)
                      ·
                        rfl

theorem cell23_4831381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_4831381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831381 prefixEnd_4831381 := by exact prefixLift 4831381
  have htrace : WordTrace (prefixWord ++ tailWord_4831381) baseStart_4831381 baseEnd_4831381 := by
    simpa [prefixWord, tailWord_4831381, baseEnd_4831381] using wordTrace_append hprefix tailTrace_4831381
  have hstable : (prefixWord ++ tailWord_4831381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831381).length < 2 ^ (prefixWord ++ tailWord_4831381).sum := by decide
  have hdescent : baseEnd_4831381 < baseStart_4831381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831388 : List Nat := [2, 2, 3, 2, 1, 1, 1, 4, 3, 4]
def baseStart_4831388 : Nat := 118140960795 + 4831388 * 2 ^ 59
def prefixEnd_4831388 : Nat := 4983230072969 + 3 ^ 40 * 4831388 * 2
def baseEnd_4831388 : Nat := 826941424121549468643619

theorem tailTrace_4831388 : CollatzResearch.WordTrace tailWord_4831388 prefixEnd_4831388 826941424121549468643619 := by
  unfold tailWord_4831388
  simp only [CollatzResearch.WordTrace]
  refine ⟨88107598510356943111563409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117476798013809257482084545 88107598510356943111563409)
  ·
    refine ⟨66080698882767707333672557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88107598510356943111563409 66080698882767707333672557)
    ·
      refine ⟨24780262081037890250127209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66080698882767707333672557 24780262081037890250127209)
      ·
        refine ⟨18585196560778417687595407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24780262081037890250127209 18585196560778417687595407)
        ·
          refine ⟨27877794841167626531393111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18585196560778417687595407 27877794841167626531393111)
          ·
            refine ⟨41816692261751439797089667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27877794841167626531393111 41816692261751439797089667)
            ·
              refine ⟨62725038392627159695634501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41816692261751439797089667 62725038392627159695634501)
              ·
                refine ⟨11760944698617592442931469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62725038392627159695634501 11760944698617592442931469)
                ·
                  refine ⟨4410354261981597166099301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11760944698617592442931469 4410354261981597166099301)
                  ·
                    refine ⟨826941424121549468643619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4410354261981597166099301 826941424121549468643619)
                    ·
                      rfl

theorem cell23_4831388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_4831388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831388 prefixEnd_4831388 := by exact prefixLift 4831388
  have htrace : WordTrace (prefixWord ++ tailWord_4831388) baseStart_4831388 baseEnd_4831388 := by
    simpa [prefixWord, tailWord_4831388, baseEnd_4831388] using wordTrace_append hprefix tailTrace_4831388
  have hstable : (prefixWord ++ tailWord_4831388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831388).length < 2 ^ (prefixWord ++ tailWord_4831388).sum := by decide
  have hdescent : baseEnd_4831388 < baseStart_4831388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831422 : List Nat := [4, 2, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_4831422 : Nat := 118140960795 + 4831422 * 2 ^ 59
def prefixEnd_4831422 : Nat := 4983230072969 + 3 ^ 40 * 4831422 * 2
def baseEnd_4831422 : Nat := 826947243568967090968567

theorem tailTrace_4831422 : CollatzResearch.WordTrace tailWord_4831422 prefixEnd_4831422 826947243568967090968567 := by
  unfold tailWord_4831422
  simp only [CollatzResearch.WordTrace]
  refine ⟨22027054637823838753733065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117477624735060473353243013 22027054637823838753733065)
  ·
    refine ⟨16520290978367879065299799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22027054637823838753733065 16520290978367879065299799)
    ·
      refine ⟨24780436467551818597949699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16520290978367879065299799 24780436467551818597949699)
      ·
        refine ⟨37170654701327727896924549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24780436467551818597949699 37170654701327727896924549)
        ·
          refine ⟨6969497756498948980673353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37170654701327727896924549 6969497756498948980673353)
          ·
            refine ⟨5227123317374211735505015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6969497756498948980673353 5227123317374211735505015)
            ·
              refine ⟨7840684976061317603257523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5227123317374211735505015 7840684976061317603257523)
              ·
                refine ⟨11761027464091976404886285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7840684976061317603257523 11761027464091976404886285)
                ·
                  refine ⟨4410385299034491151832357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11761027464091976404886285 4410385299034491151832357)
                  ·
                    refine ⟨826947243568967090968567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4410385299034491151832357 826947243568967090968567)
                    ·
                      rfl

theorem cell23_4831422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_4831422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831422 prefixEnd_4831422 := by exact prefixLift 4831422
  have htrace : WordTrace (prefixWord ++ tailWord_4831422) baseStart_4831422 baseEnd_4831422 := by
    simpa [prefixWord, tailWord_4831422, baseEnd_4831422] using wordTrace_append hprefix tailTrace_4831422
  have hstable : (prefixWord ++ tailWord_4831422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831422).length < 2 ^ (prefixWord ++ tailWord_4831422).sum := by decide
  have hdescent : baseEnd_4831422 < baseStart_4831422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831448 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 3, 5]
def baseStart_4831448 : Nat := 118140960795 + 4831448 * 2 ^ 59
def prefixEnd_4831448 : Nat := 4983230072969 + 3 ^ 40 * 4831448 * 2
def baseEnd_4831448 : Nat := 826951693734639390393527

theorem tailTrace_4831448 : CollatzResearch.WordTrace tailWord_4831448 prefixEnd_4831448 826951693734639390393527 := by
  unfold tailWord_4831448
  simp only [CollatzResearch.WordTrace]
  refine ⟨88108692700248258235155499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117478256933664344313540665 88108692700248258235155499)
  ·
    refine ⟨132163039050372387352733249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88108692700248258235155499 132163039050372387352733249)
    ·
      refine ⟨99122279287779290514549937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132163039050372387352733249 99122279287779290514549937)
      ·
        refine ⟨74341709465834467885912453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99122279287779290514549937 74341709465834467885912453)
        ·
          refine ⟨13939070524843962728608585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74341709465834467885912453 13939070524843962728608585)
          ·
            refine ⟨10454302893632972046456439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13939070524843962728608585 10454302893632972046456439)
            ·
              refine ⟨15681454340449458069684659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10454302893632972046456439 15681454340449458069684659)
              ·
                refine ⟨23522181510674187104526989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15681454340449458069684659 23522181510674187104526989)
                ·
                  refine ⟨8820818066502820164197621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23522181510674187104526989 8820818066502820164197621)
                  ·
                    refine ⟨826951693734639390393527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8820818066502820164197621 826951693734639390393527)
                    ·
                      rfl

theorem cell23_4831448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_4831448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831448 prefixEnd_4831448 := by exact prefixLift 4831448
  have htrace : WordTrace (prefixWord ++ tailWord_4831448) baseStart_4831448 baseEnd_4831448 := by
    simpa [prefixWord, tailWord_4831448, baseEnd_4831448] using wordTrace_append hprefix tailTrace_4831448
  have hstable : (prefixWord ++ tailWord_4831448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831448).length < 2 ^ (prefixWord ++ tailWord_4831448).sum := by decide
  have hdescent : baseEnd_4831448 < baseStart_4831448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831481 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 1, 1, 6]
def baseStart_4831481 : Nat := 118140960795 + 4831481 * 2 ^ 59
def prefixEnd_4831481 : Nat := 4983230072969 + 3 ^ 40 * 4831481 * 2
def baseEnd_4831481 : Nat := 2480872026065516542067929

theorem tailTrace_4831481 : CollatzResearch.WordTrace tailWord_4831481 prefixEnd_4831481 2480872026065516542067929 := by
  unfold tailWord_4831481
  simp only [CollatzResearch.WordTrace]
  refine ⟨176218589009376963106262297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117479059339584642070841531 176218589009376963106262297)
  ·
    refine ⟨132163941757032722329696723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176218589009376963106262297 132163941757032722329696723)
    ·
      refine ⟨198245912635549083494545085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132163941757032722329696723 198245912635549083494545085)
      ·
        refine ⟨74342217238330906310454407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198245912635549083494545085 74342217238330906310454407)
        ·
          refine ⟨111513325857496359465681611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74342217238330906310454407 111513325857496359465681611)
          ·
            refine ⟨167269988786244539198522417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111513325857496359465681611 167269988786244539198522417)
            ·
              refine ⟨125452491589683404398891813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167269988786244539198522417 125452491589683404398891813)
              ·
                refine ⟨23522342173065638324792215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125452491589683404398891813 23522342173065638324792215)
                ·
                  refine ⟨35283513259598457487188323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23522342173065638324792215 35283513259598457487188323)
                  ·
                    refine ⟨52925269889397686230782485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35283513259598457487188323 52925269889397686230782485)
                    ·
                      refine ⟨2480872026065516542067929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52925269889397686230782485 2480872026065516542067929)
                      ·
                        rfl

theorem cell23_4831481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_4831481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831481 prefixEnd_4831481 := by exact prefixLift 4831481
  have htrace : WordTrace (prefixWord ++ tailWord_4831481) baseStart_4831481 baseEnd_4831481 := by
    simpa [prefixWord, tailWord_4831481, baseEnd_4831481] using wordTrace_append hprefix tailTrace_4831481
  have hstable : (prefixWord ++ tailWord_4831481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831481).length < 2 ^ (prefixWord ++ tailWord_4831481).sum := by decide
  have hdescent : baseEnd_4831481 < baseStart_4831481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831485 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 7, 2, 2]
def baseStart_4831485 : Nat := 118140960795 + 4831485 * 2 ^ 59
def prefixEnd_4831485 : Nat := 4983230072969 + 3 ^ 40 * 4831485 * 2
def baseEnd_4831485 : Nat := 2480874079988134526417911

theorem tailTrace_4831485 : CollatzResearch.WordTrace tailWord_4831485 prefixEnd_4831485 2480874079988134526417911 := by
  unfold tailWord_4831485
  simp only [CollatzResearch.WordTrace]
  refine ⟨176218734901362471789407909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117479156600908314526271939 176218734901362471789407909)
  ·
    refine ⟨33041012794005463460513983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176218734901362471789407909 33041012794005463460513983)
    ·
      refine ⟨49561519191008195190770975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33041012794005463460513983 49561519191008195190770975)
      ·
        refine ⟨74342278786512292786156463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49561519191008195190770975 74342278786512292786156463)
        ·
          refine ⟨111513418179768439179234695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74342278786512292786156463 111513418179768439179234695)
          ·
            refine ⟨167270127269652658768852043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111513418179768439179234695 167270127269652658768852043)
            ·
              refine ⟨250905190904478988153278065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167270127269652658768852043 250905190904478988153278065)
              ·
                refine ⟨188178893178359241114958549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250905190904478988153278065 188178893178359241114958549)
                ·
                  refine ⟨4410442808867794713631841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 188178893178359241114958549 4410442808867794713631841)
                  ·
                    refine ⟨3307832106650846035223881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4410442808867794713631841 3307832106650846035223881)
                    ·
                      refine ⟨2480874079988134526417911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3307832106650846035223881 2480874079988134526417911)
                      ·
                        rfl

theorem cell23_4831485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_4831485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831485 prefixEnd_4831485 := by exact prefixLift 4831485
  have htrace : WordTrace (prefixWord ++ tailWord_4831485) baseStart_4831485 baseEnd_4831485 := by
    simpa [prefixWord, tailWord_4831485, baseEnd_4831485] using wordTrace_append hprefix tailTrace_4831485
  have hstable : (prefixWord ++ tailWord_4831485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831485).length < 2 ^ (prefixWord ++ tailWord_4831485).sum := by decide
  have hdescent : baseEnd_4831485 < baseStart_4831485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831488 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 3]
def baseStart_4831488 : Nat := 118140960795 + 4831488 * 2 ^ 59
def prefixEnd_4831488 : Nat := 4983230072969 + 3 ^ 40 * 4831488 * 2
def baseEnd_4831488 : Nat := 2480875620430098014680397

theorem tailTrace_4831488 : CollatzResearch.WordTrace tailWord_4831488 prefixEnd_4831488 2480875620430098014680397 := by
  unfold tailWord_4831488
  simp only [CollatzResearch.WordTrace]
  refine ⟨88109422160175801650883559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117479229546901068867844745 88109422160175801650883559)
  ·
    refine ⟨132164133240263702476325339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88109422160175801650883559 132164133240263702476325339)
    ·
      refine ⟨198246199860395553714488009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132164133240263702476325339 198246199860395553714488009)
      ·
        refine ⟨148684649895296665285866007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198246199860395553714488009 148684649895296665285866007)
        ·
          refine ⟨223026974842944997928799011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148684649895296665285866007 223026974842944997928799011)
          ·
            refine ⟨334540462264417496893198517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223026974842944997928799011 334540462264417496893198517)
            ·
              refine ⟨31363168337289140333737361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 334540462264417496893198517 31363168337289140333737361)
              ·
                refine ⟨23522376252966855250303021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31363168337289140333737361 23522376252966855250303021)
                ·
                  refine ⟨8820891094862570718863633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23522376252966855250303021 8820891094862570718863633)
                  ·
                    refine ⟨6615668321146928039147725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8820891094862570718863633 6615668321146928039147725)
                    ·
                      refine ⟨2480875620430098014680397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6615668321146928039147725 2480875620430098014680397)
                      ·
                        rfl

theorem cell23_4831488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_4831488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831488 prefixEnd_4831488 := by exact prefixLift 4831488
  have htrace : WordTrace (prefixWord ++ tailWord_4831488) baseStart_4831488 baseEnd_4831488 := by
    simpa [prefixWord, tailWord_4831488, baseEnd_4831488] using wordTrace_append hprefix tailTrace_4831488
  have hstable : (prefixWord ++ tailWord_4831488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831488).length < 2 ^ (prefixWord ++ tailWord_4831488).sum := by decide
  have hdescent : baseEnd_4831488 < baseStart_4831488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831498 : List Nat := [3, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_4831498 : Nat := 118140960795 + 4831498 * 2 ^ 59
def prefixEnd_4831498 : Nat := 4983230072969 + 3 ^ 40 * 4831498 * 2
def baseEnd_4831498 : Nat := 2480880755236642975555351

theorem tailTrace_4831498 : CollatzResearch.WordTrace tailWord_4831498 prefixEnd_4831498 2480880755236642975555351 := by
  unfold tailWord_4831498
  simp only [CollatzResearch.WordTrace]
  refine ⟨44054802262578843752407787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117479472700210250006420765 44054802262578843752407787)
  ·
    refine ⟨66082203393868265628611681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44054802262578843752407787 66082203393868265628611681)
    ·
      refine ⟨49561652545401199221458761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66082203393868265628611681 49561652545401199221458761)
      ·
        refine ⟨37171239409050899416094071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49561652545401199221458761 37171239409050899416094071)
        ·
          refine ⟨55756859113576349124141107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37171239409050899416094071 55756859113576349124141107)
          ·
            refine ⟨83635288670364523686211661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55756859113576349124141107 83635288670364523686211661)
            ·
              refine ⟨31363233251386696382329373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83635288670364523686211661 31363233251386696382329373)
              ·
                refine ⟨11761212469270011143373515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31363233251386696382329373 11761212469270011143373515)
                ·
                  refine ⟨17641818703905016715060273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11761212469270011143373515 17641818703905016715060273)
                  ·
                    refine ⟨13231364027928762536295205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17641818703905016715060273 13231364027928762536295205)
                    ·
                      refine ⟨2480880755236642975555351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13231364027928762536295205 2480880755236642975555351)
                      ·
                        rfl

theorem cell23_4831498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_4831498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831498 prefixEnd_4831498 := by exact prefixLift 4831498
  have htrace : WordTrace (prefixWord ++ tailWord_4831498) baseStart_4831498 baseEnd_4831498 := by
    simpa [prefixWord, tailWord_4831498, baseEnd_4831498] using wordTrace_append hprefix tailTrace_4831498
  have hstable : (prefixWord ++ tailWord_4831498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831498).length < 2 ^ (prefixWord ++ tailWord_4831498).sum := by decide
  have hdescent : baseEnd_4831498 < baseStart_4831498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831502 : List Nat := [4, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2]
def baseStart_4831502 : Nat := 118140960795 + 4831502 * 2 ^ 59
def prefixEnd_4831502 : Nat := 4983230072969 + 3 ^ 40 * 4831502 * 2
def baseEnd_4831502 : Nat := 2480882809159260959905333

theorem tailTrace_4831502 : CollatzResearch.WordTrace tailWord_4831502 prefixEnd_4831502 2480882809159260959905333 := by
  unfold tailWord_4831502
  simp only [CollatzResearch.WordTrace]
  refine ⟨22027419367787610461597095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117479569961533922461851173 22027419367787610461597095)
  ·
    refine ⟨33041129051681415692395643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22027419367787610461597095 33041129051681415692395643)
    ·
      refine ⟨49561693577522123538593465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33041129051681415692395643 49561693577522123538593465)
      ·
        refine ⟨37171270183141592653945099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49561693577522123538593465 37171270183141592653945099)
        ·
          refine ⟨55756905274712388980917649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37171270183141592653945099 55756905274712388980917649)
          ·
            refine ⟨41817678956034291735688237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55756905274712388980917649 41817678956034291735688237)
            ·
              refine ⟨15681629608512859400883089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41817678956034291735688237 15681629608512859400883089)
              ·
                refine ⟨11761222206384644550662317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15681629608512859400883089 11761222206384644550662317)
                ·
                  refine ⟨4410458327394241706498369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11761222206384644550662317 4410458327394241706498369)
                  ·
                    refine ⟨3307843745545681279873777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4410458327394241706498369 3307843745545681279873777)
                    ·
                      refine ⟨2480882809159260959905333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3307843745545681279873777 2480882809159260959905333)
                      ·
                        rfl

theorem cell23_4831502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_4831502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831502 prefixEnd_4831502 := by exact prefixLift 4831502
  have htrace : WordTrace (prefixWord ++ tailWord_4831502) baseStart_4831502 baseEnd_4831502 := by
    simpa [prefixWord, tailWord_4831502, baseEnd_4831502] using wordTrace_append hprefix tailTrace_4831502
  have hstable : (prefixWord ++ tailWord_4831502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831502).length < 2 ^ (prefixWord ++ tailWord_4831502).sum := by decide
  have hdescent : baseEnd_4831502 < baseStart_4831502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831519 : List Nat := [1, 1, 2, 4, 3, 1, 1, 5, 1, 2, 2]
def baseStart_4831519 : Nat := 118140960795 + 4831519 * 2 ^ 59
def prefixEnd_4831519 : Nat := 4983230072969 + 3 ^ 40 * 4831519 * 2
def baseEnd_4831519 : Nat := 2480891538330387393392755

theorem tailTrace_4831519 : CollatzResearch.WordTrace tailWord_4831519 prefixEnd_4831519 2480891538330387393392755 := by
  unfold tailWord_4831519
  simp only [CollatzResearch.WordTrace]
  refine ⟨176219974983239295596145611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117479983322159530397430407 176219974983239295596145611)
  ·
    refine ⟨264329962474858943394218417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176219974983239295596145611 264329962474858943394218417)
    ·
      refine ⟨198247471856144207545663813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264329962474858943394218417 198247471856144207545663813)
      ·
        refine ⟨37171400973027038914811965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198247471856144207545663813 37171400973027038914811965)
        ·
          refine ⟨13939275364885139593054487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37171400973027038914811965 13939275364885139593054487)
          ·
            refine ⟨20908913047327709389581731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13939275364885139593054487 20908913047327709389581731)
            ·
              refine ⟨31363369570991564084372597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20908913047327709389581731 31363369570991564084372597)
              ·
                refine ⟨2940315897280459132909931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31363369570991564084372597 2940315897280459132909931)
                ·
                  refine ⟨4410473845920688699364897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2940315897280459132909931 4410473845920688699364897)
                  ·
                    refine ⟨3307855384440516524523673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4410473845920688699364897 3307855384440516524523673)
                    ·
                      refine ⟨2480891538330387393392755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3307855384440516524523673 2480891538330387393392755)
                      ·
                        rfl

theorem cell23_4831519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_4831519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831519 prefixEnd_4831519 := by exact prefixLift 4831519
  have htrace : WordTrace (prefixWord ++ tailWord_4831519) baseStart_4831519 baseEnd_4831519 := by
    simpa [prefixWord, tailWord_4831519, baseEnd_4831519] using wordTrace_append hprefix tailTrace_4831519
  have hstable : (prefixWord ++ tailWord_4831519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831519).length < 2 ^ (prefixWord ++ tailWord_4831519).sum := by decide
  have hdescent : baseEnd_4831519 < baseStart_4831519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831522 : List Nat := [3, 3, 1, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_4831522 : Nat := 118140960795 + 4831522 * 2 ^ 59
def prefixEnd_4831522 : Nat := 4983230072969 + 3 ^ 40 * 4831522 * 2
def baseEnd_4831522 : Nat := 2480893078772350881655241

theorem tailTrace_4831522 : CollatzResearch.WordTrace tailWord_4831522 prefixEnd_4831522 2480893078772350881655241 := by
  unfold tailWord_4831522
  simp only [CollatzResearch.WordTrace]
  refine ⟨44055021100557106777126205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117480056268152284739003213 44055021100557106777126205)
  ·
    refine ⟨16520632912708915041422327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44055021100557106777126205 16520632912708915041422327)
    ·
      refine ⟨24780949369063372562133491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16520632912708915041422327 24780949369063372562133491)
      ·
        refine ⟨37171424053595058843200237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24780949369063372562133491 37171424053595058843200237)
        ·
          refine ⟨13939284020098147066200089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37171424053595058843200237 13939284020098147066200089)
          ·
            refine ⟨10454463015073610299650067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13939284020098147066200089 10454463015073610299650067)
            ·
              refine ⟨15681694522610415449475101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10454463015073610299650067 15681694522610415449475101)
              ·
                refine ⟨5880635445978905793553163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15681694522610415449475101 5880635445978905793553163)
                ·
                  refine ⟨8820953168968358690329745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5880635445978905793553163 8820953168968358690329745)
                  ·
                    refine ⟨6615714876726269017747309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8820953168968358690329745 6615714876726269017747309)
                    ·
                      refine ⟨2480893078772350881655241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6615714876726269017747309 2480893078772350881655241)
                      ·
                        rfl

theorem cell23_4831522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_4831522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831522 prefixEnd_4831522 := by exact prefixLift 4831522
  have htrace : WordTrace (prefixWord ++ tailWord_4831522) baseStart_4831522 baseEnd_4831522 := by
    simpa [prefixWord, tailWord_4831522, baseEnd_4831522] using wordTrace_append hprefix tailTrace_4831522
  have hstable : (prefixWord ++ tailWord_4831522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831522).length < 2 ^ (prefixWord ++ tailWord_4831522).sum := by decide
  have hdescent : baseEnd_4831522 < baseStart_4831522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831575 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 3, 4, 2]
def baseStart_4831575 : Nat := 118140960795 + 4831575 * 2 ^ 59
def prefixEnd_4831575 : Nat := 4983230072969 + 3 ^ 40 * 4831575 * 2
def baseEnd_4831575 : Nat := 2480920293247039174292497

theorem tailTrace_4831575 : CollatzResearch.WordTrace tailWord_4831575 prefixEnd_4831575 2480920293247039174292497 := by
  unfold tailWord_4831575
  simp only [CollatzResearch.WordTrace]
  refine ⟨176222017471036417160184179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117481344980690944773456119 176222017471036417160184179)
  ·
    refine ⟨264333026206554625740276269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176222017471036417160184179 264333026206554625740276269)
    ·
      refine ⟨99124884827457984652603601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264333026206554625740276269 99124884827457984652603601)
      ·
        refine ⟨74343663620593488489452701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99124884827457984652603601 74343663620593488489452701)
        ·
          refine ⟨27878873857722558183544763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74343663620593488489452701 27878873857722558183544763)
          ·
            refine ⟨41818310786583837275317145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27878873857722558183544763 41818310786583837275317145)
            ·
              refine ⟨31363733089937877956487859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41818310786583837275317145 31363733089937877956487859)
              ·
                refine ⟨47045599634906816934731789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31363733089937877956487859 47045599634906816934731789)
                ·
                  refine ⟨17642099863090056350524421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47045599634906816934731789 17642099863090056350524421)
                  ·
                    refine ⟨3307893724329385565723329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17642099863090056350524421 3307893724329385565723329)
                    ·
                      refine ⟨2480920293247039174292497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3307893724329385565723329 2480920293247039174292497)
                      ·
                        rfl

theorem cell23_4831575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_4831575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831575 prefixEnd_4831575 := by exact prefixLift 4831575
  have htrace : WordTrace (prefixWord ++ tailWord_4831575) baseStart_4831575 baseEnd_4831575 := by
    simpa [prefixWord, tailWord_4831575, baseEnd_4831575] using wordTrace_append hprefix tailTrace_4831575
  have hstable : (prefixWord ++ tailWord_4831575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831575).length < 2 ^ (prefixWord ++ tailWord_4831575).sum := by decide
  have hdescent : baseEnd_4831575 < baseStart_4831575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831578 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3]
def baseStart_4831578 : Nat := 118140960795 + 4831578 * 2 ^ 59
def prefixEnd_4831578 : Nat := 4983230072969 + 3 ^ 40 * 4831578 * 2
def baseEnd_4831578 : Nat := 2480921833689002662554983

theorem tailTrace_4831578 : CollatzResearch.WordTrace tailWord_4831578 prefixEnd_4831578 2480921833689002662554983 := by
  unfold tailWord_4831578
  simp only [CollatzResearch.WordTrace]
  refine ⟨44055531722506387168135847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117481417926683699115028925 44055531722506387168135847)
  ·
    refine ⟨66083297583759580752203771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44055531722506387168135847 66083297583759580752203771)
    ·
      refine ⟨99124946375639371128305657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66083297583759580752203771 99124946375639371128305657)
      ·
        refine ⟨74343709781729528346229243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99124946375639371128305657 74343709781729528346229243)
        ·
          refine ⟨111515564672594292519343865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74343709781729528346229243 111515564672594292519343865)
          ·
            refine ⟨83636673504445719389507899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111515564672594292519343865 83636673504445719389507899)
            ·
              refine ⟨125455010256668579084261849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83636673504445719389507899 125455010256668579084261849)
              ·
                refine ⟨94091257692501434313196387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125455010256668579084261849 94091257692501434313196387)
                ·
                  refine ⟨141136886538752151469794581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94091257692501434313196387 141136886538752151469794581)
                  ·
                    refine ⟨6615791556504007100146621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 141136886538752151469794581 6615791556504007100146621)
                    ·
                      refine ⟨2480921833689002662554983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6615791556504007100146621 2480921833689002662554983)
                      ·
                        rfl

theorem cell23_4831578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_4831578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831578 prefixEnd_4831578 := by exact prefixLift 4831578
  have htrace : WordTrace (prefixWord ++ tailWord_4831578) baseStart_4831578 baseEnd_4831578 := by
    simpa [prefixWord, tailWord_4831578, baseEnd_4831578] using wordTrace_append hprefix tailTrace_4831578
  have hstable : (prefixWord ++ tailWord_4831578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831578).length < 2 ^ (prefixWord ++ tailWord_4831578).sum := by decide
  have hdescent : baseEnd_4831578 < baseStart_4831578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831649 : List Nat := [1, 2, 3, 5, 1, 1, 1, 4, 5]
def baseStart_4831649 : Nat := 118140960795 + 4831649 * 2 ^ 59
def prefixEnd_4831649 : Nat := 4983230072969 + 3 ^ 40 * 4831649 * 2
def baseEnd_4831649 : Nat := 275662032312830209418573

theorem tailTrace_4831649 : CollatzResearch.WordTrace tailWord_4831649 prefixEnd_4831649 275662032312830209418573 := by
  unfold tailWord_4831649
  simp only [CollatzResearch.WordTrace]
  refine ⟨176224716472768327798378001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117483144315178885198918667 176224716472768327798378001)
  ·
    refine ⟨132168537354576245848783501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176224716472768327798378001 132168537354576245848783501)
    ·
      refine ⟨49563201507966092193293813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132168537354576245848783501 49563201507966092193293813)
      ·
        refine ⟨4646550141371821143121295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49563201507966092193293813 4646550141371821143121295)
        ·
          refine ⟨6969825212057731714681943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4646550141371821143121295 6969825212057731714681943)
          ·
            refine ⟨10454737818086597572022915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6969825212057731714681943 10454737818086597572022915)
            ·
              refine ⟨15682106727129896358034373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10454737818086597572022915 15682106727129896358034373)
              ·
                refine ⟨2940395011336855567131445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15682106727129896358034373 2940395011336855567131445)
                ·
                  refine ⟨275662032312830209418573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2940395011336855567131445 275662032312830209418573)
                  ·
                    rfl

theorem cell23_4831649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 5].length) (baseStart_4831649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831649 prefixEnd_4831649 := by exact prefixLift 4831649
  have htrace : WordTrace (prefixWord ++ tailWord_4831649) baseStart_4831649 baseEnd_4831649 := by
    simpa [prefixWord, tailWord_4831649, baseEnd_4831649] using wordTrace_append hprefix tailTrace_4831649
  have hstable : (prefixWord ++ tailWord_4831649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831649).length < 2 ^ (prefixWord ++ tailWord_4831649).sum := by decide
  have hdescent : baseEnd_4831649 < baseStart_4831649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831655 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_4831655 : Nat := 118140960795 + 4831655 * 2 ^ 59
def prefixEnd_4831655 : Nat := 4983230072969 + 3 ^ 40 * 4831655 * 2
def baseEnd_4831655 : Nat := 2480961371699398861292129

theorem tailTrace_4831655 : CollatzResearch.WordTrace tailWord_4831655 prefixEnd_4831655 2480961371699398861292129 := by
  unfold tailWord_4831655
  simp only [CollatzResearch.WordTrace]
  refine ⟨176224935310746590823096419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117483290207164393882064279 176224935310746590823096419)
  ·
    refine ⟨264337402966119886234644629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176224935310746590823096419 264337402966119886234644629)
    ·
      refine ⟨12390815764036869667248967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 264337402966119886234644629 12390815764036869667248967)
      ·
        refine ⟨18586223646055304500873451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12390815764036869667248967 18586223646055304500873451)
        ·
          refine ⟨27879335469082956751310177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18586223646055304500873451 27879335469082956751310177)
          ·
            refine ⟨20909501601812217563482633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27879335469082956751310177 20909501601812217563482633)
            ·
              refine ⟨15682126201359163172611975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20909501601812217563482633 15682126201359163172611975)
              ·
                refine ⟨23523189302038744758917963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15682126201359163172611975 23523189302038744758917963)
                ·
                  refine ⟨35284783953058117138376945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23523189302038744758917963 35284783953058117138376945)
                  ·
                    refine ⟨26463587964793587853782709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35284783953058117138376945 26463587964793587853782709)
                    ·
                      refine ⟨2480961371699398861292129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26463587964793587853782709 2480961371699398861292129)
                      ·
                        rfl

theorem cell23_4831655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_4831655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831655 prefixEnd_4831655 := by exact prefixLift 4831655
  have htrace : WordTrace (prefixWord ++ tailWord_4831655) baseStart_4831655 baseEnd_4831655 := by
    simpa [prefixWord, tailWord_4831655, baseEnd_4831655] using wordTrace_append hprefix tailTrace_4831655
  have hstable : (prefixWord ++ tailWord_4831655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831655).length < 2 ^ (prefixWord ++ tailWord_4831655).sum := by decide
  have hdescent : baseEnd_4831655 < baseStart_4831655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831709 : List Nat := [1, 4, 3, 1, 1, 1, 1, 6, 1, 4]
def baseStart_4831709 : Nat := 118140960795 + 4831709 * 2 ^ 59
def prefixEnd_4831709 : Nat := 4983230072969 + 3 ^ 40 * 4831709 * 2
def baseEnd_4831709 : Nat := 826996366551580550005627

theorem tailTrace_4831709 : CollatzResearch.WordTrace tailWord_4831709 prefixEnd_4831709 826996366551580550005627 := by
  unfold tailWord_4831709
  simp only [CollatzResearch.WordTrace]
  refine ⟨176226904852550958045562181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117484603235033972030374787 176226904852550958045562181)
  ·
    refine ⟨33042544659853304633542909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176226904852550958045562181 33042544659853304633542909)
    ·
      refine ⟨12390954247444989237578591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33042544659853304633542909 12390954247444989237578591)
      ·
        refine ⟨18586431371167483856367887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12390954247444989237578591 18586431371167483856367887)
        ·
          refine ⟨27879647056751225784551831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18586431371167483856367887 27879647056751225784551831)
          ·
            refine ⟨41819470585126838676827747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27879647056751225784551831 41819470585126838676827747)
            ·
              refine ⟨62729205877690258015241621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41819470585126838676827747 62729205877690258015241621)
              ·
                refine ⟨2940431525516730844464451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62729205877690258015241621 2940431525516730844464451)
                ·
                  refine ⟨4410647288275096266696677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2940431525516730844464451 4410647288275096266696677)
                  ·
                    refine ⟨826996366551580550005627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4410647288275096266696677 826996366551580550005627)
                    ·
                      rfl

theorem cell23_4831709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_4831709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831709 prefixEnd_4831709 := by exact prefixLift 4831709
  have htrace : WordTrace (prefixWord ++ tailWord_4831709) baseStart_4831709 baseEnd_4831709 := by
    simpa [prefixWord, tailWord_4831709, baseEnd_4831709] using wordTrace_append hprefix tailTrace_4831709
  have hstable : (prefixWord ++ tailWord_4831709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831709).length < 2 ^ (prefixWord ++ tailWord_4831709).sum := by decide
  have hdescent : baseEnd_4831709 < baseStart_4831709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831775 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 3]
def baseStart_4831775 : Nat := 118140960795 + 4831775 * 2 ^ 59
def prefixEnd_4831775 : Nat := 4983230072969 + 3 ^ 40 * 4831775 * 2
def baseEnd_4831775 : Nat := 2481022989377938391791577

theorem tailTrace_4831775 : CollatzResearch.WordTrace tailWord_4831775 prefixEnd_4831775 2481022989377938391791577 := by
  unfold tailWord_4831775
  simp only [CollatzResearch.WordTrace]
  refine ⟨176229312070311851317464779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117486208046874567544976519 176229312070311851317464779)
  ·
    refine ⟨264343968105467776976197169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176229312070311851317464779 264343968105467776976197169)
    ·
      refine ⟨198257976079100832732147877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264343968105467776976197169 198257976079100832732147877)
      ·
        refine ⟨37173370514831406137277727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198257976079100832732147877 37173370514831406137277727)
        ·
          refine ⟨55760055772247109205916591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37173370514831406137277727 55760055772247109205916591)
          ·
            refine ⟨83640083658370663808874887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55760055772247109205916591 83640083658370663808874887)
            ·
              refine ⟨125460125487555995713312331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83640083658370663808874887 125460125487555995713312331)
              ·
                refine ⟨188190188231333993569968497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125460125487555995713312331 188190188231333993569968497)
                ·
                  refine ⟨141142641173500495177476373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188190188231333993569968497 141142641173500495177476373)
                  ·
                    refine ⟨6616061305007835711444205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 141142641173500495177476373 6616061305007835711444205)
                    ·
                      refine ⟨2481022989377938391791577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6616061305007835711444205 2481022989377938391791577)
                      ·
                        rfl

theorem cell23_4831775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_4831775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831775 prefixEnd_4831775 := by exact prefixLift 4831775
  have htrace : WordTrace (prefixWord ++ tailWord_4831775) baseStart_4831775 baseEnd_4831775 := by
    simpa [prefixWord, tailWord_4831775, baseEnd_4831775] using wordTrace_append hprefix tailTrace_4831775
  have hstable : (prefixWord ++ tailWord_4831775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831775).length < 2 ^ (prefixWord ++ tailWord_4831775).sum := by decide
  have hdescent : baseEnd_4831775 < baseStart_4831775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831802 : List Nat := [3, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4]
def baseStart_4831802 : Nat := 118140960795 + 4831802 * 2 ^ 59
def prefixEnd_4831802 : Nat := 4983230072969 + 3 ^ 40 * 4831802 * 2
def baseEnd_4831802 : Nat := 2481036853355609786153953

theorem tailTrace_4831802 : CollatzResearch.WordTrace tailWord_4831802 prefixEnd_4831802 2481036853355609786153953 := by
  unfold tailWord_4831802
  simp only [CollatzResearch.WordTrace]
  refine ⟨44057574210303508732174415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117486864560809356619131773 44057574210303508732174415)
  ·
    refine ⟨66086361315455263098261623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44057574210303508732174415 66086361315455263098261623)
    ·
      refine ⟨99129541973182894647392435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66086361315455263098261623 99129541973182894647392435)
      ·
        refine ⟨148694312959774341971088653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99129541973182894647392435 148694312959774341971088653)
        ·
          refine ⟨55760367359915378239158245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148694312959774341971088653 55760367359915378239158245)
          ·
            refine ⟨10455068879984133419842171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55760367359915378239158245 10455068879984133419842171)
            ·
              refine ⟨15682603319976200129763257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10455068879984133419842171 15682603319976200129763257)
              ·
                refine ⟨11761952489982150097322443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15682603319976200129763257 11761952489982150097322443)
                ·
                  refine ⟨17642928734973225145983665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11761952489982150097322443 17642928734973225145983665)
                  ·
                    refine ⟨13232196551229918859487749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17642928734973225145983665 13232196551229918859487749)
                    ·
                      refine ⟨2481036853355609786153953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13232196551229918859487749 2481036853355609786153953)
                      ·
                        rfl

theorem cell23_4831802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_4831802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831802 prefixEnd_4831802 := by exact prefixLift 4831802
  have htrace : WordTrace (prefixWord ++ tailWord_4831802) baseStart_4831802 baseEnd_4831802 := by
    simpa [prefixWord, tailWord_4831802, baseEnd_4831802] using wordTrace_append hprefix tailTrace_4831802
  have hstable : (prefixWord ++ tailWord_4831802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831802).length < 2 ^ (prefixWord ++ tailWord_4831802).sum := by decide
  have hdescent : baseEnd_4831802 < baseStart_4831802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831809 : List Nat := [1, 2, 5, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_4831809 : Nat := 118140960795 + 4831809 * 2 ^ 59
def prefixEnd_4831809 : Nat := 4983230072969 + 3 ^ 40 * 4831809 * 2
def baseEnd_4831809 : Nat := 2481040447720191258766421

theorem tailTrace_4831809 : CollatzResearch.WordTrace tailWord_4831809 prefixEnd_4831809 2481040447720191258766421 := by
  unfold tailWord_4831809
  simp only [CollatzResearch.WordTrace]
  refine ⟨176230552152188675124202481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117487034768125783416134987 176230552152188675124202481)
  ·
    refine ⟨132172914114141506343151861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176230552152188675124202481 132172914114141506343151861)
    ·
      refine ⟨12391210698200766219670487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132172914114141506343151861 12391210698200766219670487)
      ·
        refine ⟨18586816047301149329505731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12391210698200766219670487 18586816047301149329505731)
        ·
          refine ⟨27880224070951723994258597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18586816047301149329505731 27880224070951723994258597)
          ·
            refine ⟨5227542013303448248923487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27880224070951723994258597 5227542013303448248923487)
            ·
              refine ⟨7841313019955172373385231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5227542013303448248923487 7841313019955172373385231)
              ·
                refine ⟨11761969529932758560077847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7841313019955172373385231 11761969529932758560077847)
                ·
                  refine ⟨17642954294899137840116771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11761969529932758560077847 17642954294899137840116771)
                  ·
                    refine ⟨26464431442348706760175157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17642954294899137840116771 26464431442348706760175157)
                    ·
                      refine ⟨2481040447720191258766421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26464431442348706760175157 2481040447720191258766421)
                      ·
                        rfl

theorem cell23_4831809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_4831809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831809 prefixEnd_4831809 := by exact prefixLift 4831809
  have htrace : WordTrace (prefixWord ++ tailWord_4831809) baseStart_4831809 baseEnd_4831809 := by
    simpa [prefixWord, tailWord_4831809, baseEnd_4831809] using wordTrace_append hprefix tailTrace_4831809
  have hstable : (prefixWord ++ tailWord_4831809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831809).length < 2 ^ (prefixWord ++ tailWord_4831809).sum := by decide
  have hdescent : baseEnd_4831809 < baseStart_4831809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831823 : List Nat := [1, 1, 2, 1, 1, 2, 8, 2, 1, 2, 2]
def baseStart_4831823 : Nat := 118140960795 + 4831823 * 2 ^ 59
def prefixEnd_4831823 : Nat := 4983230072969 + 3 ^ 40 * 4831823 * 2
def baseEnd_4831823 : Nat := 2481047636449354203991357

theorem tailTrace_4831823 : CollatzResearch.WordTrace tailWord_4831823 prefixEnd_4831823 2481047636449354203991357 := by
  unfold tailWord_4831823
  simp only [CollatzResearch.WordTrace]
  refine ⟨176231062774137955515212123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117487375182758637010141415 176231062774137955515212123)
  ·
    refine ⟨264346594161206933272818185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176231062774137955515212123 264346594161206933272818185)
    ·
      refine ⟨198259945620905199954613639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264346594161206933272818185 198259945620905199954613639)
      ·
        refine ⟨297389918431357799931920459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198259945620905199954613639 297389918431357799931920459)
        ·
          refine ⟨446084877647036699897880689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297389918431357799931920459 446084877647036699897880689)
          ·
            refine ⟨334563658235277524923410517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446084877647036699897880689 334563658235277524923410517)
            ·
              refine ⟨3920667869944658495196217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 334563658235277524923410517 3920667869944658495196217)
              ·
                refine ⟨2940500902458493871397163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3920667869944658495196217 2940500902458493871397163)
                ·
                  refine ⟨4410751353687740807095745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2940500902458493871397163 4410751353687740807095745)
                  ·
                    refine ⟨3308063515265805605321809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4410751353687740807095745 3308063515265805605321809)
                    ·
                      refine ⟨2481047636449354203991357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3308063515265805605321809 2481047636449354203991357)
                      ·
                        rfl

theorem cell23_4831823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 1, 2, 2].length) (baseStart_4831823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831823 prefixEnd_4831823 := by exact prefixLift 4831823
  have htrace : WordTrace (prefixWord ++ tailWord_4831823) baseStart_4831823 baseEnd_4831823 := by
    simpa [prefixWord, tailWord_4831823, baseEnd_4831823] using wordTrace_append hprefix tailTrace_4831823
  have hstable : (prefixWord ++ tailWord_4831823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831823).length < 2 ^ (prefixWord ++ tailWord_4831823).sum := by decide
  have hdescent : baseEnd_4831823 < baseStart_4831823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831825 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 2, 7]
def baseStart_4831825 : Nat := 118140960795 + 4831825 * 2 ^ 59
def prefixEnd_4831825 : Nat := 4983230072969 + 3 ^ 40 * 4831825 * 2
def baseEnd_4831825 : Nat := 827016221136887732055449

theorem tailTrace_4831825 : CollatzResearch.WordTrace tailWord_4831825 prefixEnd_4831825 827016221136887732055449 := by
  unfold tailWord_4831825
  simp only [CollatzResearch.WordTrace]
  refine ⟨176231135720130709856784929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117487423813420473237856619 176231135720130709856784929)
  ·
    refine ⟨132173351790098032392588697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176231135720130709856784929 132173351790098032392588697)
    ·
      refine ⟨99130013842573524294441523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132173351790098032392588697 99130013842573524294441523)
      ·
        refine ⟨148695020763860286441662285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99130013842573524294441523 148695020763860286441662285)
        ·
          refine ⟨55760632786447607415623357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148695020763860286441662285 55760632786447607415623357)
          ·
            refine ⟨20910237294917852780858759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55760632786447607415623357 20910237294917852780858759)
            ·
              refine ⟨31365355942376779171288139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20910237294917852780858759 31365355942376779171288139)
              ·
                refine ⟨47048033913565168756932209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31365355942376779171288139 47048033913565168756932209)
                ·
                  refine ⟨35286025435173876567699157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47048033913565168756932209 35286025435173876567699157)
                  ·
                    refine ⟨827016221136887732055449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35286025435173876567699157 827016221136887732055449)
                    ·
                      rfl

theorem cell23_4831825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_4831825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831825 prefixEnd_4831825 := by exact prefixLift 4831825
  have htrace : WordTrace (prefixWord ++ tailWord_4831825) baseStart_4831825 baseEnd_4831825 := by
    simpa [prefixWord, tailWord_4831825, baseEnd_4831825] using wordTrace_append hprefix tailTrace_4831825
  have hstable : (prefixWord ++ tailWord_4831825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831825).length < 2 ^ (prefixWord ++ tailWord_4831825).sum := by decide
  have hdescent : baseEnd_4831825 < baseStart_4831825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831849 : List Nat := [1, 2, 1, 1, 1, 4, 1, 6, 1, 3, 2]
def baseStart_4831849 : Nat := 118140960795 + 4831849 * 2 ^ 59
def prefixEnd_4831849 : Nat := 4983230072969 + 3 ^ 40 * 4831849 * 2
def baseEnd_4831849 : Nat := 2481060986946371102266237

theorem tailTrace_4831849 : CollatzResearch.WordTrace tailWord_4831849 prefixEnd_4831849 2481060986946371102266237 := by
  unfold tailWord_4831849
  simp only [CollatzResearch.WordTrace]
  refine ⟨176232011072043761955658601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117488007381362507970439067 176232011072043761955658601)
  ·
    refine ⟨132174008304032821466743951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176232011072043761955658601 132174008304032821466743951)
    ·
      refine ⟨198261012456049232200115927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132174008304032821466743951 198261012456049232200115927)
      ·
        refine ⟨297391518684073848300173891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198261012456049232200115927 297391518684073848300173891)
        ·
          refine ⟨446087278026110772450260837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297391518684073848300173891 446087278026110772450260837)
          ·
            refine ⟨83641364629895769834423907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 446087278026110772450260837 83641364629895769834423907)
            ·
              refine ⟨125462046944843654751635861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83641364629895769834423907 125462046944843654751635861)
              ·
                refine ⟨5881033450539546316482931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 125462046944843654751635861 5881033450539546316482931)
                ·
                  refine ⟨8821550175809319474724397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5881033450539546316482931 8821550175809319474724397)
                  ·
                    refine ⟨3308081315928494803021649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8821550175809319474724397 3308081315928494803021649)
                    ·
                      refine ⟨2481060986946371102266237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3308081315928494803021649 2481060986946371102266237)
                      ·
                        rfl

theorem cell23_4831849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 3, 2].length) (baseStart_4831849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831849 prefixEnd_4831849 := by exact prefixLift 4831849
  have htrace : WordTrace (prefixWord ++ tailWord_4831849) baseStart_4831849 baseEnd_4831849 := by
    simpa [prefixWord, tailWord_4831849, baseEnd_4831849] using wordTrace_append hprefix tailTrace_4831849
  have hstable : (prefixWord ++ tailWord_4831849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831849).length < 2 ^ (prefixWord ++ tailWord_4831849).sum := by decide
  have hdescent : baseEnd_4831849 < baseStart_4831849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831919 : List Nat := [1, 1, 2, 1, 2, 5, 3, 3, 5]
def baseStart_4831919 : Nat := 118140960795 + 4831919 * 2 ^ 59
def prefixEnd_4831919 : Nat := 4983230072969 + 3 ^ 40 * 4831919 * 2
def baseEnd_4831919 : Nat := 275677436732465092043435

theorem tailTrace_4831919 : CollatzResearch.WordTrace tailWord_4831919 prefixEnd_4831919 275677436732465092043435 := by
  unfold tailWord_4831919
  simp only [CollatzResearch.WordTrace]
  refine ⟨176234564181790163910706811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117489709454526775940471207 176234564181790163910706811)
  ·
    refine ⟨264351846272685245866060217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176234564181790163910706811 264351846272685245866060217)
    ·
      refine ⟨198263884704513934399545163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264351846272685245866060217 198263884704513934399545163)
      ·
        refine ⟨297395827056770901599317745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198263884704513934399545163 297395827056770901599317745)
        ·
          refine ⟨223046870292578176199488309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297395827056770901599317745 223046870292578176199488309)
          ·
            refine ⟨20910644089929204018702029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 223046870292578176199488309 20910644089929204018702029)
            ·
              refine ⟨7841491533723451507013261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20910644089929204018702029 7841491533723451507013261)
              ·
                refine ⟨2940559325146294315129973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7841491533723451507013261 2940559325146294315129973)
                ·
                  refine ⟨275677436732465092043435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2940559325146294315129973 275677436732465092043435)
                  ·
                    rfl

theorem cell23_4831919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 5].length) (baseStart_4831919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831919 prefixEnd_4831919 := by exact prefixLift 4831919
  have htrace : WordTrace (prefixWord ++ tailWord_4831919) baseStart_4831919 baseEnd_4831919 := by
    simpa [prefixWord, tailWord_4831919, baseEnd_4831919] using wordTrace_append hprefix tailTrace_4831919
  have hstable : (prefixWord ++ tailWord_4831919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831919).length < 2 ^ (prefixWord ++ tailWord_4831919).sum := by decide
  have hdescent : baseEnd_4831919 < baseStart_4831919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831936 : List Nat := [2, 1, 1, 2, 4, 3, 3, 2, 5]
def baseStart_4831936 : Nat := 118140960795 + 4831936 * 2 ^ 59
def prefixEnd_4831936 : Nat := 4983230072969 + 3 ^ 40 * 4831936 * 2
def baseEnd_4831936 : Nat := 275678406640368029097593

theorem tailTrace_4831936 : CollatzResearch.WordTrace tailWord_4831936 prefixEnd_4831936 275678406640368029097593 := by
  unfold tailWord_4831936
  simp only [CollatzResearch.WordTrace]
  refine ⟨88117592111364287907037831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117490122815152383876050441 88117592111364287907037831)
  ·
    refine ⟨132176388167046431860556747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88117592111364287907037831 132176388167046431860556747)
    ·
      refine ⟨198264582250569647790835121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132176388167046431860556747 198264582250569647790835121)
      ·
        refine ⟨148698436687927235843126341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198264582250569647790835121 148698436687927235843126341)
        ·
          refine ⟨27880956878986356720586189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148698436687927235843126341 27880956878986356720586189)
          ·
            refine ⟨10455358829619883770219821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27880956878986356720586189 10455358829619883770219821)
            ·
              refine ⟨3920759561107456413832433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10455358829619883770219821 3920759561107456413832433)
              ·
                refine ⟨2940569670830592310374325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3920759561107456413832433 2940569670830592310374325)
                ·
                  refine ⟨275678406640368029097593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2940569670830592310374325 275678406640368029097593)
                  ·
                    rfl

theorem cell23_4831936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 5].length) (baseStart_4831936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831936 prefixEnd_4831936 := by exact prefixLift 4831936
  have htrace : WordTrace (prefixWord ++ tailWord_4831936) baseStart_4831936 baseEnd_4831936 := by
    simpa [prefixWord, tailWord_4831936, baseEnd_4831936] using wordTrace_append hprefix tailTrace_4831936
  have hstable : (prefixWord ++ tailWord_4831936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831936).length < 2 ^ (prefixWord ++ tailWord_4831936).sum := by decide
  have hdescent : baseEnd_4831936 < baseStart_4831936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831969 : List Nat := [1, 2, 3, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_4831969 : Nat := 118140960795 + 4831969 * 2 ^ 59
def prefixEnd_4831969 : Nat := 4983230072969 + 3 ^ 40 * 4831969 * 2
def baseEnd_4831969 : Nat := 2481122604624910632765685

theorem tailTrace_4831969 : CollatzResearch.WordTrace tailWord_4831969 prefixEnd_4831969 2481122604624910632765685 := by
  unfold tailWord_4831969
  simp only [CollatzResearch.WordTrace]
  refine ⟨176236387831609022450026961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117490925221072681633351307 176236387831609022450026961)
  ·
    refine ⟨132177290873706766837520221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176236387831609022450026961 132177290873706766837520221)
    ·
      refine ⟨49566484077640037564070083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132177290873706766837520221 49566484077640037564070083)
      ·
        refine ⟨74349726116460056346105125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49566484077640037564070083 74349726116460056346105125)
        ·
          refine ⟨13940573646836260564894711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74349726116460056346105125 13940573646836260564894711)
          ·
            refine ⟨20910860470254390847342067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13940573646836260564894711 20910860470254390847342067)
            ·
              refine ⟨31366290705381586271013101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20910860470254390847342067 31366290705381586271013101)
              ·
                refine ⟨11762359014518094851629913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31366290705381586271013101 11762359014518094851629913)
                ·
                  refine ⟨8821769260888571138722435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11762359014518094851629913 8821769260888571138722435)
                  ·
                    refine ⟨13232653891332856708083653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8821769260888571138722435 13232653891332856708083653)
                    ·
                      refine ⟨2481122604624910632765685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13232653891332856708083653 2481122604624910632765685)
                      ·
                        rfl

theorem cell23_4831969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_4831969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4831969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4831969 prefixEnd_4831969 := by exact prefixLift 4831969
  have htrace : WordTrace (prefixWord ++ tailWord_4831969) baseStart_4831969 baseEnd_4831969 := by
    simpa [prefixWord, tailWord_4831969, baseEnd_4831969] using wordTrace_append hprefix tailTrace_4831969
  have hstable : (prefixWord ++ tailWord_4831969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831969).length < 2 ^ (prefixWord ++ tailWord_4831969).sum := by decide
  have hdescent : baseEnd_4831969 < baseStart_4831969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832023 : List Nat := [1, 1, 3, 4, 3, 2, 1, 1, 2, 2, 3]
def baseStart_4832023 : Nat := 118140960795 + 4832023 * 2 ^ 59
def prefixEnd_4832023 : Nat := 4983230072969 + 3 ^ 40 * 4832023 * 2
def baseEnd_4832023 : Nat := 2481150332580253421490437

theorem tailTrace_4832023 : CollatzResearch.WordTrace tailWord_4832023 prefixEnd_4832023 2481150332580253421490437 := by
  unfold tailWord_4832023
  simp only [CollatzResearch.WordTrace]
  refine ⟨176238357373413389672492723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117492238248942259781661815 176238357373413389672492723)
  ·
    refine ⟨264357536060120084508739085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176238357373413389672492723 264357536060120084508739085)
    ·
      refine ⟨99134076022545031690777157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264357536060120084508739085 99134076022545031690777157)
      ·
        refine ⟨18587639254227193442020717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99134076022545031690777157 18587639254227193442020717)
        ·
          refine ⟨6970364720335197540757769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18587639254227193442020717 6970364720335197540757769)
          ·
            refine ⟨5227773540251398155568327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6970364720335197540757769 5227773540251398155568327)
            ·
              refine ⟨7841660310377097233352491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5227773540251398155568327 7841660310377097233352491)
              ·
                refine ⟨11762490465565645850028737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7841660310377097233352491 11762490465565645850028737)
                ·
                  refine ⟨8821867849174234387521553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11762490465565645850028737 8821867849174234387521553)
                  ·
                    refine ⟨6616400886880675790641165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8821867849174234387521553 6616400886880675790641165)
                    ·
                      refine ⟨2481150332580253421490437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6616400886880675790641165 2481150332580253421490437)
                      ·
                        rfl

theorem cell23_4832023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_4832023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832023 prefixEnd_4832023 := by exact prefixLift 4832023
  have htrace : WordTrace (prefixWord ++ tailWord_4832023) baseStart_4832023 baseEnd_4832023 := by
    simpa [prefixWord, tailWord_4832023, baseEnd_4832023] using wordTrace_append hprefix tailTrace_4832023
  have hstable : (prefixWord ++ tailWord_4832023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832023).length < 2 ^ (prefixWord ++ tailWord_4832023).sum := by decide
  have hdescent : baseEnd_4832023 < baseStart_4832023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832053 : List Nat := [1, 3, 3, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_4832053 : Nat := 118140960795 + 4832053 * 2 ^ 59
def prefixEnd_4832053 : Nat := 4983230072969 + 3 ^ 40 * 4832053 * 2
def baseEnd_4832053 : Nat := 2481165736999888304115299

theorem tailTrace_4832053 : CollatzResearch.WordTrace tailWord_4832053 prefixEnd_4832053 2481165736999888304115299 := by
  unfold tailWord_4832053
  simp only [CollatzResearch.WordTrace]
  refine ⟨176239451563304704796084813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117492967708869803197389875 176239451563304704796084813)
  ·
    refine ⟨66089794336239264298531805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176239451563304704796084813 66089794336239264298531805)
    ·
      refine ⟨24783672876089724111949427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66089794336239264298531805 24783672876089724111949427)
      ·
        refine ⟨37175509314134586167924141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24783672876089724111949427 37175509314134586167924141)
        ·
          refine ⟨13940815992800469812971553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37175509314134586167924141 13940815992800469812971553)
          ·
            refine ⟨10455611994600352359728665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13940815992800469812971553 10455611994600352359728665)
            ·
              refine ⟨7841708995950264269796499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10455611994600352359728665 7841708995950264269796499)
              ·
                refine ⟨11762563493925396404694749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7841708995950264269796499 11762563493925396404694749)
                ·
                  refine ⟨4410961310222023651760531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11762563493925396404694749 4410961310222023651760531)
                  ·
                    refine ⟨6616441965333035477640797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4410961310222023651760531 6616441965333035477640797)
                    ·
                      refine ⟨2481165736999888304115299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6616441965333035477640797 2481165736999888304115299)
                      ·
                        rfl

theorem cell23_4832053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_4832053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832053 prefixEnd_4832053 := by exact prefixLift 4832053
  have htrace : WordTrace (prefixWord ++ tailWord_4832053) baseStart_4832053 baseEnd_4832053 := by
    simpa [prefixWord, tailWord_4832053, baseEnd_4832053] using wordTrace_append hprefix tailTrace_4832053
  have hstable : (prefixWord ++ tailWord_4832053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832053).length < 2 ^ (prefixWord ++ tailWord_4832053).sum := by decide
  have hdescent : baseEnd_4832053 < baseStart_4832053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832076 : List Nat := [2, 2, 1, 3, 3, 1, 1, 4, 1, 1, 4]
def baseStart_4832076 : Nat := 118140960795 + 4832076 * 2 ^ 59
def prefixEnd_4832076 : Nat := 4983230072969 + 3 ^ 40 * 4832076 * 2
def baseEnd_4832076 : Nat := 2481177547054941714127693

theorem tailTrace_4832076 : CollatzResearch.WordTrace tailWord_4832076 prefixEnd_4832076 2481177547054941714127693 := by
  unfold tailWord_4832076
  simp only [CollatzResearch.WordTrace]
  refine ⟨88120145221110689862086041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117493526961480919816114721 88120145221110689862086041)
  ·
    refine ⟨66090108915833017396564531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88120145221110689862086041 66090108915833017396564531)
    ·
      refine ⟨99135163373749526094846797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66090108915833017396564531 99135163373749526094846797)
      ·
        refine ⟨37175686265156072285567549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99135163373749526094846797 37175686265156072285567549)
        ·
          refine ⟨13940882349433527107087831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37175686265156072285567549 13940882349433527107087831)
          ·
            refine ⟨20911323524150290660631747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13940882349433527107087831 20911323524150290660631747)
            ·
              refine ⟨31366985286225435990947621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20911323524150290660631747 31366985286225435990947621)
              ·
                refine ⟨5881309741167269248302679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31366985286225435990947621 5881309741167269248302679)
                ·
                  refine ⟨8821964611750903872454019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5881309741167269248302679 8821964611750903872454019)
                  ·
                    refine ⟨13232946917626355808681029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8821964611750903872454019 13232946917626355808681029)
                    ·
                      refine ⟨2481177547054941714127693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13232946917626355808681029 2481177547054941714127693)
                      ·
                        rfl

theorem cell23_4832076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_4832076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832076 prefixEnd_4832076 := by exact prefixLift 4832076
  have htrace : WordTrace (prefixWord ++ tailWord_4832076) baseStart_4832076 baseEnd_4832076 := by
    simpa [prefixWord, tailWord_4832076, baseEnd_4832076] using wordTrace_append hprefix tailTrace_4832076
  have hstable : (prefixWord ++ tailWord_4832076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832076).length < 2 ^ (prefixWord ++ tailWord_4832076).sum := by decide
  have hdescent : baseEnd_4832076 < baseStart_4832076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832096 : List Nat := [2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 3]
def baseStart_4832096 : Nat := 118140960795 + 4832096 * 2 ^ 59
def prefixEnd_4832096 : Nat := 4983230072969 + 3 ^ 40 * 4832096 * 2
def baseEnd_4832096 : Nat := 2481187816668031635877601

theorem tailTrace_4832096 : CollatzResearch.WordTrace tailWord_4832096 prefixEnd_4832096 2481187816668031635877601 := by
  unfold tailWord_4832096
  simp only [CollatzResearch.WordTrace]
  refine ⟨88120509951074461569950071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117494013268099282093266761 88120509951074461569950071)
  ·
    refine ⟨132180764926611692354925107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88120509951074461569950071 132180764926611692354925107)
    ·
      refine ⟨198271147389917538532387661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132180764926611692354925107 198271147389917538532387661)
      ·
        refine ⟨74351680271219076949645373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198271147389917538532387661 74351680271219076949645373)
        ·
          refine ⟨27881880101707153856117015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74351680271219076949645373 27881880101707153856117015)
          ·
            refine ⟨41822820152560730784175523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27881880101707153856117015 41822820152560730784175523)
            ·
              refine ⟨62734230228841096176263285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41822820152560730784175523 62734230228841096176263285)
              ·
                refine ⟨5881334083953852766524683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62734230228841096176263285 5881334083953852766524683)
                ·
                  refine ⟨8822001125930779149787025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5881334083953852766524683 8822001125930779149787025)
                  ·
                    refine ⟨6616500844448084362340269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8822001125930779149787025 6616500844448084362340269)
                    ·
                      refine ⟨2481187816668031635877601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6616500844448084362340269 2481187816668031635877601)
                      ·
                        rfl

theorem cell23_4832096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_4832096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832096 prefixEnd_4832096 := by exact prefixLift 4832096
  have htrace : WordTrace (prefixWord ++ tailWord_4832096) baseStart_4832096 baseEnd_4832096 := by
    simpa [prefixWord, tailWord_4832096, baseEnd_4832096] using wordTrace_append hprefix tailTrace_4832096
  have hstable : (prefixWord ++ tailWord_4832096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832096).length < 2 ^ (prefixWord ++ tailWord_4832096).sum := by decide
  have hdescent : baseEnd_4832096 < baseStart_4832096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832099 : List Nat := [1, 1, 1, 5, 3, 3, 9]
def baseStart_4832099 : Nat := 118140960795 + 4832099 * 2 ^ 59
def prefixEnd_4832099 : Nat := 4983230072969 + 3 ^ 40 * 4832099 * 2
def baseEnd_4832099 : Nat := 30631967371728334865927

theorem tailTrace_4832099 : CollatzResearch.WordTrace tailWord_4832099 prefixEnd_4832099 30631967371728334865927 := by
  unfold tailWord_4832099
  simp only [CollatzResearch.WordTrace]
  refine ⟨176241129321138054652259351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117494086214092036434839567 176241129321138054652259351)
  ·
    refine ⟨264361693981707081978389027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176241129321138054652259351 264361693981707081978389027)
    ·
      refine ⟨396542540972560622967583541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264361693981707081978389027 396542540972560622967583541)
      ·
        refine ⟨37175863216177558403210957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 396542540972560622967583541 37175863216177558403210957)
        ·
          refine ⟨13940948706066584401204109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37175863216177558403210957 13940948706066584401204109)
          ·
            refine ⟨5227855764774969150451541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13940948706066584401204109 5227855764774969150451541)
            ·
              refine ⟨30631967371728334865927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5227855764774969150451541 30631967371728334865927)
              ·
                rfl

theorem cell23_4832099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 9].length) (baseStart_4832099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832099 prefixEnd_4832099 := by exact prefixLift 4832099
  have htrace : WordTrace (prefixWord ++ tailWord_4832099) baseStart_4832099 baseEnd_4832099 := by
    simpa [prefixWord, tailWord_4832099, baseEnd_4832099] using wordTrace_append hprefix tailTrace_4832099
  have hstable : (prefixWord ++ tailWord_4832099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832099).length < 2 ^ (prefixWord ++ tailWord_4832099).sum := by decide
  have hdescent : baseEnd_4832099 < baseStart_4832099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832169 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 1, 6, 3]
def baseStart_4832169 : Nat := 118140960795 + 4832169 * 2 ^ 59
def prefixEnd_4832169 : Nat := 4983230072969 + 3 ^ 40 * 4832169 * 2
def baseEnd_4832169 : Nat := 2481225300755809850264765

theorem tailTrace_4832169 : CollatzResearch.WordTrace tailWord_4832169 prefixEnd_4832169 2481225300755809850264765 := by
  unfold tailWord_4832169
  simp only [CollatzResearch.WordTrace]
  refine ⟨176243682430884456607307561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117495788287256304404871707 176243682430884456607307561)
  ·
    refine ⟨132182761823163342455480671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176243682430884456607307561 132182761823163342455480671)
    ·
      refine ⟨198274142734745013683221007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132182761823163342455480671 198274142734745013683221007)
      ·
        refine ⟨297411214102117520524831511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198274142734745013683221007 297411214102117520524831511)
        ·
          refine ⟨446116821153176280787247267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297411214102117520524831511 446116821153176280787247267)
          ·
            refine ⟨669175231729764421180870901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446116821153176280787247267 669175231729764421180870901)
            ·
              refine ⟨62735177974665414485706647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 669175231729764421180870901 62735177974665414485706647)
              ·
                refine ⟨94102766961998121728559971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62735177974665414485706647 94102766961998121728559971)
                ·
                  refine ⟨141154150442997182592839957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94102766961998121728559971 141154150442997182592839957)
                  ·
                    refine ⟨6616600802015492934039373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 141154150442997182592839957 6616600802015492934039373)
                    ·
                      refine ⟨2481225300755809850264765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6616600802015492934039373 2481225300755809850264765)
                      ·
                        rfl

theorem cell23_4832169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 6, 3].length) (baseStart_4832169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832169 prefixEnd_4832169 := by exact prefixLift 4832169
  have htrace : WordTrace (prefixWord ++ tailWord_4832169) baseStart_4832169 baseEnd_4832169 := by
    simpa [prefixWord, tailWord_4832169, baseEnd_4832169] using wordTrace_append hprefix tailTrace_4832169
  have hstable : (prefixWord ++ tailWord_4832169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832169).length < 2 ^ (prefixWord ++ tailWord_4832169).sum := by decide
  have hdescent : baseEnd_4832169 < baseStart_4832169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832198 : List Nat := [6, 1, 3, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_4832198 : Nat := 118140960795 + 4832198 * 2 ^ 59
def prefixEnd_4832198 : Nat := 4983230072969 + 3 ^ 40 * 4832198 * 2
def baseEnd_4832198 : Nat := 2481240191694790236802133

theorem tailTrace_4832198 : CollatzResearch.WordTrace tailWord_4832198 prefixEnd_4832198 2481240191694790236802133 := by
  unfold tailWord_4832198
  simp only [CollatzResearch.WordTrace]
  refine ⟨5507648129618106080003539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 117496493431852929706742165 5507648129618106080003539)
  ·
    refine ⟨8261472194427159120005309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5507648129618106080003539 8261472194427159120005309)
    ·
      refine ⟨3098052072910184670001991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8261472194427159120005309 3098052072910184670001991)
      ·
        refine ⟨4647078109365277005002987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3098052072910184670001991 4647078109365277005002987)
        ·
          refine ⟨6970617164047915507504481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4647078109365277005002987 6970617164047915507504481)
          ·
            refine ⟨5227962873035936630628361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6970617164047915507504481 5227962873035936630628361)
            ·
              refine ⟨3920972154776952472971271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5227962873035936630628361 3920972154776952472971271)
              ·
                refine ⟨5881458232165428709456907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3920972154776952472971271 5881458232165428709456907)
                ·
                  refine ⟨8822187348248143064185361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5881458232165428709456907 8822187348248143064185361)
                  ·
                    refine ⟨6616640511186107298139021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8822187348248143064185361 6616640511186107298139021)
                    ·
                      refine ⟨2481240191694790236802133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6616640511186107298139021 2481240191694790236802133)
                      ·
                        rfl

theorem cell23_4832198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_4832198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832198 prefixEnd_4832198 := by exact prefixLift 4832198
  have htrace : WordTrace (prefixWord ++ tailWord_4832198) baseStart_4832198 baseEnd_4832198 := by
    simpa [prefixWord, tailWord_4832198, baseEnd_4832198] using wordTrace_append hprefix tailTrace_4832198
  have hstable : (prefixWord ++ tailWord_4832198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832198).length < 2 ^ (prefixWord ++ tailWord_4832198).sum := by decide
  have hdescent : baseEnd_4832198 < baseStart_4832198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832216 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 2, 3, 3]
def baseStart_4832216 : Nat := 118140960795 + 4832216 * 2 ^ 59
def prefixEnd_4832216 : Nat := 4983230072969 + 3 ^ 40 * 4832216 * 2
def baseEnd_4832216 : Nat := 2481249434346571166377049

theorem tailTrace_4832216 : CollatzResearch.WordTrace tailWord_4832216 prefixEnd_4832216 2481249434346571166377049 := by
  unfold tailWord_4832216
  simp only [CollatzResearch.WordTrace]
  refine ⟨88122698330857091817134251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117496931107809455756179001 88122698330857091817134251)
  ·
    refine ⟨132184047496285637725701377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88122698330857091817134251 132184047496285637725701377)
    ·
      refine ⟨99138035622214228294276033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132184047496285637725701377 99138035622214228294276033)
      ·
        refine ⟨74353526716660671220707025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99138035622214228294276033 74353526716660671220707025)
        ·
          refine ⟨55765145037495503415530269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74353526716660671220707025 55765145037495503415530269)
          ·
            refine ⟨20911929389060813780823851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55765145037495503415530269 20911929389060813780823851)
            ·
              refine ⟨31367894083591220671235777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20911929389060813780823851 31367894083591220671235777)
              ·
                refine ⟨23525920562693415503426833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31367894083591220671235777 23525920562693415503426833)
                ·
                  refine ⟨17644440422020061627570125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23525920562693415503426833 17644440422020061627570125)
                  ·
                    refine ⟨6616665158257523110338797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17644440422020061627570125 6616665158257523110338797)
                    ·
                      refine ⟨2481249434346571166377049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6616665158257523110338797 2481249434346571166377049)
                      ·
                        rfl

theorem cell23_4832216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_4832216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832216 prefixEnd_4832216 := by exact prefixLift 4832216
  have htrace : WordTrace (prefixWord ++ tailWord_4832216) baseStart_4832216 baseEnd_4832216 := by
    simpa [prefixWord, tailWord_4832216, baseEnd_4832216] using wordTrace_append hprefix tailTrace_4832216
  have hstable : (prefixWord ++ tailWord_4832216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832216).length < 2 ^ (prefixWord ++ tailWord_4832216).sum := by decide
  have hdescent : baseEnd_4832216 < baseStart_4832216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832217 : List Nat := [1, 2, 1, 2, 5, 3, 1, 2, 2, 2, 2]
def baseStart_4832217 : Nat := 118140960795 + 4832217 * 2 ^ 59
def prefixEnd_4832217 : Nat := 4983230072969 + 3 ^ 40 * 4832217 * 2
def baseEnd_4832217 : Nat := 2481249947827225662464545

theorem tailTrace_4832217 : CollatzResearch.WordTrace tailWord_4832217 prefixEnd_4832217 2481249947827225662464545 := by
  unfold tailWord_4832217
  simp only [CollatzResearch.WordTrace]
  refine ⟨176245433134710560805054905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117496955423140373870036603 176245433134710560805054905)
  ·
    refine ⟨132184074851032920603791179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176245433134710560805054905 132184074851032920603791179)
    ·
      refine ⟨198276112276549380905686769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132184074851032920603791179 198276112276549380905686769)
      ·
        refine ⟨148707084207412035679265077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198276112276549380905686769 148707084207412035679265077)
        ·
          refine ⟨13941289144444878344931101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148707084207412035679265077 13941289144444878344931101)
          ·
            refine ⟨5227983429166829379349163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13941289144444878344931101 5227983429166829379349163)
            ·
              refine ⟨7841975143750244069023745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5227983429166829379349163 7841975143750244069023745)
              ·
                refine ⟨5881481357812683051767809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7841975143750244069023745 5881481357812683051767809)
                ·
                  refine ⟨4411111018359512288825857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5881481357812683051767809 4411111018359512288825857)
                  ·
                    refine ⟨3308333263769634216619393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4411111018359512288825857 3308333263769634216619393)
                    ·
                      refine ⟨2481249947827225662464545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3308333263769634216619393 2481249947827225662464545)
                      ·
                        rfl

theorem cell23_4832217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 2, 2].length) (baseStart_4832217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832217 prefixEnd_4832217 := by exact prefixLift 4832217
  have htrace : WordTrace (prefixWord ++ tailWord_4832217) baseStart_4832217 baseEnd_4832217 := by
    simpa [prefixWord, tailWord_4832217, baseEnd_4832217] using wordTrace_append hprefix tailTrace_4832217
  have hstable : (prefixWord ++ tailWord_4832217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832217).length < 2 ^ (prefixWord ++ tailWord_4832217).sum := by decide
  have hdescent : baseEnd_4832217 < baseStart_4832217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832249 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 2, 8]
def baseStart_4832249 : Nat := 118140960795 + 4832249 * 2 ^ 59
def prefixEnd_4832249 : Nat := 4983230072969 + 3 ^ 40 * 4832249 * 2
def baseEnd_4832249 : Nat := 827088793069389845754799

theorem tailTrace_4832249 : CollatzResearch.WordTrace tailWord_4832249 prefixEnd_4832249 827088793069389845754799 := by
  unfold tailWord_4832249
  simp only [CollatzResearch.WordTrace]
  refine ⟨176246600270594630270219801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117497733513729753513479867 176246600270594630270219801)
  ·
    refine ⟨132184950202945972702664851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176246600270594630270219801 132184950202945972702664851)
    ·
      refine ⟨198277425304418959053997277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132184950202945972702664851 198277425304418959053997277)
      ·
        refine ⟨74354034489157109645248979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198277425304418959053997277 74354034489157109645248979)
        ·
          refine ⟨111531051733735664467873469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74354034489157109645248979 111531051733735664467873469)
          ·
            refine ⟨41824144400150874175452551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111531051733735664467873469 41824144400150874175452551)
            ·
              refine ⟨62736216600226311263178827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41824144400150874175452551 62736216600226311263178827)
              ·
                refine ⟨94104324900339466894768241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62736216600226311263178827 94104324900339466894768241)
                ·
                  refine ⟨70578243675254600171076181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94104324900339466894768241 70578243675254600171076181)
                  ·
                    refine ⟨827088793069389845754799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70578243675254600171076181 827088793069389845754799)
                    ·
                      rfl

theorem cell23_4832249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 8].length) (baseStart_4832249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832249 prefixEnd_4832249 := by exact prefixLift 4832249
  have htrace : WordTrace (prefixWord ++ tailWord_4832249) baseStart_4832249 baseEnd_4832249 := by
    simpa [prefixWord, tailWord_4832249, baseEnd_4832249] using wordTrace_append hprefix tailTrace_4832249
  have hstable : (prefixWord ++ tailWord_4832249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832249).length < 2 ^ (prefixWord ++ tailWord_4832249).sum := by decide
  have hdescent : baseEnd_4832249 < baseStart_4832249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832259 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 5]
def baseStart_4832259 : Nat := 118140960795 + 4832259 * 2 ^ 59
def prefixEnd_4832259 : Nat := 4983230072969 + 3 ^ 40 * 4832259 * 2
def baseEnd_4832259 : Nat := 2481271514014714498139351

theorem tailTrace_4832259 : CollatzResearch.WordTrace tailWord_4832259 prefixEnd_4832259 2481271514014714498139351 := by
  unfold tailWord_4832259
  simp only [CollatzResearch.WordTrace]
  refine ⟨176246965000558401978083831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117497976667038934652055887 176246965000558401978083831)
  ·
    refine ⟨264370447500837602967125747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176246965000558401978083831 264370447500837602967125747)
    ·
      refine ⟨396555671251256404450688621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264370447500837602967125747 396555671251256404450688621)
      ·
        refine ⟨148708376719221151669008233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 396555671251256404450688621 148708376719221151669008233)
        ·
          refine ⟨111531282539415863751756175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148708376719221151669008233 111531282539415863751756175)
          ·
            refine ⟨167296923809123795627634263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111531282539415863751756175 167296923809123795627634263)
            ·
              refine ⟨250945385713685693441451395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167296923809123795627634263 250945385713685693441451395)
              ·
                refine ⟨376418078570528540162177093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250945385713685693441451395 376418078570528540162177093)
                ·
                  refine ⟨70578389731974101280408205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 376418078570528540162177093 70578389731974101280408205)
                  ·
                    refine ⟨26466896149490287980153077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70578389731974101280408205 26466896149490287980153077)
                    ·
                      refine ⟨2481271514014714498139351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26466896149490287980153077 2481271514014714498139351)
                      ·
                        rfl

theorem cell23_4832259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_4832259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832259 prefixEnd_4832259 := by exact prefixLift 4832259
  have htrace : WordTrace (prefixWord ++ tailWord_4832259) baseStart_4832259 baseEnd_4832259 := by
    simpa [prefixWord, tailWord_4832259, baseEnd_4832259] using wordTrace_append hprefix tailTrace_4832259
  have hstable : (prefixWord ++ tailWord_4832259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832259).length < 2 ^ (prefixWord ++ tailWord_4832259).sum := by decide
  have hdescent : baseEnd_4832259 < baseStart_4832259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832274 : List Nat := [3, 2, 5, 1, 2, 1, 1, 1, 7]
def baseStart_4832274 : Nat := 118140960795 + 4832274 * 2 ^ 59
def prefixEnd_4832274 : Nat := 4983230072969 + 3 ^ 40 * 4832274 * 2
def baseEnd_4832274 : Nat := 275697690691614659939087

theorem tailTrace_4832274 : CollatzResearch.WordTrace tailWord_4832274 prefixEnd_4832274 275697690691614659939087 := by
  unfold tailWord_4832274
  simp only [CollatzResearch.WordTrace]
  refine ⟨44061878023876014884969969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117498341397002706359919917 44061878023876014884969969)
  ·
    refine ⟨33046408517907011163727477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44061878023876014884969969 33046408517907011163727477)
    ·
      refine ⟨3098100798553782296599451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33046408517907011163727477 3098100798553782296599451)
      ·
        refine ⟨4647151197830673444899177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3098100798553782296599451 4647151197830673444899177)
        ·
          refine ⟨3485363398373005083674383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4647151197830673444899177 3485363398373005083674383)
          ·
            refine ⟨5228045097559507625511575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3485363398373005083674383 5228045097559507625511575)
            ·
              refine ⟨7842067646339261438267363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5228045097559507625511575 7842067646339261438267363)
              ·
                refine ⟨11763101469508892157401045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7842067646339261438267363 11763101469508892157401045)
                ·
                  refine ⟨275697690691614659939087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11763101469508892157401045 275697690691614659939087)
                  ·
                    rfl

theorem cell23_4832274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_4832274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832274 prefixEnd_4832274 := by exact prefixLift 4832274
  have htrace : WordTrace (prefixWord ++ tailWord_4832274) baseStart_4832274 baseEnd_4832274 := by
    simpa [prefixWord, tailWord_4832274, baseEnd_4832274] using wordTrace_append hprefix tailTrace_4832274
  have hstable : (prefixWord ++ tailWord_4832274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832274).length < 2 ^ (prefixWord ++ tailWord_4832274).sum := by decide
  have hdescent : baseEnd_4832274 < baseStart_4832274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832310 : List Nat := [5, 1, 2, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_4832310 : Nat := 118140960795 + 4832310 * 2 ^ 59
def prefixEnd_4832310 : Nat := 4983230072969 + 3 ^ 40 * 4832310 * 2
def baseEnd_4832310 : Nat := 2481297701528093798601617

theorem tailTrace_4832310 : CollatzResearch.WordTrace tailWord_4832310 prefixEnd_4832310 2481297701528093798601617 := by
  unfold tailWord_4832310
  simp only [CollatzResearch.WordTrace]
  refine ⟨11015551570210852355511899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117499216748915758458793589 11015551570210852355511899)
  ·
    refine ⟨16523327355316278533267849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11015551570210852355511899 16523327355316278533267849)
    ·
      refine ⟨12392495516487208899950887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16523327355316278533267849 12392495516487208899950887)
      ·
        refine ⟨18588743274730813349926331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12392495516487208899950887 18588743274730813349926331)
        ·
          refine ⟨27883114912096220024889497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18588743274730813349926331 27883114912096220024889497)
          ·
            refine ⟨20912336184072165018667123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27883114912096220024889497 20912336184072165018667123)
            ·
              refine ⟨31368504276108247528000685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20912336184072165018667123 31368504276108247528000685)
              ·
                refine ⟨11763189103540592823000257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31368504276108247528000685 11763189103540592823000257)
                ·
                  refine ⟨8822391827655444617250193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11763189103540592823000257 8822391827655444617250193)
                  ·
                    refine ⟨6616793870741583462937645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8822391827655444617250193 6616793870741583462937645)
                    ·
                      refine ⟨2481297701528093798601617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6616793870741583462937645 2481297701528093798601617)
                      ·
                        rfl

theorem cell23_4832310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_4832310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832310 prefixEnd_4832310 := by exact prefixLift 4832310
  have htrace : WordTrace (prefixWord ++ tailWord_4832310) baseStart_4832310 baseEnd_4832310 := by
    simpa [prefixWord, tailWord_4832310, baseEnd_4832310] using wordTrace_append hprefix tailTrace_4832310
  have hstable : (prefixWord ++ tailWord_4832310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832310).length < 2 ^ (prefixWord ++ tailWord_4832310).sum := by decide
  have hdescent : baseEnd_4832310 < baseStart_4832310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832374 : List Nat := [5, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3]
def baseStart_4832374 : Nat := 118140960795 + 4832374 * 2 ^ 59
def prefixEnd_4832374 : Nat := 4983230072969 + 3 ^ 40 * 4832374 * 2
def baseEnd_4832374 : Nat := 2481330564289981548201323

theorem tailTrace_4832374 : CollatzResearch.WordTrace tailWord_4832374 prefixEnd_4832374 2481330564289981548201323 := by
  unfold tailWord_4832374
  simp only [CollatzResearch.WordTrace]
  refine ⟨11015697462196361038657511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117500772930094517745680117 11015697462196361038657511)
  ·
    refine ⟨16523546193294541557986267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11015697462196361038657511 16523546193294541557986267)
    ·
      refine ⟨24785319289941812336979401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16523546193294541557986267 24785319289941812336979401)
      ·
        refine ⟨18588989467456359252734551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24785319289941812336979401 18588989467456359252734551)
        ·
          refine ⟨27883484201184538879101827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18588989467456359252734551 27883484201184538879101827)
          ·
            refine ⟨41825226301776808318652741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27883484201184538879101827 41825226301776808318652741)
            ·
              refine ⟨7842229931583151559747389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41825226301776808318652741 7842229931583151559747389)
              ·
                refine ⟨2940836224343681834905271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7842229931583151559747389 2940836224343681834905271)
                ·
                  refine ⟨4411254336515522752357907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2940836224343681834905271 4411254336515522752357907)
                  ·
                    refine ⟨6616881504773284128536861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4411254336515522752357907 6616881504773284128536861)
                    ·
                      refine ⟨2481330564289981548201323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6616881504773284128536861 2481330564289981548201323)
                      ·
                        rfl

theorem cell23_4832374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_4832374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832374 prefixEnd_4832374 := by exact prefixLift 4832374
  have htrace : WordTrace (prefixWord ++ tailWord_4832374) baseStart_4832374 baseEnd_4832374 := by
    simpa [prefixWord, tailWord_4832374, baseEnd_4832374] using wordTrace_append hprefix tailTrace_4832374
  have hstable : (prefixWord ++ tailWord_4832374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832374).length < 2 ^ (prefixWord ++ tailWord_4832374).sum := by decide
  have hdescent : baseEnd_4832374 < baseStart_4832374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832377 : List Nat := [1, 2, 1, 3, 5, 2, 2, 1, 1, 5]
def baseStart_4832377 : Nat := 118140960795 + 4832377 * 2 ^ 59
def prefixEnd_4832377 : Nat := 4983230072969 + 3 ^ 40 * 4832377 * 2
def baseEnd_4832377 : Nat := 827110701577315012154603

theorem tailTrace_4832377 : CollatzResearch.WordTrace tailWord_4832377 prefixEnd_4832377 827110701577315012154603 := by
  unfold tailWord_4832377
  simp only [CollatzResearch.WordTrace]
  refine ⟨176251268814130908130879385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117500845876087272087252923 176251268814130908130879385)
  ·
    refine ⟨132188451610598181098159539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176251268814130908130879385 132188451610598181098159539)
    ·
      refine ⟨198282677415897271647239309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132188451610598181098159539 198282677415897271647239309)
      ·
        refine ⟨74356004030961476867714741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198282677415897271647239309 74356004030961476867714741)
        ·
          refine ⟨6970875377902638456348257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74356004030961476867714741 6970875377902638456348257)
          ·
            refine ⟨5228156533426978842261193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6970875377902638456348257 5228156533426978842261193)
            ·
              refine ⟨3921117400070234131695895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5228156533426978842261193 3921117400070234131695895)
              ·
                refine ⟨5881676100105351197543843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3921117400070234131695895 5881676100105351197543843)
                ·
                  refine ⟨8822514150158026796315765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5881676100105351197543843 8822514150158026796315765)
                  ·
                    refine ⟨827110701577315012154603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8822514150158026796315765 827110701577315012154603)
                    ·
                      rfl

theorem cell23_4832377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 1, 5].length) (baseStart_4832377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832377 prefixEnd_4832377 := by exact prefixLift 4832377
  have htrace : WordTrace (prefixWord ++ tailWord_4832377) baseStart_4832377 baseEnd_4832377 := by
    simpa [prefixWord, tailWord_4832377, baseEnd_4832377] using wordTrace_append hprefix tailTrace_4832377
  have hstable : (prefixWord ++ tailWord_4832377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832377).length < 2 ^ (prefixWord ++ tailWord_4832377).sum := by decide
  have hdescent : baseEnd_4832377 < baseStart_4832377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832380 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 5, 2, 2]
def baseStart_4832380 : Nat := 118140960795 + 4832380 * 2 ^ 59
def prefixEnd_4832380 : Nat := 4983230072969 + 3 ^ 40 * 4832380 * 2
def baseEnd_4832380 : Nat := 2481333645173908524726295

theorem tailTrace_4832380 : CollatzResearch.WordTrace tailWord_4832380 prefixEnd_4832380 2481333645173908524726295 := by
  unfold tailWord_4832380
  simp only [CollatzResearch.WordTrace]
  refine ⟨88125689116560019821619297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117500918822080026428825729 88125689116560019821619297)
  ·
    refine ⟨66094266837420014866214473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88125689116560019821619297 66094266837420014866214473)
    ·
      refine ⟨49570700128065011149660855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66094266837420014866214473 49570700128065011149660855)
      ·
        refine ⟨74356050192097516724491283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49570700128065011149660855 74356050192097516724491283)
        ·
          refine ⟨111534075288146275086736925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74356050192097516724491283 111534075288146275086736925)
          ·
            refine ⟨41825278233054853157526347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111534075288146275086736925 41825278233054853157526347)
            ·
              refine ⟨62737917349582279736289521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41825278233054853157526347 62737917349582279736289521)
              ·
                refine ⟨47053438012186709802217141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62737917349582279736289521 47053438012186709802217141)
                ·
                  refine ⟨4411259813642504043957857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47053438012186709802217141 4411259813642504043957857)
                  ·
                    refine ⟨3308444860231878032968393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4411259813642504043957857 3308444860231878032968393)
                    ·
                      refine ⟨2481333645173908524726295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3308444860231878032968393 2481333645173908524726295)
                      ·
                        rfl

theorem cell23_4832380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_4832380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832380 prefixEnd_4832380 := by exact prefixLift 4832380
  have htrace : WordTrace (prefixWord ++ tailWord_4832380) baseStart_4832380 baseEnd_4832380 := by
    simpa [prefixWord, tailWord_4832380, baseEnd_4832380] using wordTrace_append hprefix tailTrace_4832380
  have hstable : (prefixWord ++ tailWord_4832380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832380).length < 2 ^ (prefixWord ++ tailWord_4832380).sum := by decide
  have hdescent : baseEnd_4832380 < baseStart_4832380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832407 : List Nat := [1, 1, 3, 3, 3, 2, 3, 1, 2, 4]
def baseStart_4832407 : Nat := 118140960795 + 4832407 * 2 ^ 59
def prefixEnd_4832407 : Nat := 4983230072969 + 3 ^ 40 * 4832407 * 2
def baseEnd_4832407 : Nat := 827115836383859973029557

theorem tailTrace_4832407 : CollatzResearch.WordTrace tailWord_4832407 prefixEnd_4832407 827115836383859973029557 := by
  unfold tailWord_4832407
  simp only [CollatzResearch.WordTrace]
  refine ⟨176252363004022223254471475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117501575336014815502980983 176252363004022223254471475)
  ·
    refine ⟨264378544506033334881707213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176252363004022223254471475 264378544506033334881707213)
    ·
      refine ⟨99141954189762500580640205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264378544506033334881707213 99141954189762500580640205)
      ·
        refine ⟨37178232821160937717740077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99141954189762500580640205 37178232821160937717740077)
        ·
          refine ⟨13941837307935351644152529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37178232821160937717740077 13941837307935351644152529)
          ·
            refine ⟨10456377980951513733114397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13941837307935351644152529 10456377980951513733114397)
            ·
              refine ⟨3921141742856817649917899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10456377980951513733114397 3921141742856817649917899)
              ·
                refine ⟨5881712614285226474876849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3921141742856817649917899 5881712614285226474876849)
                ·
                  refine ⟨4411284460713919856157637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5881712614285226474876849 4411284460713919856157637)
                  ·
                    refine ⟨827115836383859973029557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4411284460713919856157637 827115836383859973029557)
                    ·
                      rfl

theorem cell23_4832407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 2, 4].length) (baseStart_4832407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832407 prefixEnd_4832407 := by exact prefixLift 4832407
  have htrace : WordTrace (prefixWord ++ tailWord_4832407) baseStart_4832407 baseEnd_4832407 := by
    simpa [prefixWord, tailWord_4832407, baseEnd_4832407] using wordTrace_append hprefix tailTrace_4832407
  have hstable : (prefixWord ++ tailWord_4832407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832407).length < 2 ^ (prefixWord ++ tailWord_4832407).sum := by decide
  have hdescent : baseEnd_4832407 < baseStart_4832407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832410 : List Nat := [3, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4]
def baseStart_4832410 : Nat := 118140960795 + 4832410 * 2 ^ 59
def prefixEnd_4832410 : Nat := 4983230072969 + 3 ^ 40 * 4832410 * 2
def baseEnd_4832410 : Nat := 2481349049593543407351157

theorem tailTrace_4832410 : CollatzResearch.WordTrace tailWord_4832410 prefixEnd_4832410 2481349049593543407351157 := by
  unfold tailWord_4832410
  simp only [CollatzResearch.WordTrace]
  refine ⟨44063118105752838691707671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117501648282007569844553789 44063118105752838691707671)
  ·
    refine ⟨66094677158629258037561507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44063118105752838691707671 66094677158629258037561507)
    ·
      refine ⟨99142015737943887056342261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66094677158629258037561507 99142015737943887056342261)
      ·
        refine ⟨9294563975432239411532087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99142015737943887056342261 9294563975432239411532087)
        ·
          refine ⟨13941845963148359117298131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9294563975432239411532087 13941845963148359117298131)
          ·
            refine ⟨20912768944722538675947197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13941845963148359117298131 20912768944722538675947197)
            ·
              refine ⟨7842288354270952003480199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20912768944722538675947197 7842288354270952003480199)
              ·
                refine ⟨11763432531406428005220299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7842288354270952003480199 11763432531406428005220299)
                ·
                  refine ⟨17645148797109642007830449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11763432531406428005220299 17645148797109642007830449)
                  ·
                    refine ⟨13233861597832231505872837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17645148797109642007830449 13233861597832231505872837)
                    ·
                      refine ⟨2481349049593543407351157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13233861597832231505872837 2481349049593543407351157)
                      ·
                        rfl

theorem cell23_4832410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_4832410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832410 prefixEnd_4832410 := by exact prefixLift 4832410
  have htrace : WordTrace (prefixWord ++ tailWord_4832410) baseStart_4832410 baseEnd_4832410 := by
    simpa [prefixWord, tailWord_4832410, baseEnd_4832410] using wordTrace_append hprefix tailTrace_4832410
  have hstable : (prefixWord ++ tailWord_4832410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832410).length < 2 ^ (prefixWord ++ tailWord_4832410).sum := by decide
  have hdescent : baseEnd_4832410 < baseStart_4832410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832414 : List Nat := [4, 3, 1, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_4832414 : Nat := 118140960795 + 4832414 * 2 ^ 59
def prefixEnd_4832414 : Nat := 4983230072969 + 3 ^ 40 * 4832414 * 2
def baseEnd_4832414 : Nat := 2481351103516161391701139

theorem tailTrace_4832414 : CollatzResearch.WordTrace tailWord_4832414 prefixEnd_4832414 2481351103516161391701139 := by
  unfold tailWord_4832414
  simp only [CollatzResearch.WordTrace]
  refine ⟨22031577289374607931247037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117501745543331242299984197 22031577289374607931247037)
  ·
    refine ⟨8261841483515477974217639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22031577289374607931247037 8261841483515477974217639)
    ·
      refine ⟨12392762225273216961326459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8261841483515477974217639 12392762225273216961326459)
      ·
        refine ⟨18589143337909825441989689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12392762225273216961326459 18589143337909825441989689)
        ·
          refine ⟨13941857503432369081492267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18589143337909825441989689 13941857503432369081492267)
          ·
            refine ⟨20912786255148553622238401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13941857503432369081492267 20912786255148553622238401)
            ·
              refine ⟨15684589691361415216678801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20912786255148553622238401 15684589691361415216678801)
              ·
                refine ⟨11763442268521061412509101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15684589691361415216678801 11763442268521061412509101)
                ·
                  refine ⟨4411290850695398029690913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11763442268521061412509101 4411290850695398029690913)
                  ·
                    refine ⟨3308468138021548522268185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4411290850695398029690913 3308468138021548522268185)
                    ·
                      refine ⟨2481351103516161391701139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3308468138021548522268185 2481351103516161391701139)
                      ·
                        rfl

theorem cell23_4832414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_4832414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832414 prefixEnd_4832414 := by exact prefixLift 4832414
  have htrace : WordTrace (prefixWord ++ tailWord_4832414) baseStart_4832414 baseEnd_4832414 := by
    simpa [prefixWord, tailWord_4832414, baseEnd_4832414] using wordTrace_append hprefix tailTrace_4832414
  have hstable : (prefixWord ++ tailWord_4832414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832414).length < 2 ^ (prefixWord ++ tailWord_4832414).sum := by decide
  have hdescent : baseEnd_4832414 < baseStart_4832414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832420 : List Nat := [2, 3, 1, 2, 3, 3, 2, 7]
def baseStart_4832420 : Nat := 118140960795 + 4832420 * 2 ^ 59
def prefixEnd_4832420 : Nat := 4983230072969 + 3 ^ 40 * 4832420 * 2
def baseEnd_4832420 : Nat := 91902006829632902526893

theorem tailTrace_4832420 : CollatzResearch.WordTrace tailWord_4832420 prefixEnd_4832420 91902006829632902526893 := by
  unfold tailWord_4832420
  simp only [CollatzResearch.WordTrace]
  refine ⟨88126418576487563237347357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117501891435316750983129809 88126418576487563237347357)
  ·
    refine ⟨33047406966182836214005259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88126418576487563237347357 33047406966182836214005259)
    ·
      refine ⟨49571110449274254321007889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33047406966182836214005259 49571110449274254321007889)
      ·
        refine ⟨37178332836955690740755917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49571110449274254321007889 37178332836955690740755917)
        ·
          refine ⟨13941874813858384027783469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37178332836955690740755917 13941874813858384027783469)
          ·
            refine ⟨5228203055196894010418801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13941874813858384027783469 5228203055196894010418801)
            ·
              refine ⟨3921152291397670507814101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5228203055196894010418801 3921152291397670507814101)
              ·
                refine ⟨91902006829632902526893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3921152291397670507814101 91902006829632902526893)
                ·
                  rfl

theorem cell23_4832420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 7].length) (baseStart_4832420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832420 prefixEnd_4832420 := by exact prefixLift 4832420
  have htrace : WordTrace (prefixWord ++ tailWord_4832420) baseStart_4832420 baseEnd_4832420 := by
    simpa [prefixWord, tailWord_4832420, baseEnd_4832420] using wordTrace_append hprefix tailTrace_4832420
  have hstable : (prefixWord ++ tailWord_4832420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832420).length < 2 ^ (prefixWord ++ tailWord_4832420).sum := by decide
  have hdescent : baseEnd_4832420 < baseStart_4832420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832454 : List Nat := [6, 1, 2, 2, 1, 1, 2, 8]
def baseStart_4832454 : Nat := 118140960795 + 4832454 * 2 ^ 59
def prefixEnd_4832454 : Nat := 4983230072969 + 3 ^ 40 * 4832454 * 2
def baseEnd_4832454 : Nat := 91902653434901527229665

theorem tailTrace_4832454 : CollatzResearch.WordTrace tailWord_4832454 prefixEnd_4832454 91902653434901527229665 := by
  unfold tailWord_4832454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5507939913589123446294763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 117502718156567966854288277 5507939913589123446294763)
  ·
    refine ⟨8261909870383685169442145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5507939913589123446294763 8261909870383685169442145)
    ·
      refine ⟨6196432402787763877081609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8261909870383685169442145 6196432402787763877081609)
      ·
        refine ⟨4647324302090822907811207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6196432402787763877081609 4647324302090822907811207)
        ·
          refine ⟨6970986453136234361716811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4647324302090822907811207 6970986453136234361716811)
          ·
            refine ⟨10456479679704351542575217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6970986453136234361716811 10456479679704351542575217)
            ·
              refine ⟨7842359759778263656931413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10456479679704351542575217 7842359759778263656931413)
              ·
                refine ⟨91902653434901527229665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7842359759778263656931413 91902653434901527229665)
                ·
                  rfl

theorem cell23_4832454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_4832454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832454 prefixEnd_4832454 := by exact prefixLift 4832454
  have htrace : WordTrace (prefixWord ++ tailWord_4832454) baseStart_4832454 baseEnd_4832454 := by
    simpa [prefixWord, tailWord_4832454, baseEnd_4832454] using wordTrace_append hprefix tailTrace_4832454
  have hstable : (prefixWord ++ tailWord_4832454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832454).length < 2 ^ (prefixWord ++ tailWord_4832454).sum := by decide
  have hdescent : baseEnd_4832454 < baseStart_4832454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832503 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 3]
def baseStart_4832503 : Nat := 118140960795 + 4832503 * 2 ^ 59
def prefixEnd_4832503 : Nat := 4983230072969 + 3 ^ 40 * 4832503 * 2
def baseEnd_4832503 : Nat := 2481396803294411543488229

theorem tailTrace_4832503 : CollatzResearch.WordTrace tailWord_4832503 prefixEnd_4832503 2481396803294411543488229 := by
  unfold tailWord_4832503
  simp only [CollatzResearch.WordTrace]
  refine ⟨176255864411674431649966163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117503909607782954433310775 176255864411674431649966163)
  ·
    refine ⟨264383796617511647474949245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176255864411674431649966163 264383796617511647474949245)
    ·
      refine ⟨99143923731566867803105967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264383796617511647474949245 99143923731566867803105967)
      ·
        refine ⟨148715885597350301704658951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99143923731566867803105967 148715885597350301704658951)
        ·
          refine ⟨223073828396025452556988427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148715885597350301704658951 223073828396025452556988427)
          ·
            refine ⟨334610742594038178835482641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223073828396025452556988427 334610742594038178835482641)
            ·
              refine ⟨250958056945528634126611981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334610742594038178835482641 250958056945528634126611981)
              ·
                refine ⟨94109271354573237797479493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 250958056945528634126611981 94109271354573237797479493)
                ·
                  refine ⟨17645488378982482087027405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94109271354573237797479493 17645488378982482087027405)
                  ·
                    refine ⟨6617058142118430782635277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17645488378982482087027405 6617058142118430782635277)
                    ·
                      refine ⟨2481396803294411543488229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6617058142118430782635277 2481396803294411543488229)
                      ·
                        rfl

theorem cell23_4832503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_4832503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832503 prefixEnd_4832503 := by exact prefixLift 4832503
  have htrace : WordTrace (prefixWord ++ tailWord_4832503) baseStart_4832503 baseEnd_4832503 := by
    simpa [prefixWord, tailWord_4832503, baseEnd_4832503] using wordTrace_append hprefix tailTrace_4832503
  have hstable : (prefixWord ++ tailWord_4832503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832503).length < 2 ^ (prefixWord ++ tailWord_4832503).sum := by decide
  have hdescent : baseEnd_4832503 < baseStart_4832503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832540 : List Nat := [2, 2, 3, 1, 1, 1, 5, 1, 2, 5]
def baseStart_4832540 : Nat := 118140960795 + 4832540 * 2 ^ 59
def prefixEnd_4832540 : Nat := 4983230072969 + 3 ^ 40 * 4832540 * 2
def baseEnd_4832540 : Nat := 827138600692875966241853

theorem tailTrace_4832540 : CollatzResearch.WordTrace tailWord_4832540 prefixEnd_4832540 827138600692875966241853 := by
  unfold tailWord_4832540
  simp only [CollatzResearch.WordTrace]
  refine ⟨88128606956270193484531537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117504809275026924646042049 88128606956270193484531537)
  ·
    refine ⟨66096455217202645113398653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88128606956270193484531537 66096455217202645113398653)
    ·
      refine ⟨24786170706450991917524495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66096455217202645113398653 24786170706450991917524495)
      ·
        refine ⟨37179256059676487876286743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24786170706450991917524495 37179256059676487876286743)
        ·
          refine ⟨55768884089514731814430115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37179256059676487876286743 55768884089514731814430115)
          ·
            refine ⟨83653326134272097721645173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55768884089514731814430115 83653326134272097721645173)
            ·
              refine ⟨7842499325088009161404235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83653326134272097721645173 7842499325088009161404235)
              ·
                refine ⟨11763748987632013742106353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7842499325088009161404235 11763748987632013742106353)
                ·
                  refine ⟨8822811740724010306579765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11763748987632013742106353 8822811740724010306579765)
                  ·
                    refine ⟨827138600692875966241853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8822811740724010306579765 827138600692875966241853)
                    ·
                      rfl

theorem cell23_4832540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_4832540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832540 prefixEnd_4832540 := by exact prefixLift 4832540
  have htrace : WordTrace (prefixWord ++ tailWord_4832540) baseStart_4832540 baseEnd_4832540 := by
    simpa [prefixWord, tailWord_4832540, baseEnd_4832540] using wordTrace_append hprefix tailTrace_4832540
  have hstable : (prefixWord ++ tailWord_4832540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832540).length < 2 ^ (prefixWord ++ tailWord_4832540).sum := by decide
  have hdescent : baseEnd_4832540 < baseStart_4832540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832560 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 4, 4, 2]
def baseStart_4832560 : Nat := 118140960795 + 4832560 * 2 ^ 59
def prefixEnd_4832560 : Nat := 4983230072969 + 3 ^ 40 * 4832560 * 2
def baseEnd_4832560 : Nat := 2481426071691717820475467

theorem tailTrace_4832560 : CollatzResearch.WordTrace tailWord_4832560 prefixEnd_4832560 2481426071691717820475467 := by
  unfold tailWord_4832560
  simp only [CollatzResearch.WordTrace]
  refine ⟨88128971686233965192395567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117505295581645286923194089 88128971686233965192395567)
  ·
    refine ⟨132193457529350947788593351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88128971686233965192395567 132193457529350947788593351)
    ·
      refine ⟨198290186294026421682890027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132193457529350947788593351 198290186294026421682890027)
      ·
        refine ⟨297435279441039632524335041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198290186294026421682890027 297435279441039632524335041)
        ·
          refine ⟨223076459580779724393251281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297435279441039632524335041 223076459580779724393251281)
          ·
            refine ⟨167307344685584793294938461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223076459580779724393251281 167307344685584793294938461)
            ·
              refine ⟨62740254257094297485601923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167307344685584793294938461 62740254257094297485601923)
              ·
                refine ⟨94110381385641446228402885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62740254257094297485601923 94110381385641446228402885)
                ·
                  refine ⟨17645696509807771167825541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94110381385641446228402885 17645696509807771167825541)
                  ·
                    refine ⟨3308568095588957093967289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17645696509807771167825541 3308568095588957093967289)
                    ·
                      refine ⟨2481426071691717820475467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3308568095588957093967289 2481426071691717820475467)
                      ·
                        rfl

theorem cell23_4832560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4, 4, 2].length) (baseStart_4832560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832560 prefixEnd_4832560 := by exact prefixLift 4832560
  have htrace : WordTrace (prefixWord ++ tailWord_4832560) baseStart_4832560 baseEnd_4832560 := by
    simpa [prefixWord, tailWord_4832560, baseEnd_4832560] using wordTrace_append hprefix tailTrace_4832560
  have hstable : (prefixWord ++ tailWord_4832560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832560).length < 2 ^ (prefixWord ++ tailWord_4832560).sum := by decide
  have hdescent : baseEnd_4832560 < baseStart_4832560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832621 : List Nat := [1, 5, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_4832621 : Nat := 118140960795 + 4832621 * 2 ^ 59
def prefixEnd_4832621 : Nat := 4983230072969 + 3 ^ 40 * 4832621 * 2
def baseEnd_4832621 : Nat := 827152464670547360604229

theorem tailTrace_4832621 : CollatzResearch.WordTrace tailWord_4832621 prefixEnd_4832621 827152464670547360604229 := by
  unfold tailWord_4832621
  simp only [CollatzResearch.WordTrace]
  refine ⟨176260168225246937802761717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117506778816831291868507811 176260168225246937802761717)
  ·
    refine ⟨16524390771116900419008911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176260168225246937802761717 16524390771116900419008911)
    ·
      refine ⟨24786586156675350628513367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16524390771116900419008911 24786586156675350628513367)
      ·
        refine ⟨37179879235013025942770051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24786586156675350628513367 37179879235013025942770051)
        ·
          refine ⟨55769818852519538914155077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37179879235013025942770051 55769818852519538914155077)
          ·
            refine ⟨10456841034847413546404077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55769818852519538914155077 10456841034847413546404077)
            ·
              refine ⟨3921315388067780079901529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10456841034847413546404077 3921315388067780079901529)
              ·
                refine ⟨2940986541050835059926147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3921315388067780079901529 2940986541050835059926147)
                ·
                  refine ⟨4411479811576252589889221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2940986541050835059926147 4411479811576252589889221)
                  ·
                    refine ⟨827152464670547360604229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4411479811576252589889221 827152464670547360604229)
                    ·
                      rfl

theorem cell23_4832621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_4832621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832621 prefixEnd_4832621 := by exact prefixLift 4832621
  have htrace : WordTrace (prefixWord ++ tailWord_4832621) baseStart_4832621 baseEnd_4832621 := by
    simpa [prefixWord, tailWord_4832621, baseEnd_4832621] using wordTrace_append hprefix tailTrace_4832621
  have hstable : (prefixWord ++ tailWord_4832621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832621).length < 2 ^ (prefixWord ++ tailWord_4832621).sum := by decide
  have hdescent : baseEnd_4832621 < baseStart_4832621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832637 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 4, 3, 2]
def baseStart_4832637 : Nat := 118140960795 + 4832637 * 2 ^ 59
def prefixEnd_4832637 : Nat := 4983230072969 + 3 ^ 40 * 4832637 * 2
def baseEnd_4832637 : Nat := 2481465609702114019212613

theorem tailTrace_4832637 : CollatzResearch.WordTrace tailWord_4832637 prefixEnd_4832637 2481465609702114019212613 := by
  unfold tailWord_4832637
  simp only [CollatzResearch.WordTrace]
  refine ⟨176260751793188972535344165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117507167862125981690229443 176260751793188972535344165)
  ·
    refine ⟨33048890961222932350377031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176260751793188972535344165 33048890961222932350377031)
    ·
      refine ⟨49573336441834398525565547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33048890961222932350377031 49573336441834398525565547)
      ·
        refine ⟨74360004662751597788348321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49573336441834398525565547 74360004662751597788348321)
        ·
          refine ⟨55770003497063698341261241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74360004662751597788348321 55770003497063698341261241)
          ·
            refine ⟨41827502622797773755945931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55770003497063698341261241 41827502622797773755945931)
            ·
              refine ⟨62741253934196660633918897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41827502622797773755945931 62741253934196660633918897)
              ·
                refine ⟨47055940450647495475439173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62741253934196660633918897 47055940450647495475439173)
                ·
                  refine ⟨8822988834496405401644845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47055940450647495475439173 8822988834496405401644845)
                  ·
                    refine ⟨3308620812936152025616817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8822988834496405401644845 3308620812936152025616817)
                    ·
                      refine ⟨2481465609702114019212613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3308620812936152025616817 2481465609702114019212613)
                      ·
                        rfl

theorem cell23_4832637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_4832637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832637 prefixEnd_4832637 := by exact prefixLift 4832637
  have htrace : WordTrace (prefixWord ++ tailWord_4832637) baseStart_4832637 baseEnd_4832637 := by
    simpa [prefixWord, tailWord_4832637, baseEnd_4832637] using wordTrace_append hprefix tailTrace_4832637
  have hstable : (prefixWord ++ tailWord_4832637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832637).length < 2 ^ (prefixWord ++ tailWord_4832637).sum := by decide
  have hdescent : baseEnd_4832637 < baseStart_4832637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832647 : List Nat := [1, 1, 4, 2, 2, 2, 3, 2, 1, 5]
def baseStart_4832647 : Nat := 118140960795 + 4832647 * 2 ^ 59
def prefixEnd_4832647 : Nat := 4983230072969 + 3 ^ 40 * 4832647 * 2
def baseEnd_4832647 : Nat := 827156914836219660029189

theorem tailTrace_4832647 : CollatzResearch.WordTrace tailWord_4832647 prefixEnd_4832647 827156914836219660029189 := by
  unfold tailWord_4832647
  simp only [CollatzResearch.WordTrace]
  refine ⟨176261116523152744243208195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117507411015435162828805463 176261116523152744243208195)
  ·
    refine ⟨264391674784729116364812293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176261116523152744243208195 264391674784729116364812293)
    ·
      refine ⟨49573439022136709318402305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 264391674784729116364812293 49573439022136709318402305)
      ·
        refine ⟨37180079266602531988801729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49573439022136709318402305 37180079266602531988801729)
        ·
          refine ⟨27885059449951898991601297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37180079266602531988801729 27885059449951898991601297)
          ·
            refine ⟨20913794587463924243700973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27885059449951898991601297 20913794587463924243700973)
            ·
              refine ⟨7842672970298971591387865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20913794587463924243700973 7842672970298971591387865)
              ·
                refine ⟨5882004727724228693540899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7842672970298971591387865 5882004727724228693540899)
                ·
                  refine ⟨8823007091586343040311349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5882004727724228693540899 8823007091586343040311349)
                  ·
                    refine ⟨827156914836219660029189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8823007091586343040311349 827156914836219660029189)
                    ·
                      rfl

theorem cell23_4832647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_4832647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832647 prefixEnd_4832647 := by exact prefixLift 4832647
  have htrace : WordTrace (prefixWord ++ tailWord_4832647) baseStart_4832647 baseEnd_4832647 := by
    simpa [prefixWord, tailWord_4832647, baseEnd_4832647] using wordTrace_append hprefix tailTrace_4832647
  have hstable : (prefixWord ++ tailWord_4832647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832647).length < 2 ^ (prefixWord ++ tailWord_4832647).sum := by decide
  have hdescent : baseEnd_4832647 < baseStart_4832647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832673 : List Nat := [1, 2, 3, 17]
def baseStart_4832673 : Nat := 118140960795 + 4832673 * 2 ^ 59
def prefixEnd_4832673 : Nat := 4983230072969 + 3 ^ 40 * 4832673 * 2
def baseEnd_4832673 : Nat := 1134652078191895691981

theorem tailTrace_4832673 : CollatzResearch.WordTrace tailWord_4832673 prefixEnd_4832673 1134652078191895691981 := by
  unfold tailWord_4832673
  simp only [CollatzResearch.WordTrace]
  refine ⟨176262064821058550683654673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117508043214039033789103115 176262064821058550683654673)
  ·
    refine ⟨132196548615793913012741005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176262064821058550683654673 132196548615793913012741005)
    ·
      refine ⟨49573705730922717379777877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132196548615793913012741005 49573705730922717379777877)
      ·
        refine ⟨1134652078191895691981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 49573705730922717379777877 1134652078191895691981)
        ·
          rfl

theorem cell23_4832673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 17].length) (baseStart_4832673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832673 prefixEnd_4832673 := by exact prefixLift 4832673
  have htrace : WordTrace (prefixWord ++ tailWord_4832673) baseStart_4832673 baseEnd_4832673 := by
    simpa [prefixWord, tailWord_4832673, baseEnd_4832673] using wordTrace_append hprefix tailTrace_4832673
  have hstable : (prefixWord ++ tailWord_4832673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832673).length < 2 ^ (prefixWord ++ tailWord_4832673).sum := by decide
  have hdescent : baseEnd_4832673 < baseStart_4832673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832740 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_4832740 : Nat := 118140960795 + 4832740 * 2 ^ 59
def prefixEnd_4832740 : Nat := 4983230072969 + 3 ^ 40 * 4832740 * 2
def baseEnd_4832740 : Nat := 2481518498209527116224639

theorem tailTrace_4832740 : CollatzResearch.WordTrace tailWord_4832740 prefixEnd_4832740 2481518498209527116224639 := by
  unfold tailWord_4832740
  simp only [CollatzResearch.WordTrace]
  refine ⟨88132254255907910563171837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117509672341210547417562449 88132254255907910563171837)
  ·
    refine ⟨33049595345965466461189439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88132254255907910563171837 33049595345965466461189439)
    ·
      refine ⟨49574393018948199691784159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33049595345965466461189439 49574393018948199691784159)
      ·
        refine ⟨74361589528422299537676239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49574393018948199691784159 74361589528422299537676239)
        ·
          refine ⟨111542384292633449306514359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74361589528422299537676239 111542384292633449306514359)
          ·
            refine ⟨167313576438950173959771539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111542384292633449306514359 167313576438950173959771539)
            ·
              refine ⟨250970364658425260939657309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167313576438950173959771539 250970364658425260939657309)
              ·
                refine ⟨94113886746909472852371491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 250970364658425260939657309 94113886746909472852371491)
                ·
                  refine ⟨141170830120364209278557237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94113886746909472852371491 141170830120364209278557237)
                  ·
                    refine ⟨13234765323784144619864741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 141170830120364209278557237 13234765323784144619864741)
                    ·
                      refine ⟨2481518498209527116224639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13234765323784144619864741 2481518498209527116224639)
                      ·
                        rfl

theorem cell23_4832740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_4832740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832740 prefixEnd_4832740 := by exact prefixLift 4832740
  have htrace : WordTrace (prefixWord ++ tailWord_4832740) baseStart_4832740 baseEnd_4832740 := by
    simpa [prefixWord, tailWord_4832740, baseEnd_4832740] using wordTrace_append hprefix tailTrace_4832740
  have hstable : (prefixWord ++ tailWord_4832740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832740).length < 2 ^ (prefixWord ++ tailWord_4832740).sum := by decide
  have hdescent : baseEnd_4832740 < baseStart_4832740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832857 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 7, 4]
def baseStart_4832857 : Nat := 118140960795 + 4832857 * 2 ^ 59
def prefixEnd_4832857 : Nat := 4983230072969 + 3 ^ 40 * 4832857 * 2
def baseEnd_4832857 : Nat := 827192858482034386153867

theorem tailTrace_4832857 : CollatzResearch.WordTrace tailWord_4832857 prefixEnd_4832857 827192858482034386153867 := by
  unfold tailWord_4832857
  simp only [CollatzResearch.WordTrace]
  refine ⟨176268775852391950108352825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117512517234927966738901883 176268775852391950108352825)
  ·
    refine ⟨132201581889293962581264619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176268775852391950108352825 132201581889293962581264619)
    ·
      refine ⟨198302372833940943871896929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132201581889293962581264619 198302372833940943871896929)
      ·
        refine ⟨148726779625455707903922697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198302372833940943871896929 148726779625455707903922697)
        ·
          refine ⟨111545084719091780927942023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148726779625455707903922697 111545084719091780927942023)
          ·
            refine ⟨167317627078637671391913035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111545084719091780927942023 167317627078637671391913035)
            ·
              refine ⟨250976440617956507087869553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167317627078637671391913035 250976440617956507087869553)
              ·
                refine ⟨188232330463467380315902165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250976440617956507087869553 188232330463467380315902165)
                ·
                  refine ⟨4411695245237516726153957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 188232330463467380315902165 4411695245237516726153957)
                  ·
                    refine ⟨827192858482034386153867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4411695245237516726153957 827192858482034386153867)
                    ·
                      rfl

theorem cell23_4832857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 4].length) (baseStart_4832857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832857 prefixEnd_4832857 := by exact prefixLift 4832857
  have htrace : WordTrace (prefixWord ++ tailWord_4832857) baseStart_4832857 baseEnd_4832857 := by
    simpa [prefixWord, tailWord_4832857, baseEnd_4832857] using wordTrace_append hprefix tailTrace_4832857
  have hstable : (prefixWord ++ tailWord_4832857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832857).length < 2 ^ (prefixWord ++ tailWord_4832857).sum := by decide
  have hdescent : baseEnd_4832857 < baseStart_4832857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832874 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 5, 4]
def baseStart_4832874 : Nat := 118140960795 + 4832874 * 2 ^ 59
def prefixEnd_4832874 : Nat := 4983230072969 + 3 ^ 40 * 4832874 * 2
def baseEnd_4832874 : Nat := 827195768205743197316341

theorem tailTrace_4832874 : CollatzResearch.WordTrace tailWord_4832874 prefixEnd_4832874 827195768205743197316341 := by
  unfold tailWord_4832874
  simp only [CollatzResearch.WordTrace]
  refine ⟨44067348973332590502930419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117512930595553574674481117 44067348973332590502930419)
  ·
    refine ⟨66101023459998885754395629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44067348973332590502930419 66101023459998885754395629)
    ·
      refine ⟨24787883797499582157898361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66101023459998885754395629 24787883797499582157898361)
      ·
        refine ⟨18590912848124686618423771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24787883797499582157898361 18590912848124686618423771)
        ·
          refine ⟨27886369272187029927635657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18590912848124686618423771 27886369272187029927635657)
          ·
            refine ⟨20914776954140272445726743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27886369272187029927635657 20914776954140272445726743)
            ·
              refine ⟨31372165431210408668590115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20914776954140272445726743 31372165431210408668590115)
              ·
                refine ⟨47058248146815613002885173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31372165431210408668590115 47058248146815613002885173)
                ·
                  refine ⟨4411710763763963719020485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47058248146815613002885173 4411710763763963719020485)
                  ·
                    refine ⟨827195768205743197316341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4411710763763963719020485 827195768205743197316341)
                    ·
                      rfl

theorem cell23_4832874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_4832874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832874 prefixEnd_4832874 := by exact prefixLift 4832874
  have htrace : WordTrace (prefixWord ++ tailWord_4832874) baseStart_4832874 baseEnd_4832874 := by
    simpa [prefixWord, tailWord_4832874, baseEnd_4832874] using wordTrace_append hprefix tailTrace_4832874
  have hstable : (prefixWord ++ tailWord_4832874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832874).length < 2 ^ (prefixWord ++ tailWord_4832874).sum := by decide
  have hdescent : baseEnd_4832874 < baseStart_4832874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832878 : List Nat := [4, 1, 2, 2, 4, 1, 1, 1, 2, 5]
def baseStart_4832878 : Nat := 118140960795 + 4832878 * 2 ^ 59
def prefixEnd_4832878 : Nat := 4983230072969 + 3 ^ 40 * 4832878 * 2
def baseEnd_4832878 : Nat := 827196452846615858766335

theorem tailTrace_4832878 : CollatzResearch.WordTrace tailWord_4832878 prefixEnd_4832878 827196452846615858766335 := by
  unfold tailWord_4832878
  simp only [CollatzResearch.WordTrace]
  refine ⟨22033692723164483836858411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117513027856877247129911525 22033692723164483836858411)
  ·
    refine ⟨33050539084746725755287617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22033692723164483836858411 33050539084746725755287617)
    ·
      refine ⟨24787904313560044316465713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33050539084746725755287617 24787904313560044316465713)
      ·
        refine ⟨18590928235170033237349285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24787904313560044316465713 18590928235170033237349285)
        ·
          refine ⟨3485799044094381232002991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18590928235170033237349285 3485799044094381232002991)
          ·
            refine ⟨5228698566141571848004487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3485799044094381232002991 5228698566141571848004487)
            ·
              refine ⟨7843047849212357772006731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5228698566141571848004487 7843047849212357772006731)
              ·
                refine ⟨11764571773818536658010097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7843047849212357772006731 11764571773818536658010097)
                ·
                  refine ⟨8823428830363902493507573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11764571773818536658010097 8823428830363902493507573)
                  ·
                    refine ⟨827196452846615858766335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8823428830363902493507573 827196452846615858766335)
                    ·
                      rfl

theorem cell23_4832878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_4832878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832878 prefixEnd_4832878 := by exact prefixLift 4832878
  have htrace : WordTrace (prefixWord ++ tailWord_4832878) baseStart_4832878 baseEnd_4832878 := by
    simpa [prefixWord, tailWord_4832878, baseEnd_4832878] using wordTrace_append hprefix tailTrace_4832878
  have hstable : (prefixWord ++ tailWord_4832878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832878).length < 2 ^ (prefixWord ++ tailWord_4832878).sum := by decide
  have hdescent : baseEnd_4832878 < baseStart_4832878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832891 : List Nat := [1, 1, 1, 1, 1, 4, 6, 3, 1, 4]
def baseStart_4832891 : Nat := 118140960795 + 4832891 * 2 ^ 59
def prefixEnd_4832891 : Nat := 4983230072969 + 3 ^ 40 * 4832891 * 2
def baseEnd_4832891 : Nat := 827198677929452008478815

theorem tailTrace_4832891 : CollatzResearch.WordTrace tailWord_4832891 prefixEnd_4832891 827198677929452008478815 := by
  unfold tailWord_4832891
  simp only [CollatzResearch.WordTrace]
  refine ⟨176270015934268773915090527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117513343956179182610060351 176270015934268773915090527)
  ·
    refine ⟨264405023901403160872635791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176270015934268773915090527 264405023901403160872635791)
    ·
      refine ⟨396607535852104741308953687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264405023901403160872635791 396607535852104741308953687)
      ·
        refine ⟨594911303778157111963430531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396607535852104741308953687 594911303778157111963430531)
        ·
          refine ⟨892366955667235667945145797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 594911303778157111963430531 892366955667235667945145797)
          ·
            refine ⟨167318804187606687739714837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 892366955667235667945145797 167318804187606687739714837)
            ·
              refine ⟨7843068946294063487799133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 167318804187606687739714837 7843068946294063487799133)
              ·
                refine ⟨2941150854860273807924675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7843068946294063487799133 2941150854860273807924675)
                ·
                  refine ⟨4411726282290410711887013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2941150854860273807924675 4411726282290410711887013)
                  ·
                    refine ⟨827198677929452008478815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4411726282290410711887013 827198677929452008478815)
                    ·
                      rfl

theorem cell23_4832891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 1, 4].length) (baseStart_4832891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832891 prefixEnd_4832891 := by exact prefixLift 4832891
  have htrace : WordTrace (prefixWord ++ tailWord_4832891) baseStart_4832891 baseEnd_4832891 := by
    simpa [prefixWord, tailWord_4832891, baseEnd_4832891] using wordTrace_append hprefix tailTrace_4832891
  have hstable : (prefixWord ++ tailWord_4832891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832891).length < 2 ^ (prefixWord ++ tailWord_4832891).sum := by decide
  have hdescent : baseEnd_4832891 < baseStart_4832891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832917 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 5, 5]
def baseStart_4832917 : Nat := 118140960795 + 4832917 * 2 ^ 59
def prefixEnd_4832917 : Nat := 4983230072969 + 3 ^ 40 * 4832917 * 2
def baseEnd_4832917 : Nat := 827203128095124307903775

theorem tailTrace_4832917 : CollatzResearch.WordTrace tailWord_4832917 prefixEnd_4832917 827203128095124307903775 := by
  unfold tailWord_4832917
  simp only [CollatzResearch.WordTrace]
  refine ⟨176270964232174580355537005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117513976154783053570358003 176270964232174580355537005)
  ·
    refine ⟨66101611587065467633326377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176270964232174580355537005 66101611587065467633326377)
    ·
      refine ⟨49576208690299100724994783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66101611587065467633326377 49576208690299100724994783)
      ·
        refine ⟨74364313035448651087492175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49576208690299100724994783 74364313035448651087492175)
        ·
          refine ⟨111546469553172976631238263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74364313035448651087492175 111546469553172976631238263)
          ·
            refine ⟨167319704329759464946857395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111546469553172976631238263 167319704329759464946857395)
            ·
              refine ⟨250979556494639197420286093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167319704329759464946857395 250979556494639197420286093)
              ·
                refine ⟨94117333685489699032607285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 250979556494639197420286093 94117333685489699032607285)
                ·
                  refine ⟨8823500033014659284306933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94117333685489699032607285 8823500033014659284306933)
                  ·
                    refine ⟨827203128095124307903775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8823500033014659284306933 827203128095124307903775)
                    ·
                      rfl

theorem cell23_4832917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_4832917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832917 prefixEnd_4832917 := by exact prefixLift 4832917
  have htrace : WordTrace (prefixWord ++ tailWord_4832917) baseStart_4832917 baseEnd_4832917 := by
    simpa [prefixWord, tailWord_4832917, baseEnd_4832917] using wordTrace_append hprefix tailTrace_4832917
  have hstable : (prefixWord ++ tailWord_4832917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832917).length < 2 ^ (prefixWord ++ tailWord_4832917).sum := by decide
  have hdescent : baseEnd_4832917 < baseStart_4832917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832941 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_4832941 : Nat := 118140960795 + 4832941 * 2 ^ 59
def prefixEnd_4832941 : Nat := 4983230072969 + 3 ^ 40 * 4832941 * 2
def baseEnd_4832941 : Nat := 2481621707821080829811215

theorem tailTrace_4832941 : CollatzResearch.WordTrace tailWord_4832941 prefixEnd_4832941 2481621707821080829811215 := by
  unfold tailWord_4832941
  simp only [CollatzResearch.WordTrace]
  refine ⟨176271839584087632454410677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117514559722725088302940451 176271839584087632454410677)
  ·
    refine ⟨16525484961008215542601001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176271839584087632454410677 16525484961008215542601001)
    ·
      refine ⟨12394113720756161656950751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16525484961008215542601001 12394113720756161656950751)
      ·
        refine ⟨18591170581134242485426127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12394113720756161656950751 18591170581134242485426127)
        ·
          refine ⟨27886755871701363728139191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18591170581134242485426127 27886755871701363728139191)
          ·
            refine ⟨41830133807552045592208787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27886755871701363728139191 41830133807552045592208787)
            ·
              refine ⟨62745200711328068388313181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41830133807552045592208787 62745200711328068388313181)
              ·
                refine ⟨23529450266748025645617443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62745200711328068388313181 23529450266748025645617443)
                ·
                  refine ⟨35294175400122038468426165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23529450266748025645617443 35294175400122038468426165)
                  ·
                    refine ⟨3308828943761441106414953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35294175400122038468426165 3308828943761441106414953)
                    ·
                      refine ⟨2481621707821080829811215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3308828943761441106414953 2481621707821080829811215)
                      ·
                        rfl

theorem cell23_4832941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_4832941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832941 prefixEnd_4832941 := by exact prefixLift 4832941
  have htrace : WordTrace (prefixWord ++ tailWord_4832941) baseStart_4832941 baseEnd_4832941 := by
    simpa [prefixWord, tailWord_4832941, baseEnd_4832941] using wordTrace_append hprefix tailTrace_4832941
  have hstable : (prefixWord ++ tailWord_4832941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832941).length < 2 ^ (prefixWord ++ tailWord_4832941).sum := by decide
  have hdescent : baseEnd_4832941 < baseStart_4832941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832942 : List Nat := [4, 1, 4, 1, 2, 2, 1, 3, 1, 4]
def baseStart_4832942 : Nat := 118140960795 + 4832942 * 2 ^ 59
def prefixEnd_4832942 : Nat := 4983230072969 + 3 ^ 40 * 4832942 * 2
def baseEnd_4832942 : Nat := 827207407100578441966237

theorem tailTrace_4832942 : CollatzResearch.WordTrace tailWord_4832942 prefixEnd_4832942 827207407100578441966237 := by
  unfold tailWord_4832942
  simp only [CollatzResearch.WordTrace]
  refine ⟨22033984507135501203149635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117514584038056006416798053 22033984507135501203149635)
  ·
    refine ⟨33050976760703251804724453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22033984507135501203149635 33050976760703251804724453)
    ·
      refine ⟨6197058142631859713385835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33050976760703251804724453 6197058142631859713385835)
      ·
        refine ⟨9295587213947789570078753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6197058142631859713385835 9295587213947789570078753)
        ·
          refine ⟨6971690410460842177559065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9295587213947789570078753 6971690410460842177559065)
          ·
            refine ⟨5228767807845631633169299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6971690410460842177559065 5228767807845631633169299)
            ·
              refine ⟨7843151711768447449753949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5228767807845631633169299 7843151711768447449753949)
              ·
                refine ⟨2941181891913167793657731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7843151711768447449753949 2941181891913167793657731)
                ·
                  refine ⟨4411772837869751690486597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2941181891913167793657731 4411772837869751690486597)
                  ·
                    refine ⟨827207407100578441966237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4411772837869751690486597 827207407100578441966237)
                    ·
                      rfl

theorem cell23_4832942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_4832942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832942 prefixEnd_4832942 := by exact prefixLift 4832942
  have htrace : WordTrace (prefixWord ++ tailWord_4832942) baseStart_4832942 baseEnd_4832942 := by
    simpa [prefixWord, tailWord_4832942, baseEnd_4832942] using wordTrace_append hprefix tailTrace_4832942
  have hstable : (prefixWord ++ tailWord_4832942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832942).length < 2 ^ (prefixWord ++ tailWord_4832942).sum := by decide
  have hdescent : baseEnd_4832942 < baseStart_4832942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832947 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 3, 6]
def baseStart_4832947 : Nat := 118140960795 + 4832947 * 2 ^ 59
def prefixEnd_4832947 : Nat := 4983230072969 + 3 ^ 40 * 4832947 * 2
def baseEnd_4832947 : Nat := 827208262901669268778729

theorem tailTrace_4832947 : CollatzResearch.WordTrace tailWord_4832947 prefixEnd_4832947 827208262901669268778729 := by
  unfold tailWord_4832947
  simp only [CollatzResearch.WordTrace]
  refine ⟨176272058422065895479129095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117514705614710596986086063 176272058422065895479129095)
  ·
    refine ⟨264408087633098843218693643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176272058422065895479129095 264408087633098843218693643)
    ·
      refine ⟨396612131449648264828040465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264408087633098843218693643 396612131449648264828040465)
      ·
        refine ⟨297459098587236198621030349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 396612131449648264828040465 297459098587236198621030349)
        ·
          refine ⟨111547161970213574482886381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297459098587236198621030349 111547161970213574482886381)
          ·
            refine ⟨41830185738830090431082393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111547161970213574482886381 41830185738830090431082393)
            ·
              refine ⟨31372639304122567823311795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41830185738830090431082393 31372639304122567823311795)
              ·
                refine ⟨47058958956183851734967693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31372639304122567823311795 47058958956183851734967693)
                ·
                  refine ⟨17647109608568944400612885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47058958956183851734967693 17647109608568944400612885)
                  ·
                    refine ⟨827208262901669268778729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17647109608568944400612885 827208262901669268778729)
                    ·
                      rfl

theorem cell23_4832947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 6].length) (baseStart_4832947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832947 prefixEnd_4832947 := by exact prefixLift 4832947
  have htrace : WordTrace (prefixWord ++ tailWord_4832947) baseStart_4832947 baseEnd_4832947 := by
    simpa [prefixWord, tailWord_4832947, baseEnd_4832947] using wordTrace_append hprefix tailTrace_4832947
  have hstable : (prefixWord ++ tailWord_4832947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832947).length < 2 ^ (prefixWord ++ tailWord_4832947).sum := by decide
  have hdescent : baseEnd_4832947 < baseStart_4832947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832958 : List Nat := [4, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2]
def baseStart_4832958 : Nat := 118140960795 + 4832958 * 2 ^ 59
def prefixEnd_4832958 : Nat := 4983230072969 + 3 ^ 40 * 4832958 * 2
def baseEnd_4832958 : Nat := 2481630436992207263298637

theorem tailTrace_4832958 : CollatzResearch.WordTrace tailWord_4832958 prefixEnd_4832958 2481630436992207263298637 := by
  unfold tailWord_4832958
  simp only [CollatzResearch.WordTrace]
  refine ⟨22034057453128255544722441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117514973083350696238519685 22034057453128255544722441)
  ·
    refine ⟨16525543089846191658541831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22034057453128255544722441 16525543089846191658541831)
    ·
      refine ⟨24788314634769287487812747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16525543089846191658541831 24788314634769287487812747)
      ·
        refine ⟨37182471952153931231719121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24788314634769287487812747 37182471952153931231719121)
        ·
          refine ⟨27886853964115448423789341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37182471952153931231719121 27886853964115448423789341)
          ·
            refine ⟨10457570236543293158921003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27886853964115448423789341 10457570236543293158921003)
            ·
              refine ⟨15686355354814939738381505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10457570236543293158921003 15686355354814939738381505)
              ·
                refine ⟨11764766516111204803786129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15686355354814939738381505 11764766516111204803786129)
                ·
                  refine ⟨8823574887083403602839597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11764766516111204803786129 8823574887083403602839597)
                  ·
                    refine ⟨3308840582656276351064849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8823574887083403602839597 3308840582656276351064849)
                    ·
                      refine ⟨2481630436992207263298637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3308840582656276351064849 2481630436992207263298637)
                      ·
                        rfl

theorem cell23_4832958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_4832958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832958 prefixEnd_4832958 := by exact prefixLift 4832958
  have htrace : WordTrace (prefixWord ++ tailWord_4832958) baseStart_4832958 baseEnd_4832958 := by
    simpa [prefixWord, tailWord_4832958, baseEnd_4832958] using wordTrace_append hprefix tailTrace_4832958
  have hstable : (prefixWord ++ tailWord_4832958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832958).length < 2 ^ (prefixWord ++ tailWord_4832958).sum := by decide
  have hdescent : baseEnd_4832958 < baseStart_4832958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832967 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_4832967 : Nat := 118140960795 + 4832967 * 2 ^ 59
def prefixEnd_4832967 : Nat := 4983230072969 + 3 ^ 40 * 4832967 * 2
def baseEnd_4832967 : Nat := 2481635058318097728086095

theorem tailTrace_4832967 : CollatzResearch.WordTrace tailWord_4832967 prefixEnd_4832967 2481635058318097728086095 := by
  unfold tailWord_4832967
  simp only [CollatzResearch.WordTrace]
  refine ⟨176272787881993438894857155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117515191921328959263238103 176272787881993438894857155)
  ·
    refine ⟨264409181822990158342285733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176272787881993438894857155 264409181822990158342285733)
    ·
      refine ⟨49576721591810654689178575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 264409181822990158342285733 49576721591810654689178575)
      ·
        refine ⟨74365082387715982033767863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49576721591810654689178575 74365082387715982033767863)
        ·
          refine ⟨111547623581573973050651795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74365082387715982033767863 111547623581573973050651795)
          ·
            refine ⟨167321435372360959575977693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111547623581573973050651795 167321435372360959575977693)
            ·
              refine ⟨62745538264635359840991635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167321435372360959575977693 62745538264635359840991635)
              ·
                refine ⟨94118307396953039761487453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62745538264635359840991635 94118307396953039761487453)
                ·
                  refine ⟨35294365273857389910557795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94118307396953039761487453 35294365273857389910557795)
                  ·
                    refine ⟨52941547910786084865836693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35294365273857389910557795 52941547910786084865836693)
                    ·
                      refine ⟨2481635058318097728086095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52941547910786084865836693 2481635058318097728086095)
                      ·
                        rfl

theorem cell23_4832967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_4832967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832967 prefixEnd_4832967 := by exact prefixLift 4832967
  have htrace : WordTrace (prefixWord ++ tailWord_4832967) baseStart_4832967 baseEnd_4832967 := by
    simpa [prefixWord, tailWord_4832967, baseEnd_4832967] using wordTrace_append hprefix tailTrace_4832967
  have hstable : (prefixWord ++ tailWord_4832967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832967).length < 2 ^ (prefixWord ++ tailWord_4832967).sum := by decide
  have hdescent : baseEnd_4832967 < baseStart_4832967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832974 : List Nat := [4, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_4832974 : Nat := 118140960795 + 4832974 * 2 ^ 59
def prefixEnd_4832974 : Nat := 4983230072969 + 3 ^ 40 * 4832974 * 2
def baseEnd_4832974 : Nat := 2481638652682679200698563

theorem tailTrace_4832974 : CollatzResearch.WordTrace tailWord_4832974 prefixEnd_4832974 2481638652682679200698563 := by
  unfold tailWord_4832974
  simp only [CollatzResearch.WordTrace]
  refine ⟨22034130399121009886295247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117515362128645386060241317 22034130399121009886295247)
  ·
    refine ⟨33051195598681514829442871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22034130399121009886295247 33051195598681514829442871)
    ·
      refine ⟨49576793398022272244164307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33051195598681514829442871 49576793398022272244164307)
      ·
        refine ⟨74365190097033408366246461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49576793398022272244164307 74365190097033408366246461)
        ·
          refine ⟨27886946286387528137342423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74365190097033408366246461 27886946286387528137342423)
          ·
            refine ⟨41830419429581292206013635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27886946286387528137342423 41830419429581292206013635)
            ·
              refine ⟨62745629144371938309020453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41830419429581292206013635 62745629144371938309020453)
              ·
                refine ⟨11764805464569738432941335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62745629144371938309020453 11764805464569738432941335)
                ·
                  refine ⟨17647208196854607649412003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11764805464569738432941335 17647208196854607649412003)
                  ·
                    refine ⟨26470812295281911474118005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17647208196854607649412003 26470812295281911474118005)
                    ·
                      refine ⟨2481638652682679200698563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26470812295281911474118005 2481638652682679200698563)
                      ·
                        rfl

theorem cell23_4832974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_4832974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832974 prefixEnd_4832974 := by exact prefixLift 4832974
  have htrace : WordTrace (prefixWord ++ tailWord_4832974) baseStart_4832974 baseEnd_4832974 := by
    simpa [prefixWord, tailWord_4832974, baseEnd_4832974] using wordTrace_append hprefix tailTrace_4832974
  have hstable : (prefixWord ++ tailWord_4832974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832974).length < 2 ^ (prefixWord ++ tailWord_4832974).sum := by decide
  have hdescent : baseEnd_4832974 < baseStart_4832974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832977 : List Nat := [1, 2, 2, 1, 2, 4, 1, 10]
def baseStart_4832977 : Nat := 118140960795 + 4832977 * 2 ^ 59
def prefixEnd_4832977 : Nat := 4983230072969 + 3 ^ 40 * 4832977 * 2
def baseEnd_4832977 : Nat := 91912599745357136628187

theorem tailTrace_4832977 : CollatzResearch.WordTrace tailWord_4832977 prefixEnd_4832977 91912599745357136628187 := by
  unfold tailWord_4832977
  simp only [CollatzResearch.WordTrace]
  refine ⟨176273152611957210602721185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117515435074638140401814123 176273152611957210602721185)
  ·
    refine ⟨132204864458967907952040889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176273152611957210602721185 132204864458967907952040889)
    ·
      refine ⟨99153648344225930964030667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132204864458967907952040889 99153648344225930964030667)
      ·
        refine ⟨148730472516338896446046001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99153648344225930964030667 148730472516338896446046001)
        ·
          refine ⟨111547854387254172334534501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148730472516338896446046001 111547854387254172334534501)
          ·
            refine ⟨20915222697610157312725219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111547854387254172334534501 20915222697610157312725219)
            ·
              refine ⟨31372834046415235969087829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20915222697610157312725219 31372834046415235969087829)
              ·
                refine ⟨91912599745357136628187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31372834046415235969087829 91912599745357136628187)
                ·
                  rfl

theorem cell23_4832977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 10].length) (baseStart_4832977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832977 prefixEnd_4832977 := by exact prefixLift 4832977
  have htrace : WordTrace (prefixWord ++ tailWord_4832977) baseStart_4832977 baseEnd_4832977 := by
    simpa [prefixWord, tailWord_4832977, baseEnd_4832977] using wordTrace_append hprefix tailTrace_4832977
  have hstable : (prefixWord ++ tailWord_4832977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832977).length < 2 ^ (prefixWord ++ tailWord_4832977).sum := by decide
  have hdescent : baseEnd_4832977 < baseStart_4832977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832984 : List Nat := [2, 1, 2, 2, 3, 1, 2, 3, 1, 2, 4]
def baseStart_4832984 : Nat := 118140960795 + 4832984 * 2 ^ 59
def prefixEnd_4832984 : Nat := 4983230072969 + 3 ^ 40 * 4832984 * 2
def baseEnd_4832984 : Nat := 2481643787489224161573517

theorem tailTrace_4832984 : CollatzResearch.WordTrace tailWord_4832984 prefixEnd_4832984 2481643787489224161573517 := by
  unfold tailWord_4832984
  simp only [CollatzResearch.WordTrace]
  refine ⟨88136703961465925399113003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117515605281954567198817337 88136703961465925399113003)
  ·
    refine ⟨132205055942198888098669505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88136703961465925399113003 132205055942198888098669505)
    ·
      refine ⟨99153791956649166074002129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132205055942198888098669505 99153791956649166074002129)
      ·
        refine ⟨74365343967486874555501597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99153791956649166074002129 74365343967486874555501597)
        ·
          refine ⟨27887003987807577958313099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74365343967486874555501597 27887003987807577958313099)
          ·
            refine ⟨41830505981711366937469649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27887003987807577958313099 41830505981711366937469649)
            ·
              refine ⟨31372879486283525203102237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41830505981711366937469649 31372879486283525203102237)
              ·
                refine ⟨11764829807356321951163339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31372879486283525203102237 11764829807356321951163339)
                ·
                  refine ⟨17647244711034482926745009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11764829807356321951163339 17647244711034482926745009)
                  ·
                    refine ⟨13235433533275862195058757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17647244711034482926745009 13235433533275862195058757)
                    ·
                      refine ⟨2481643787489224161573517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13235433533275862195058757 2481643787489224161573517)
                      ·
                        rfl

theorem cell23_4832984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_4832984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832984 prefixEnd_4832984 := by exact prefixLift 4832984
  have htrace : WordTrace (prefixWord ++ tailWord_4832984) baseStart_4832984 baseEnd_4832984 := by
    simpa [prefixWord, tailWord_4832984, baseEnd_4832984] using wordTrace_append hprefix tailTrace_4832984
  have hstable : (prefixWord ++ tailWord_4832984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832984).length < 2 ^ (prefixWord ++ tailWord_4832984).sum := by decide
  have hdescent : baseEnd_4832984 < baseStart_4832984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4832988 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_4832988 : Nat := 118140960795 + 4832988 * 2 ^ 59
def prefixEnd_4832988 : Nat := 4983230072969 + 3 ^ 40 * 4832988 * 2
def baseEnd_4832988 : Nat := 2481645841411842145923499

theorem tailTrace_4832988 : CollatzResearch.WordTrace tailWord_4832988 prefixEnd_4832988 2481645841411842145923499 := by
  unfold tailWord_4832988
  simp only [CollatzResearch.WordTrace]
  refine ⟨88136776907458679740685809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117515702543278239654247745 88136776907458679740685809)
  ·
    refine ⟨66102582680594009805514357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88136776907458679740685809 66102582680594009805514357)
    ·
      refine ⟨6197117126305688419266971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66102582680594009805514357 6197117126305688419266971)
      ·
        refine ⟨9295675689458532628900457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6197117126305688419266971 9295675689458532628900457)
        ·
          refine ⟨6971756767093899471675343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9295675689458532628900457 6971756767093899471675343)
          ·
            refine ⟨10457635150640849207513015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6971756767093899471675343 10457635150640849207513015)
            ·
              refine ⟨15686452725961273811269523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10457635150640849207513015 15686452725961273811269523)
              ·
                refine ⟨23529679088941910716904285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15686452725961273811269523 23529679088941910716904285)
                ·
                  refine ⟨8823629658353216518839107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23529679088941910716904285 8823629658353216518839107)
                  ·
                    refine ⟨13235444487529824778258661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8823629658353216518839107 13235444487529824778258661)
                    ·
                      refine ⟨2481645841411842145923499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13235444487529824778258661 2481645841411842145923499)
                      ·
                        rfl

theorem cell23_4832988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_4832988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4832988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4832988 prefixEnd_4832988 := by exact prefixLift 4832988
  have htrace : WordTrace (prefixWord ++ tailWord_4832988) baseStart_4832988 baseEnd_4832988 := by
    simpa [prefixWord, tailWord_4832988, baseEnd_4832988] using wordTrace_append hprefix tailTrace_4832988
  have hstable : (prefixWord ++ tailWord_4832988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4832988).length < 2 ^ (prefixWord ++ tailWord_4832988).sum := by decide
  have hdescent : baseEnd_4832988 < baseStart_4832988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4832988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833004 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 3]
def baseStart_4833004 : Nat := 118140960795 + 4833004 * 2 ^ 59
def prefixEnd_4833004 : Nat := 4983230072969 + 3 ^ 40 * 4833004 * 2
def baseEnd_4833004 : Nat := 2481654057102314083323425

theorem tailTrace_4833004 : CollatzResearch.WordTrace tailWord_4833004 prefixEnd_4833004 2481654057102314083323425 := by
  unfold tailWord_4833004
  simp only [CollatzResearch.WordTrace]
  refine ⟨88137068691429697106977033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117516091588572929475969377 88137068691429697106977033)
  ·
    refine ⟨66102801518572272830232775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88137068691429697106977033 66102801518572272830232775)
    ·
      refine ⟨99154202277858409245349163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66102801518572272830232775 99154202277858409245349163)
      ·
        refine ⟨148731303416787613868023745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99154202277858409245349163 148731303416787613868023745)
        ·
          refine ⟨111548477562590710401017809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148731303416787613868023745 111548477562590710401017809)
          ·
            refine ⟨83661358171943032800763357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111548477562590710401017809 83661358171943032800763357)
            ·
              refine ⟨31373009314478637300286259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83661358171943032800763357 31373009314478637300286259)
              ·
                refine ⟨47059513971717955950429389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31373009314478637300286259 47059513971717955950429389)
                ·
                  refine ⟨17647317739394233481411021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47059513971717955950429389 17647317739394233481411021)
                  ·
                    refine ⟨6617744152272837555529133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17647317739394233481411021 6617744152272837555529133)
                    ·
                      refine ⟨2481654057102314083323425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6617744152272837555529133 2481654057102314083323425)
                      ·
                        rfl

theorem cell23_4833004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_4833004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833004 prefixEnd_4833004 := by exact prefixLift 4833004
  have htrace : WordTrace (prefixWord ++ tailWord_4833004) baseStart_4833004 baseEnd_4833004 := by
    simpa [prefixWord, tailWord_4833004, baseEnd_4833004] using wordTrace_append hprefix tailTrace_4833004
  have hstable : (prefixWord ++ tailWord_4833004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833004).length < 2 ^ (prefixWord ++ tailWord_4833004).sum := by decide
  have hdescent : baseEnd_4833004 < baseStart_4833004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833017 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 2, 3, 7]
def baseStart_4833017 : Nat := 118140960795 + 4833017 * 2 ^ 59
def prefixEnd_4833017 : Nat := 4983230072969 + 3 ^ 40 * 4833017 * 2
def baseEnd_4833017 : Nat := 2481660732350822532460865

theorem tailTrace_4833017 : CollatzResearch.WordTrace tailWord_4833017 prefixEnd_4833017 2481660732350822532460865 := by
  unfold tailWord_4833017
  simp only [CollatzResearch.WordTrace]
  refine ⟨176274611531812297434177305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117516407687874864956118203 176274611531812297434177305)
  ·
    refine ⟨132205958648859223075632979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176274611531812297434177305 132205958648859223075632979)
    ·
      refine ⟨198308937973288834613449469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132205958648859223075632979 198308937973288834613449469)
      ·
        refine ⟨74365851739983312980043551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198308937973288834613449469 74365851739983312980043551)
        ·
          refine ⟨111548777609974969470065327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74365851739983312980043551 111548777609974969470065327)
          ·
            refine ⟨167323166414962454205097991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111548777609974969470065327 167323166414962454205097991)
            ·
              refine ⟨250984749622443681307646987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167323166414962454205097991 250984749622443681307646987)
              ·
                refine ⟨376477124433665521961470481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250984749622443681307646987 376477124433665521961470481)
                ·
                  refine ⟨282357843325249141471102861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376477124433665521961470481 282357843325249141471102861)
                  ·
                    refine ⟨105884191246968428051663573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 282357843325249141471102861 105884191246968428051663573)
                    ·
                      refine ⟨2481660732350822532460865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105884191246968428051663573 2481660732350822532460865)
                      ·
                        rfl

theorem cell23_4833017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_4833017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833017 prefixEnd_4833017 := by exact prefixLift 4833017
  have htrace : WordTrace (prefixWord ++ tailWord_4833017) baseStart_4833017 baseEnd_4833017 := by
    simpa [prefixWord, tailWord_4833017, baseEnd_4833017] using wordTrace_append hprefix tailTrace_4833017
  have hstable : (prefixWord ++ tailWord_4833017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833017).length < 2 ^ (prefixWord ++ tailWord_4833017).sum := by decide
  have hdescent : baseEnd_4833017 < baseStart_4833017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833038 : List Nat := [4, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3]
def baseStart_4833038 : Nat := 118140960795 + 4833038 * 2 ^ 59
def prefixEnd_4833038 : Nat := 4983230072969 + 3 ^ 40 * 4833038 * 2
def baseEnd_4833038 : Nat := 2481671515444566950298269

theorem tailTrace_4833038 : CollatzResearch.WordTrace tailWord_4833038 prefixEnd_4833038 2481671515444566950298269 := by
  unfold tailWord_4833038
  simp only [CollatzResearch.WordTrace]
  refine ⟨22034422183092027252586471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117516918309824145347127845 22034422183092027252586471)
  ·
    refine ⟨33051633274638040878879707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22034422183092027252586471 33051633274638040878879707)
    ·
      refine ⟨49577449911957061318319561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33051633274638040878879707 49577449911957061318319561)
      ·
        refine ⟨37183087433967795988739671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49577449911957061318319561 37183087433967795988739671)
        ·
          refine ⟨55774631150951693983109507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37183087433967795988739671 55774631150951693983109507)
          ·
            refine ⟨83661946726427540974664261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55774631150951693983109507 83661946726427540974664261)
            ·
              refine ⟨15686615011205163932749549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83661946726427540974664261 15686615011205163932749549)
              ·
                refine ⟨5882480629201936474781081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15686615011205163932749549 5882480629201936474781081)
                ·
                  refine ⟨4411860471901452356085811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5882480629201936474781081 4411860471901452356085811)
                  ·
                    refine ⟨6617790707852178534128717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4411860471901452356085811 6617790707852178534128717)
                    ·
                      refine ⟨2481671515444566950298269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6617790707852178534128717 2481671515444566950298269)
                      ·
                        rfl

theorem cell23_4833038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_4833038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833038 prefixEnd_4833038 := by exact prefixLift 4833038
  have htrace : WordTrace (prefixWord ++ tailWord_4833038) baseStart_4833038 baseEnd_4833038 := by
    simpa [prefixWord, tailWord_4833038, baseEnd_4833038] using wordTrace_append hprefix tailTrace_4833038
  have hstable : (prefixWord ++ tailWord_4833038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833038).length < 2 ^ (prefixWord ++ tailWord_4833038).sum := by decide
  have hdescent : baseEnd_4833038 < baseStart_4833038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833084 : List Nat := [2, 2, 2, 2, 1, 1, 3, 3, 7]
def baseStart_4833084 : Nat := 118140960795 + 4833084 * 2 ^ 59
def prefixEnd_4833084 : Nat := 4983230072969 + 3 ^ 40 * 4833084 * 2
def baseEnd_4833084 : Nat := 275743903950519307813673

theorem tailTrace_4833084 : CollatzResearch.WordTrace tailWord_4833084 prefixEnd_4833084 275743903950519307813673 := by
  unfold tailWord_4833084
  simp only [CollatzResearch.WordTrace]
  refine ⟨88138527611284783938433153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117518036815046378584577537 88138527611284783938433153)
  ·
    refine ⟨66103895708463587953824865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88138527611284783938433153 66103895708463587953824865)
    ·
      refine ⟨49577921781347690965368649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66103895708463587953824865 49577921781347690965368649)
      ·
        refine ⟨37183441336010768224026487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49577921781347690965368649 37183441336010768224026487)
        ·
          refine ⟨55775162004016152336039731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37183441336010768224026487 55775162004016152336039731)
          ·
            refine ⟨83662743006024228504059597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55775162004016152336039731 83662743006024228504059597)
            ·
              refine ⟨31373528627259085689022349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83662743006024228504059597 31373528627259085689022349)
              ·
                refine ⟨11765073235222157133383381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31373528627259085689022349 11765073235222157133383381)
                ·
                  refine ⟨275743903950519307813673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11765073235222157133383381 275743903950519307813673)
                  ·
                    rfl

theorem cell23_4833084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 7].length) (baseStart_4833084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833084 prefixEnd_4833084 := by exact prefixLift 4833084
  have htrace : WordTrace (prefixWord ++ tailWord_4833084) baseStart_4833084 baseEnd_4833084 := by
    simpa [prefixWord, tailWord_4833084, baseEnd_4833084] using wordTrace_append hprefix tailTrace_4833084
  have hstable : (prefixWord ++ tailWord_4833084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833084).length < 2 ^ (prefixWord ++ tailWord_4833084).sum := by decide
  have hdescent : baseEnd_4833084 < baseStart_4833084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833114 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 1, 7]
def baseStart_4833114 : Nat := 118140960795 + 4833114 * 2 ^ 59
def prefixEnd_4833114 : Nat := 4983230072969 + 3 ^ 40 * 4833114 * 2
def baseEnd_4833114 : Nat := 827236846658102884315973

theorem tailTrace_4833114 : CollatzResearch.WordTrace tailWord_4833114 prefixEnd_4833114 827236846658102884315973 := by
  unfold tailWord_4833114
  simp only [CollatzResearch.WordTrace]
  refine ⟨44069537353115220750114599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117518766274973922000305597 44069537353115220750114599)
  ·
    refine ⟨66104306029672831125171899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44069537353115220750114599 66104306029672831125171899)
    ·
      refine ⟨99156459044509246687757849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66104306029672831125171899 99156459044509246687757849)
      ·
        refine ⟨74367344283381935015818387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99156459044509246687757849 74367344283381935015818387)
        ·
          refine ⟨111551016425072902523727581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74367344283381935015818387 111551016425072902523727581)
          ·
            refine ⟨41831631159402338446397843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111551016425072902523727581 41831631159402338446397843)
            ·
              refine ⟨62747446739103507669596765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41831631159402338446397843 62747446739103507669596765)
              ·
                refine ⟨23530292527163815376098787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62747446739103507669596765 23530292527163815376098787)
                ·
                  refine ⟨35295438790745723064148181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23530292527163815376098787 35295438790745723064148181)
                  ·
                    refine ⟨827236846658102884315973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35295438790745723064148181 827236846658102884315973)
                    ·
                      rfl

theorem cell23_4833114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_4833114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833114 prefixEnd_4833114 := by exact prefixLift 4833114
  have htrace : WordTrace (prefixWord ++ tailWord_4833114) baseStart_4833114 baseEnd_4833114 := by
    simpa [prefixWord, tailWord_4833114, baseEnd_4833114] using wordTrace_append hprefix tailTrace_4833114
  have hstable : (prefixWord ++ tailWord_4833114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833114).length < 2 ^ (prefixWord ++ tailWord_4833114).sum := by decide
  have hdescent : baseEnd_4833114 < baseStart_4833114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833141 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_4833141 : Nat := 118140960795 + 4833141 * 2 ^ 59
def prefixEnd_4833141 : Nat := 4983230072969 + 3 ^ 40 * 4833141 * 2
def baseEnd_4833141 : Nat := 2481724403951980047310295

theorem tailTrace_4833141 : CollatzResearch.WordTrace tailWord_4833141 prefixEnd_4833141 2481724403951980047310295 := by
  unfold tailWord_4833141
  simp only [CollatzResearch.WordTrace]
  refine ⟨176279134183363066611691277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117519422788908711074460851 176279134183363066611691277)
  ·
    refine ⟨66104675318761149979384229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176279134183363066611691277 66104675318761149979384229)
    ·
      refine ⟨12394626622267715621134543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66104675318761149979384229 12394626622267715621134543)
      ·
        refine ⟨18591939933401573431701815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12394626622267715621134543 18591939933401573431701815)
        ·
          refine ⟨27887909900102360147552723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18591939933401573431701815 27887909900102360147552723)
          ·
            refine ⟨41831864850153540221329085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27887909900102360147552723 41831864850153540221329085)
            ·
              refine ⟨15686949318807577582998407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41831864850153540221329085 15686949318807577582998407)
              ·
                refine ⟨23530423978211366374497611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15686949318807577582998407 23530423978211366374497611)
                ·
                  refine ⟨35295635967317049561746417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23530423978211366374497611 35295635967317049561746417)
                  ·
                    refine ⟨26471726975487787171309813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35295635967317049561746417 26471726975487787171309813)
                    ·
                      refine ⟨2481724403951980047310295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26471726975487787171309813 2481724403951980047310295)
                      ·
                        rfl

theorem cell23_4833141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_4833141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833141 prefixEnd_4833141 := by exact prefixLift 4833141
  have htrace : WordTrace (prefixWord ++ tailWord_4833141) baseStart_4833141 baseEnd_4833141 := by
    simpa [prefixWord, tailWord_4833141, baseEnd_4833141] using wordTrace_append hprefix tailTrace_4833141
  have hstable : (prefixWord ++ tailWord_4833141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833141).length < 2 ^ (prefixWord ++ tailWord_4833141).sum := by decide
  have hdescent : baseEnd_4833141 < baseStart_4833141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833151 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 1, 6, 2]
def baseStart_4833151 : Nat := 118140960795 + 4833151 * 2 ^ 59
def prefixEnd_4833151 : Nat := 4983230072969 + 3 ^ 40 * 4833151 * 2
def baseEnd_4833151 : Nat := 2481729538758525008185249

theorem tailTrace_4833151 : CollatzResearch.WordTrace tailWord_4833151 prefixEnd_4833151 2481729538758525008185249 := by
  unfold tailWord_4833151
  simp only [CollatzResearch.WordTrace]
  refine ⟨176279498913326838319555307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117519665942217892213036871 176279498913326838319555307)
  ·
    refine ⟨264419248369990257479332961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176279498913326838319555307 264419248369990257479332961)
    ·
      refine ⟨198314436277492693109499721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264419248369990257479332961 198314436277492693109499721)
      ·
        refine ⟨148735827208119519832124791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198314436277492693109499721 148735827208119519832124791)
        ·
          refine ⟨223103740812179279748187187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148735827208119519832124791 223103740812179279748187187)
          ·
            refine ⟨334655611218268919622280781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223103740812179279748187187 334655611218268919622280781)
            ·
              refine ⟨125495854206850844858355293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 334655611218268919622280781 125495854206850844858355293)
              ·
                refine ⟨47060945327569066821883235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125495854206850844858355293 47060945327569066821883235)
                ·
                  refine ⟨70591417991353600232824853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47060945327569066821883235 70591417991353600232824853)
                  ·
                    refine ⟨3308972718344700010913665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70591417991353600232824853 3308972718344700010913665)
                    ·
                      refine ⟨2481729538758525008185249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3308972718344700010913665 2481729538758525008185249)
                      ·
                        rfl

theorem cell23_4833151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 6, 2].length) (baseStart_4833151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833151 prefixEnd_4833151 := by exact prefixLift 4833151
  have htrace : WordTrace (prefixWord ++ tailWord_4833151) baseStart_4833151 baseEnd_4833151 := by
    simpa [prefixWord, tailWord_4833151, baseEnd_4833151] using wordTrace_append hprefix tailTrace_4833151
  have hstable : (prefixWord ++ tailWord_4833151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833151).length < 2 ^ (prefixWord ++ tailWord_4833151).sum := by decide
  have hdescent : baseEnd_4833151 < baseStart_4833151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833161 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 5, 4]
def baseStart_4833161 : Nat := 118140960795 + 4833161 * 2 ^ 59
def prefixEnd_4833161 : Nat := 4983230072969 + 3 ^ 40 * 4833161 * 2
def baseEnd_4833161 : Nat := 827244891188356656353401

theorem tailTrace_4833161 : CollatzResearch.WordTrace tailWord_4833161 prefixEnd_4833161 827244891188356656353401 := by
  unfold tailWord_4833161
  simp only [CollatzResearch.WordTrace]
  refine ⟨176279863643290610027419337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117519909095527073351612891 176279863643290610027419337)
  ·
    refine ⟨132209897732467957520564503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176279863643290610027419337 132209897732467957520564503)
    ·
      refine ⟨198314846598701936280846755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132209897732467957520564503 198314846598701936280846755)
      ·
        refine ⟨297472269898052904421270133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198314846598701936280846755 297472269898052904421270133)
        ·
          refine ⟨27888025302942459789494075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 297472269898052904421270133 27888025302942459789494075)
          ·
            refine ⟨41832037954413689684241113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27888025302942459789494075 41832037954413689684241113)
            ·
              refine ⟨31374028465810267263180835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41832037954413689684241113 31374028465810267263180835)
              ·
                refine ⟨47061042698715400894771253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31374028465810267263180835 47061042698715400894771253)
                ·
                  refine ⟨4411972753004568833884805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47061042698715400894771253 4411972753004568833884805)
                  ·
                    refine ⟨827244891188356656353401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4411972753004568833884805 827244891188356656353401)
                    ·
                      rfl

theorem cell23_4833161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 4].length) (baseStart_4833161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833161 prefixEnd_4833161 := by exact prefixLift 4833161
  have htrace : WordTrace (prefixWord ++ tailWord_4833161) baseStart_4833161 baseEnd_4833161 := by
    simpa [prefixWord, tailWord_4833161, baseEnd_4833161] using wordTrace_append hprefix tailTrace_4833161
  have hstable : (prefixWord ++ tailWord_4833161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833161).length < 2 ^ (prefixWord ++ tailWord_4833161).sum := by decide
  have hdescent : baseEnd_4833161 < baseStart_4833161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833164 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 1, 3, 6]
def baseStart_4833164 : Nat := 118140960795 + 4833164 * 2 ^ 59
def prefixEnd_4833164 : Nat := 4983230072969 + 3 ^ 40 * 4833164 * 2
def baseEnd_4833164 : Nat := 2481736214007033457322689

theorem tailTrace_4833164 : CollatzResearch.WordTrace tailWord_4833164 prefixEnd_4833164 2481736214007033457322689 := by
  unfold tailWord_4833164
  simp only [CollatzResearch.WordTrace]
  refine ⟨88139986531139870769889273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117519982041519827693185697 88139986531139870769889273)
  ·
    refine ⟨66104989898354903077416955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88139986531139870769889273 66104989898354903077416955)
    ·
      refine ⟨99157484847532354616125433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66104989898354903077416955 99157484847532354616125433)
      ·
        refine ⟨74368113635649265962094075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99157484847532354616125433 74368113635649265962094075)
        ·
          refine ⟨111552170453473898943141113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74368113635649265962094075 111552170453473898943141113)
          ·
            refine ⟨83664127840105424207355835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111552170453473898943141113 83664127840105424207355835)
            ·
              refine ⟨125496191760158136311033753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83664127840105424207355835 125496191760158136311033753)
              ·
                refine ⟨94122143820118602233275315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125496191760158136311033753 94122143820118602233275315)
                ·
                  refine ⟨141183215730177903349912973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94122143820118602233275315 141183215730177903349912973)
                  ·
                    refine ⟨52943705898816713756217365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 141183215730177903349912973 52943705898816713756217365)
                    ·
                      refine ⟨2481736214007033457322689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52943705898816713756217365 2481736214007033457322689)
                      ·
                        rfl

theorem cell23_4833164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_4833164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833164 prefixEnd_4833164 := by exact prefixLift 4833164
  have htrace : WordTrace (prefixWord ++ tailWord_4833164) baseStart_4833164 baseEnd_4833164 := by
    simpa [prefixWord, tailWord_4833164, baseEnd_4833164] using wordTrace_append hprefix tailTrace_4833164
  have hstable : (prefixWord ++ tailWord_4833164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833164).length < 2 ^ (prefixWord ++ tailWord_4833164).sum := by decide
  have hdescent : baseEnd_4833164 < baseStart_4833164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833188 : List Nat := [2, 3, 1, 2, 1, 3, 2, 2, 2, 2, 3]
def baseStart_4833188 : Nat := 118140960795 + 4833188 * 2 ^ 59
def prefixEnd_4833188 : Nat := 4983230072969 + 3 ^ 40 * 4833188 * 2
def baseEnd_4833188 : Nat := 2481748537542741363422579

theorem tailTrace_4833188 : CollatzResearch.WordTrace tailWord_4833188 prefixEnd_4833188 2481748537542741363422579 := by
  unfold tailWord_4833188
  simp only [CollatzResearch.WordTrace]
  refine ⟨88140424207096396819326109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117520565609461862425768145 88140424207096396819326109)
  ·
    refine ⟨33052659077661148807247291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88140424207096396819326109 33052659077661148807247291)
    ·
      refine ⟨49578988616491723210870937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33052659077661148807247291 49578988616491723210870937)
      ·
        refine ⟨37184241462368792408153203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49578988616491723210870937 37184241462368792408153203)
        ·
          refine ⟨55776362193553188612229805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37184241462368792408153203 55776362193553188612229805)
          ·
            refine ⟨20916135822582445729586177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55776362193553188612229805 20916135822582445729586177)
            ·
              refine ⟨15687101866936834297189633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20916135822582445729586177 15687101866936834297189633)
              ·
                refine ⟨11765326400202625722892225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15687101866936834297189633 11765326400202625722892225)
                ·
                  refine ⟨8823994800151969292169169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11765326400202625722892225 8823994800151969292169169)
                  ·
                    refine ⟨6617996100113976969126877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8823994800151969292169169 6617996100113976969126877)
                    ·
                      refine ⟨2481748537542741363422579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6617996100113976969126877 2481748537542741363422579)
                      ·
                        rfl

theorem cell23_4833188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_4833188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833188 prefixEnd_4833188 := by exact prefixLift 4833188
  have htrace : WordTrace (prefixWord ++ tailWord_4833188) baseStart_4833188 baseEnd_4833188 := by
    simpa [prefixWord, tailWord_4833188, baseEnd_4833188] using wordTrace_append hprefix tailTrace_4833188
  have hstable : (prefixWord ++ tailWord_4833188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833188).length < 2 ^ (prefixWord ++ tailWord_4833188).sum := by decide
  have hdescent : baseEnd_4833188 < baseStart_4833188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833275 : List Nat := [1, 1, 1, 1, 1, 3, 6, 2, 3, 2, 2]
def baseStart_4833275 : Nat := 118140960795 + 4833275 * 2 ^ 59
def prefixEnd_4833275 : Nat := 4983230072969 + 3 ^ 40 * 4833275 * 2
def baseEnd_4833275 : Nat := 2481793210359682523034679

theorem tailTrace_4833275 : CollatzResearch.WordTrace tailWord_4833275 prefixEnd_4833275 2481793210359682523034679 := by
  unfold tailWord_4833275
  simp only [CollatzResearch.WordTrace]
  refine ⟨176284021564877607497069279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117522681043251738331379519 176284021564877607497069279)
  ·
    refine ⟨264426032347316411245603919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176284021564877607497069279 264426032347316411245603919)
    ·
      refine ⟨396639048520974616868405879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264426032347316411245603919 396639048520974616868405879)
      ·
        refine ⟨594958572781461925302608819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396639048520974616868405879 594958572781461925302608819)
        ·
          refine ⟨892437859172192887953913229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 594958572781461925302608819 892437859172192887953913229)
          ·
            refine ⟨334664197189572332982717461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 892437859172192887953913229 334664197189572332982717461)
            ·
              refine ⟨15687384243261203108564881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 334664197189572332982717461 15687384243261203108564881)
              ·
                refine ⟨11765538182445902331423661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15687384243261203108564881 11765538182445902331423661)
                ·
                  refine ⟨4412076818417213374283873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11765538182445902331423661 4412076818417213374283873)
                  ·
                    refine ⟨3309057613812910030712905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4412076818417213374283873 3309057613812910030712905)
                    ·
                      refine ⟨2481793210359682523034679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3309057613812910030712905 2481793210359682523034679)
                      ·
                        rfl

theorem cell23_4833275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 2, 2].length) (baseStart_4833275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833275 prefixEnd_4833275 := by exact prefixLift 4833275
  have htrace : WordTrace (prefixWord ++ tailWord_4833275) baseStart_4833275 baseEnd_4833275 := by
    simpa [prefixWord, tailWord_4833275, baseEnd_4833275] using wordTrace_append hprefix tailTrace_4833275
  have hstable : (prefixWord ++ tailWord_4833275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833275).length < 2 ^ (prefixWord ++ tailWord_4833275).sum := by decide
  have hdescent : baseEnd_4833275 < baseStart_4833275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833281 : List Nat := [1, 2, 4, 1, 2, 1, 3, 9]
def baseStart_4833281 : Nat := 118140960795 + 4833281 * 2 ^ 59
def prefixEnd_4833281 : Nat := 4983230072969 + 3 ^ 40 * 4833281 * 2
def baseEnd_4833281 : Nat := 91918381157170722205913

theorem tailTrace_4833281 : CollatzResearch.WordTrace tailWord_4833281 prefixEnd_4833281 91918381157170722205913 := by
  unfold tailWord_4833281
  simp only [CollatzResearch.WordTrace]
  refine ⟨176284240402855870521787697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117522826935237247014525131 176284240402855870521787697)
  ·
    refine ⟨132213180302141902891340773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176284240402855870521787697 132213180302141902891340773)
    ·
      refine ⟨24789971306651606792126395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132213180302141902891340773 24789971306651606792126395)
      ·
        refine ⟨37184956959977410188189593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24789971306651606792126395 37184956959977410188189593)
        ·
          refine ⟨27888717719983057641142195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37184956959977410188189593 27888717719983057641142195)
          ·
            refine ⟨41833076579974586461713293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27888717719983057641142195 41833076579974586461713293)
            ·
              refine ⟨15687403717490469923142485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41833076579974586461713293 15687403717490469923142485)
              ·
                refine ⟨91918381157170722205913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15687403717490469923142485 91918381157170722205913)
                ·
                  rfl

theorem cell23_4833281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 9].length) (baseStart_4833281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833281 prefixEnd_4833281 := by exact prefixLift 4833281
  have htrace : WordTrace (prefixWord ++ tailWord_4833281) baseStart_4833281 baseEnd_4833281 := by
    simpa [prefixWord, tailWord_4833281, baseEnd_4833281] using wordTrace_append hprefix tailTrace_4833281
  have hstable : (prefixWord ++ tailWord_4833281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833281).length < 2 ^ (prefixWord ++ tailWord_4833281).sum := by decide
  have hdescent : baseEnd_4833281 < baseStart_4833281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833309 : List Nat := [1, 4, 2, 2, 2, 3, 1, 1, 3, 2, 2]
def baseStart_4833309 : Nat := 118140960795 + 4833309 * 2 ^ 59
def prefixEnd_4833309 : Nat := 4983230072969 + 3 ^ 40 * 4833309 * 2
def baseEnd_4833309 : Nat := 2481810668701935390009523

theorem tailTrace_4833309 : CollatzResearch.WordTrace tailWord_4833309 prefixEnd_4833309 2481810668701935390009523 := by
  unfold tailWord_4833309
  simp only [CollatzResearch.WordTrace]
  refine ⟨176285261646754431303806981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117523507764502954202537987 176285261646754431303806981)
  ·
    refine ⟨33053486558766455869463809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176285261646754431303806981 33053486558766455869463809)
    ·
      refine ⟨24790114919074841902097857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33053486558766455869463809 24790114919074841902097857)
      ·
        refine ⟨18592586189306131426573393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24790114919074841902097857 18592586189306131426573393)
        ·
          refine ⟨13944439641979598569930045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18592586189306131426573393 13944439641979598569930045)
          ·
            refine ⟨5229164865742349463723767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13944439641979598569930045 5229164865742349463723767)
            ·
              refine ⟨7843747298613524195585651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5229164865742349463723767 7843747298613524195585651)
              ·
                refine ⟨11765620947920286293378477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7843747298613524195585651 11765620947920286293378477)
                ·
                  refine ⟨4412107855470107360016929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11765620947920286293378477 4412107855470107360016929)
                  ·
                    refine ⟨3309080891602580520012697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4412107855470107360016929 3309080891602580520012697)
                    ·
                      refine ⟨2481810668701935390009523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3309080891602580520012697 2481810668701935390009523)
                      ·
                        rfl

theorem cell23_4833309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_4833309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833309 prefixEnd_4833309 := by exact prefixLift 4833309
  have htrace : WordTrace (prefixWord ++ tailWord_4833309) baseStart_4833309 baseEnd_4833309 := by
    simpa [prefixWord, tailWord_4833309, baseEnd_4833309] using wordTrace_append hprefix tailTrace_4833309
  have hstable : (prefixWord ++ tailWord_4833309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833309).length < 2 ^ (prefixWord ++ tailWord_4833309).sum := by decide
  have hdescent : baseEnd_4833309 < baseStart_4833309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833311 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 2, 7]
def baseStart_4833311 : Nat := 118140960795 + 4833311 * 2 ^ 59
def prefixEnd_4833311 : Nat := 4983230072969 + 3 ^ 40 * 4833311 * 2
def baseEnd_4833311 : Nat := 827270565221081460728171

theorem tailTrace_4833311 : CollatzResearch.WordTrace tailWord_4833311 prefixEnd_4833311 827270565221081460728171 := by
  unfold tailWord_4833311
  simp only [CollatzResearch.WordTrace]
  refine ⟨176285334592747185645379787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117523556395164790430253191 176285334592747185645379787)
  ·
    refine ⟨264428001889120778468069681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176285334592747185645379787 264428001889120778468069681)
    ·
      refine ⟨198321001416840583851052261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264428001889120778468069681 198321001416840583851052261)
      ·
        refine ⟨37185187765657609472072299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198321001416840583851052261 37185187765657609472072299)
        ·
          refine ⟨55777781648486414208108449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37185187765657609472072299 55777781648486414208108449)
          ·
            refine ⟨41833336236364810656081337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55777781648486414208108449 41833336236364810656081337)
            ·
              refine ⟨31375002177273607992061003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41833336236364810656081337 31375002177273607992061003)
              ·
                refine ⟨47062503265910411988091505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31375002177273607992061003 47062503265910411988091505)
                ·
                  refine ⟨35296877449432808991068629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47062503265910411988091505 35296877449432808991068629)
                  ·
                    refine ⟨827270565221081460728171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35296877449432808991068629 827270565221081460728171)
                    ·
                      rfl

theorem cell23_4833311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 7].length) (baseStart_4833311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833311 prefixEnd_4833311 := by exact prefixLift 4833311
  have htrace : WordTrace (prefixWord ++ tailWord_4833311) baseStart_4833311 baseEnd_4833311 := by
    simpa [prefixWord, tailWord_4833311, baseEnd_4833311] using wordTrace_append hprefix tailTrace_4833311
  have hstable : (prefixWord ++ tailWord_4833311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833311).length < 2 ^ (prefixWord ++ tailWord_4833311).sum := by decide
  have hdescent : baseEnd_4833311 < baseStart_4833311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833342 : List Nat := [4, 2, 1, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_4833342 : Nat := 118140960795 + 4833342 * 2 ^ 59
def prefixEnd_4833342 : Nat := 4983230072969 + 3 ^ 40 * 4833342 * 2
def baseEnd_4833342 : Nat := 2481827613563533760896871

theorem tailTrace_4833342 : CollatzResearch.WordTrace tailWord_4833342 prefixEnd_4833342 2481827613563533760896871 := by
  unfold tailWord_4833342
  simp only [CollatzResearch.WordTrace]
  refine ⟨22035808156954359742469785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117524310170423251959838853 22035808156954359742469785)
  ·
    refine ⟨16526856117715769806852339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22035808156954359742469785 16526856117715769806852339)
    ·
      refine ⟨24790284176573654710278509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16526856117715769806852339 24790284176573654710278509)
      ·
        refine ⟨9296356566215120516354441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24790284176573654710278509 9296356566215120516354441)
        ·
          refine ⟨6972267424661340387265831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9296356566215120516354441 6972267424661340387265831)
          ·
            refine ⟨10458401136992010580898747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6972267424661340387265831 10458401136992010580898747)
            ·
              refine ⟨15687601705488015871348121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10458401136992010580898747 15687601705488015871348121)
              ·
                refine ⟨11765701279116011903511091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15687601705488015871348121 11765701279116011903511091)
                ·
                  refine ⟨17648551918674017855266637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11765701279116011903511091 17648551918674017855266637)
                  ·
                    refine ⟨6618206969502756695724989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17648551918674017855266637 6618206969502756695724989)
                    ·
                      refine ⟨2481827613563533760896871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6618206969502756695724989 2481827613563533760896871)
                      ·
                        rfl

theorem cell23_4833342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_4833342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833342 prefixEnd_4833342 := by exact prefixLift 4833342
  have htrace : WordTrace (prefixWord ++ tailWord_4833342) baseStart_4833342 baseEnd_4833342 := by
    simpa [prefixWord, tailWord_4833342, baseEnd_4833342] using wordTrace_append hprefix tailTrace_4833342
  have hstable : (prefixWord ++ tailWord_4833342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833342).length < 2 ^ (prefixWord ++ tailWord_4833342).sum := by decide
  have hdescent : baseEnd_4833342 < baseStart_4833342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833361 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 2, 3, 6]
def baseStart_4833361 : Nat := 118140960795 + 4833361 * 2 ^ 59
def prefixEnd_4833361 : Nat := 4983230072969 + 3 ^ 40 * 4833361 * 2
def baseEnd_4833361 : Nat := 2481837369695969186559283

theorem tailTrace_4833361 : CollatzResearch.WordTrace tailWord_4833361 prefixEnd_4833361 2481837369695969186559283 := by
  unfold tailWord_4833361
  simp only [CollatzResearch.WordTrace]
  refine ⟨176287158242566044184699937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117524772161710696123133291 176287158242566044184699937)
  ·
    refine ⟨132215368681924533138524953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176287158242566044184699937 132215368681924533138524953)
    ·
      refine ⟨99161526511443399853893715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132215368681924533138524953 99161526511443399853893715)
      ·
        refine ⟨148742289767165099780840573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99161526511443399853893715 148742289767165099780840573)
        ·
          refine ⟨55778358662686912417815215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148742289767165099780840573 55778358662686912417815215)
          ·
            refine ⟨83667537994030368626722823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55778358662686912417815215 83667537994030368626722823)
            ·
              refine ⟨125501306991045552940084235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83667537994030368626722823 125501306991045552940084235)
              ·
                refine ⟨188251960486568329410126353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125501306991045552940084235 188251960486568329410126353)
                ·
                  refine ⟨141188970364926247057594765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188251960486568329410126353 141188970364926247057594765)
                  ·
                    refine ⟨52945863886847342646598037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 141188970364926247057594765 52945863886847342646598037)
                    ·
                      refine ⟨2481837369695969186559283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52945863886847342646598037 2481837369695969186559283)
                      ·
                        rfl

theorem cell23_4833361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_4833361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833361 prefixEnd_4833361 := by exact prefixLift 4833361
  have htrace : WordTrace (prefixWord ++ tailWord_4833361) baseStart_4833361 baseEnd_4833361 := by
    simpa [prefixWord, tailWord_4833361, baseEnd_4833361] using wordTrace_append hprefix tailTrace_4833361
  have hstable : (prefixWord ++ tailWord_4833361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833361).length < 2 ^ (prefixWord ++ tailWord_4833361).sum := by decide
  have hdescent : baseEnd_4833361 < baseStart_4833361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833368 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 2, 4, 3]
def baseStart_4833368 : Nat := 118140960795 + 4833368 * 2 ^ 59
def prefixEnd_4833368 : Nat := 4983230072969 + 3 ^ 40 * 4833368 * 2
def baseEnd_4833368 : Nat := 2481840964060550659171751

theorem tailTrace_4833368 : CollatzResearch.WordTrace tailWord_4833368 prefixEnd_4833368 2481840964060550659171751 := by
  unfold tailWord_4833368
  simp only [CollatzResearch.WordTrace]
  refine ⟨88143706776770342190102379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117524942369027122920136505 88143706776770342190102379)
  ·
    refine ⟨132215560165155513285153569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88143706776770342190102379 132215560165155513285153569)
    ·
      refine ⟨99161670123866634963865177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132215560165155513285153569 99161670123866634963865177)
      ·
        refine ⟨74371252592899976222898883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99161670123866634963865177 74371252592899976222898883)
        ·
          refine ⟨111556878889349964334348325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74371252592899976222898883 111556878889349964334348325)
          ·
            refine ⟨20916914791753118312690311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111556878889349964334348325 20916914791753118312690311)
            ·
              refine ⟨31375372187629677469035467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20916914791753118312690311 31375372187629677469035467)
              ·
                refine ⟨47063058281444516203553201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31375372187629677469035467 47063058281444516203553201)
                ·
                  refine ⟨35297293711083387152664901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47063058281444516203553201 35297293711083387152664901)
                  ·
                    refine ⟨6618242570828135091124669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35297293711083387152664901 6618242570828135091124669)
                    ·
                      refine ⟨2481840964060550659171751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6618242570828135091124669 2481840964060550659171751)
                      ·
                        rfl

theorem cell23_4833368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_4833368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833368 prefixEnd_4833368 := by exact prefixLift 4833368
  have htrace : WordTrace (prefixWord ++ tailWord_4833368) baseStart_4833368 baseEnd_4833368 := by
    simpa [prefixWord, tailWord_4833368, baseEnd_4833368] using wordTrace_append hprefix tailTrace_4833368
  have hstable : (prefixWord ++ tailWord_4833368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833368).length < 2 ^ (prefixWord ++ tailWord_4833368).sum := by decide
  have hdescent : baseEnd_4833368 < baseStart_4833368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833388 : List Nat := [2, 2, 1, 1, 3, 4, 1, 2, 7]
def baseStart_4833388 : Nat := 118140960795 + 4833388 * 2 ^ 59
def prefixEnd_4833388 : Nat := 4983230072969 + 3 ^ 40 * 4833388 * 2
def baseEnd_4833388 : Nat := 275761248185960064546851

theorem tailTrace_4833388 : CollatzResearch.WordTrace tailWord_4833388 prefixEnd_4833388 275761248185960064546851 := by
  unfold tailWord_4833388
  simp only [CollatzResearch.WordTrace]
  refine ⟨88144071506734113897966409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117525428675645485197288545 88144071506734113897966409)
  ·
    refine ⟨66108053630050585423474807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88144071506734113897966409 66108053630050585423474807)
    ·
      refine ⟨99162080445075878135212211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66108053630050585423474807 99162080445075878135212211)
      ·
        refine ⟨148743120667613817202818317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99162080445075878135212211 148743120667613817202818317)
        ·
          refine ⟨55778670250355181451056869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148743120667613817202818317 55778670250355181451056869)
          ·
            refine ⟨10458500671941596522073163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55778670250355181451056869 10458500671941596522073163)
            ·
              refine ⟨15687751007912394783109745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10458500671941596522073163 15687751007912394783109745)
              ·
                refine ⟨11765813255934296087332309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15687751007912394783109745 11765813255934296087332309)
                ·
                  refine ⟨275761248185960064546851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11765813255934296087332309 275761248185960064546851)
                  ·
                    rfl

theorem cell23_4833388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 7].length) (baseStart_4833388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833388 prefixEnd_4833388 := by exact prefixLift 4833388
  have htrace : WordTrace (prefixWord ++ tailWord_4833388) baseStart_4833388 baseEnd_4833388 := by
    simpa [prefixWord, tailWord_4833388, baseEnd_4833388] using wordTrace_append hprefix tailTrace_4833388
  have hstable : (prefixWord ++ tailWord_4833388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833388).length < 2 ^ (prefixWord ++ tailWord_4833388).sum := by decide
  have hdescent : baseEnd_4833388 < baseStart_4833388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833405 : List Nat := [1, 4, 1, 1, 3, 2, 1, 5, 5]
def baseStart_4833405 : Nat := 118140960795 + 4833405 * 2 ^ 59
def prefixEnd_4833405 : Nat := 4983230072969 + 3 ^ 40 * 4833405 * 2
def baseEnd_4833405 : Nat := 275762218093863001601009

theorem tailTrace_4833405 : CollatzResearch.WordTrace tailWord_4833405 prefixEnd_4833405 275762218093863001601009 := by
  unfold tailWord_4833405
  simp only [CollatzResearch.WordTrace]
  refine ⟨176288763054406639699301669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117525842036271093132867779 176288763054406639699301669)
  ·
    refine ⟨33054143072701244943619063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176288763054406639699301669 33054143072701244943619063)
    ·
      refine ⟨49581214609051867415428595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33054143072701244943619063 49581214609051867415428595)
      ·
        refine ⟨74371821913577801123142893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49581214609051867415428595 74371821913577801123142893)
        ·
          refine ⟨27889433217591675421178585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74371821913577801123142893 27889433217591675421178585)
          ·
            refine ⟨20917074913193756565883939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27889433217591675421178585 20917074913193756565883939)
            ·
              refine ⟨31375612369790634848825909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20917074913193756565883939 31375612369790634848825909)
              ·
                refine ⟨2941463659667872017077429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31375612369790634848825909 2941463659667872017077429)
                ·
                  refine ⟨275762218093863001601009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2941463659667872017077429 275762218093863001601009)
                  ·
                    rfl

theorem cell23_4833405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_4833405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833405 prefixEnd_4833405 := by exact prefixLift 4833405
  have htrace : WordTrace (prefixWord ++ tailWord_4833405) baseStart_4833405 baseEnd_4833405 := by
    simpa [prefixWord, tailWord_4833405, baseEnd_4833405] using wordTrace_append hprefix tailTrace_4833405
  have hstable : (prefixWord ++ tailWord_4833405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833405).length < 2 ^ (prefixWord ++ tailWord_4833405).sum := by decide
  have hdescent : baseEnd_4833405 < baseStart_4833405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833416 : List Nat := [2, 1, 3, 4, 1, 3, 1, 2, 2, 2, 2]
def baseStart_4833416 : Nat := 118140960795 + 4833416 * 2 ^ 59
def prefixEnd_4833416 : Nat := 4983230072969 + 3 ^ 40 * 4833416 * 2
def baseEnd_4833416 : Nat := 2481865611131966471371531

theorem tailTrace_4833416 : CollatzResearch.WordTrace tailWord_4833416 prefixEnd_4833416 2481865611131966471371531 := by
  unfold tailWord_4833416
  simp only [CollatzResearch.WordTrace]
  refine ⟨88144582128683394288976051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117526109504911192385301401 88144582128683394288976051)
  ·
    refine ⟨132216873193025091433464077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88144582128683394288976051 132216873193025091433464077)
    ·
      refine ⟨49581327447384409287549029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132216873193025091433464077 49581327447384409287549029)
      ·
        refine ⟨9296498896384576741415443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49581327447384409287549029 9296498896384576741415443)
        ·
          refine ⟨13944748344576865112123165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9296498896384576741415443 13944748344576865112123165)
          ·
            refine ⟨5229280629216324417046187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13944748344576865112123165 5229280629216324417046187)
            ·
              refine ⟨7843920943824486625569281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5229280629216324417046187 7843920943824486625569281)
              ·
                refine ⟨5882940707868364969176961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7843920943824486625569281 5882940707868364969176961)
                ·
                  refine ⟨4412205530901273726882721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5882940707868364969176961 4412205530901273726882721)
                  ·
                    refine ⟨3309154148175955295162041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4412205530901273726882721 3309154148175955295162041)
                    ·
                      refine ⟨2481865611131966471371531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3309154148175955295162041 2481865611131966471371531)
                      ·
                        rfl

theorem cell23_4833416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_4833416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833416 prefixEnd_4833416 := by exact prefixLift 4833416
  have htrace : WordTrace (prefixWord ++ tailWord_4833416) baseStart_4833416 baseEnd_4833416 := by
    simpa [prefixWord, tailWord_4833416, baseEnd_4833416] using wordTrace_append hprefix tailTrace_4833416
  have hstable : (prefixWord ++ tailWord_4833416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833416).length < 2 ^ (prefixWord ++ tailWord_4833416).sum := by decide
  have hdescent : baseEnd_4833416 < baseStart_4833416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833498 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6]
def baseStart_4833498 : Nat := 118140960795 + 4833498 * 2 ^ 59
def prefixEnd_4833498 : Nat := 4983230072969 + 3 ^ 40 * 4833498 * 2
def baseEnd_4833498 : Nat := 2481907716545635150546153

theorem tailTrace_4833498 : CollatzResearch.WordTrace tailWord_4833498 prefixEnd_4833498 2481907716545635150546153 := by
  unfold tailWord_4833498
  simp only [CollatzResearch.WordTrace]
  refine ⟨44073038760767429145609287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117528103362046477721624765 44073038760767429145609287)
  ·
    refine ⟨66109558141151143718413931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44073038760767429145609287 66109558141151143718413931)
    ·
      refine ⟨99164337211726715577620897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66109558141151143718413931 99164337211726715577620897)
      ·
        refine ⟨74373252908795036683215673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99164337211726715577620897 74373252908795036683215673)
        ·
          refine ⟨55779939681596277512411755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74373252908795036683215673 55779939681596277512411755)
          ·
            refine ⟨83669909522394416268617633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55779939681596277512411755 83669909522394416268617633)
            ·
              refine ⟨62752432141795812201463225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83669909522394416268617633 62752432141795812201463225)
              ·
                refine ⟨47064324106346859151097419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62752432141795812201463225 47064324106346859151097419)
                ·
                  refine ⟨70596486159520288726646129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47064324106346859151097419 70596486159520288726646129)
                  ·
                    refine ⟨52947364619640216544984597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70596486159520288726646129 52947364619640216544984597)
                    ·
                      refine ⟨2481907716545635150546153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52947364619640216544984597 2481907716545635150546153)
                      ·
                        rfl

theorem cell23_4833498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_4833498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833498 prefixEnd_4833498 := by exact prefixLift 4833498
  have htrace : WordTrace (prefixWord ++ tailWord_4833498) baseStart_4833498 baseEnd_4833498 := by
    simpa [prefixWord, tailWord_4833498, baseEnd_4833498] using wordTrace_append hprefix tailTrace_4833498
  have hstable : (prefixWord ++ tailWord_4833498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833498).length < 2 ^ (prefixWord ++ tailWord_4833498).sum := by decide
  have hdescent : baseEnd_4833498 < baseStart_4833498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833539 : List Nat := [1, 1, 1, 3, 2, 3, 3, 4, 1, 1, 3]
def baseStart_4833539 : Nat := 118140960795 + 4833539 * 2 ^ 59
def prefixEnd_4833539 : Nat := 4983230072969 + 3 ^ 40 * 4833539 * 2
def baseEnd_4833539 : Nat := 2481928769252469490133465

theorem tailTrace_4833539 : CollatzResearch.WordTrace tailWord_4833539 prefixEnd_4833539 2481928769252469490133465 := by
  unfold tailWord_4833539
  simp only [CollatzResearch.WordTrace]
  refine ⟨176293650435921180584679671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117529100290614120389786447 176293650435921180584679671)
  ·
    refine ⟨264440475653881770877019507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176293650435921180584679671 264440475653881770877019507)
    ·
      refine ⟨396660713480822656315529261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264440475653881770877019507 396660713480822656315529261)
      ·
        refine ⟨148747767555308496118323473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 396660713480822656315529261 148747767555308496118323473)
        ·
          refine ⟨111560825666481372088742605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148747767555308496118323473 111560825666481372088742605)
          ·
            refine ⟨41835309624930514533278477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111560825666481372088742605 41835309624930514533278477)
            ·
              refine ⟨15688241109348942949979429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41835309624930514533278477 15688241109348942949979429)
              ·
                refine ⟨2941545208002926803121143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15688241109348942949979429 2941545208002926803121143)
                ·
                  refine ⟨4412317812004390204681715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2941545208002926803121143 4412317812004390204681715)
                  ·
                    refine ⟨6618476718006585307022573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4412317812004390204681715 6618476718006585307022573)
                    ·
                      refine ⟨2481928769252469490133465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6618476718006585307022573 2481928769252469490133465)
                      ·
                        rfl

theorem cell23_4833539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 1, 1, 3].length) (baseStart_4833539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833539 prefixEnd_4833539 := by exact prefixLift 4833539
  have htrace : WordTrace (prefixWord ++ tailWord_4833539) baseStart_4833539 baseEnd_4833539 := by
    simpa [prefixWord, tailWord_4833539, baseEnd_4833539] using wordTrace_append hprefix tailTrace_4833539
  have hstable : (prefixWord ++ tailWord_4833539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833539).length < 2 ^ (prefixWord ++ tailWord_4833539).sum := by decide
  have hdescent : baseEnd_4833539 < baseStart_4833539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833545 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 3, 1, 4]
def baseStart_4833545 : Nat := 118140960795 + 4833545 * 2 ^ 59
def prefixEnd_4833545 : Nat := 4983230072969 + 3 ^ 40 * 4833545 * 2
def baseEnd_4833545 : Nat := 2481931850136396466658437

theorem tailTrace_4833545 : CollatzResearch.WordTrace tailWord_4833545 prefixEnd_4833545 2481931850136396466658437 := by
  unfold tailWord_4833545
  simp only [CollatzResearch.WordTrace]
  refine ⟨176293869273899443609398089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117529246182599629072932059 176293869273899443609398089)
  ·
    refine ⟨132220401955424582707048567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176293869273899443609398089 132220401955424582707048567)
    ·
      refine ⟨198330602933136874060572851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132220401955424582707048567 198330602933136874060572851)
      ·
        refine ⟨297495904399705311090859277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198330602933136874060572851 297495904399705311090859277)
        ·
          refine ⟨111560964149889491659072229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297495904399705311090859277 111560964149889491659072229)
          ·
            refine ⟨20917680778104279686076043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111560964149889491659072229 20917680778104279686076043)
            ·
              refine ⟨31376521167156419529114065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20917680778104279686076043 31376521167156419529114065)
              ·
                refine ⟨23532390875367314646835549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31376521167156419529114065 23532390875367314646835549)
                ·
                  refine ⟨8824646578262742992563331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23532390875367314646835549 8824646578262742992563331)
                  ·
                    refine ⟨13236969867394114488844997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8824646578262742992563331 13236969867394114488844997)
                    ·
                      refine ⟨2481931850136396466658437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13236969867394114488844997 2481931850136396466658437)
                      ·
                        rfl

theorem cell23_4833545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 1, 4].length) (baseStart_4833545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833545 prefixEnd_4833545 := by exact prefixLift 4833545
  have htrace : WordTrace (prefixWord ++ tailWord_4833545) baseStart_4833545 baseEnd_4833545 := by
    simpa [prefixWord, tailWord_4833545, baseEnd_4833545] using wordTrace_append hprefix tailTrace_4833545
  have hstable : (prefixWord ++ tailWord_4833545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833545).length < 2 ^ (prefixWord ++ tailWord_4833545).sum := by decide
  have hdescent : baseEnd_4833545 < baseStart_4833545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833566 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_4833566 : Nat := 118140960795 + 4833566 * 2 ^ 59
def prefixEnd_4833566 : Nat := 4983230072969 + 3 ^ 40 * 4833566 * 2
def baseEnd_4833566 : Nat := 2481942633230140884495841

theorem tailTrace_4833566 : CollatzResearch.WordTrace tailWord_4833566 prefixEnd_4833566 2481942633230140884495841 := by
  unfold tailWord_4833566
  simp only [CollatzResearch.WordTrace]
  refine ⟨22036829400852920524489069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117529756804548909463941701 22036829400852920524489069)
  ·
    refine ⟨8263811025319845196683401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22036829400852920524489069 8263811025319845196683401)
    ·
      refine ⟨6197858268989883897512551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8263811025319845196683401 6197858268989883897512551)
      ·
        refine ⟨9296787403484825846268827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6197858268989883897512551 9296787403484825846268827)
        ·
          refine ⟨13945181105227238769403241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9296787403484825846268827 13945181105227238769403241)
          ·
            refine ⟨10458885828920429077052431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13945181105227238769403241 10458885828920429077052431)
            ·
              refine ⟨15688328743380643615578647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10458885828920429077052431 15688328743380643615578647)
              ·
                refine ⟨23532493115070965423367971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15688328743380643615578647 23532493115070965423367971)
                ·
                  refine ⟨35298739672606448135051957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23532493115070965423367971 35298739672606448135051957)
                  ·
                    refine ⟨3309256844306854512661121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35298739672606448135051957 3309256844306854512661121)
                    ·
                      refine ⟨2481942633230140884495841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3309256844306854512661121 2481942633230140884495841)
                      ·
                        rfl

theorem cell23_4833566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_4833566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833566 prefixEnd_4833566 := by exact prefixLift 4833566
  have htrace : WordTrace (prefixWord ++ tailWord_4833566) baseStart_4833566 baseEnd_4833566 := by
    simpa [prefixWord, tailWord_4833566, baseEnd_4833566] using wordTrace_append hprefix tailTrace_4833566
  have hstable : (prefixWord ++ tailWord_4833566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833566).length < 2 ^ (prefixWord ++ tailWord_4833566).sum := by decide
  have hdescent : baseEnd_4833566 < baseStart_4833566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833576 : List Nat := [2, 1, 5, 1, 3, 2, 2, 1, 1, 5]
def baseStart_4833576 : Nat := 118140960795 + 4833576 * 2 ^ 59
def prefixEnd_4833576 : Nat := 4983230072969 + 3 ^ 40 * 4833576 * 2
def baseEnd_4833576 : Nat := 827315922678895281790265

theorem tailTrace_4833576 : CollatzResearch.WordTrace tailWord_4833576 prefixEnd_4833576 827315922678895281790265 := by
  unfold tailWord_4833576
  simp only [CollatzResearch.WordTrace]
  refine ⟨88147499968393567951888291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117529999957858090602517721 88147499968393567951888291)
  ·
    refine ⟨132221249952590351927832437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88147499968393567951888291 132221249952590351927832437)
    ·
      refine ⟨12395742183055345493234291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132221249952590351927832437 12395742183055345493234291)
      ·
        refine ⟨18593613274583018239851437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12395742183055345493234291 18593613274583018239851437)
        ·
          refine ⟨6972604977968631839944289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18593613274583018239851437 6972604977968631839944289)
          ·
            refine ⟨5229453733476473879958217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6972604977968631839944289 5229453733476473879958217)
            ·
              refine ⟨3922090300107355409968663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5229453733476473879958217 3922090300107355409968663)
              ·
                refine ⟨5883135450161033114952995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3922090300107355409968663 5883135450161033114952995)
                ·
                  refine ⟨8824703175241549672429493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5883135450161033114952995 8824703175241549672429493)
                  ·
                    refine ⟨827315922678895281790265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8824703175241549672429493 827315922678895281790265)
                    ·
                      rfl

theorem cell23_4833576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_4833576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833576 prefixEnd_4833576 := by exact prefixLift 4833576
  have htrace : WordTrace (prefixWord ++ tailWord_4833576) baseStart_4833576 baseEnd_4833576 := by
    simpa [prefixWord, tailWord_4833576, baseEnd_4833576] using wordTrace_append hprefix tailTrace_4833576
  have hstable : (prefixWord ++ tailWord_4833576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833576).length < 2 ^ (prefixWord ++ tailWord_4833576).sum := by decide
  have hdescent : baseEnd_4833576 < baseStart_4833576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833585 : List Nat := [1, 2, 2, 3, 4, 1, 10]
def baseStart_4833585 : Nat := 118140960795 + 4833585 * 2 ^ 59
def prefixEnd_4833585 : Nat := 4983230072969 + 3 ^ 40 * 4833585 * 2
def baseEnd_4833585 : Nat := 30641387522994769261213

theorem tailTrace_4833585 : CollatzResearch.WordTrace tailWord_4833585 prefixEnd_4833585 30641387522994769261213 := by
  unfold tailWord_4833585
  simp only [CollatzResearch.WordTrace]
  refine ⟨176295328193754530440854209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117530218795836353627236139 176295328193754530440854209)
  ·
    refine ⟨132221496145315897830640657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176295328193754530440854209 132221496145315897830640657)
    ·
      refine ⟨99166122108986923372980493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132221496145315897830640657 99166122108986923372980493)
      ·
        refine ⟨37187295790870096264867685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99166122108986923372980493 37187295790870096264867685)
        ·
          refine ⟨6972617960788143049662691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37187295790870096264867685 6972617960788143049662691)
          ·
            refine ⟨10458926941182214574494037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6972617960788143049662691 10458926941182214574494037)
            ·
              refine ⟨30641387522994769261213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10458926941182214574494037 30641387522994769261213)
              ·
                rfl

theorem cell23_4833585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 10].length) (baseStart_4833585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833585 prefixEnd_4833585 := by exact prefixLift 4833585
  have htrace : WordTrace (prefixWord ++ tailWord_4833585) baseStart_4833585 baseEnd_4833585 := by
    simpa [prefixWord, tailWord_4833585, baseEnd_4833585] using wordTrace_append hprefix tailTrace_4833585
  have hstable : (prefixWord ++ tailWord_4833585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833585).length < 2 ^ (prefixWord ++ tailWord_4833585).sum := by decide
  have hdescent : baseEnd_4833585 < baseStart_4833585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833596 : List Nat := [2, 2, 2, 2, 1, 2, 1, 6, 1, 2, 2]
def baseStart_4833596 : Nat := 118140960795 + 4833596 * 2 ^ 59
def prefixEnd_4833596 : Nat := 4983230072969 + 3 ^ 40 * 4833596 * 2
def baseEnd_4833596 : Nat := 2481958037649775767120703

theorem tailTrace_4833596 : CollatzResearch.WordTrace tailWord_4833596 prefixEnd_4833596 2481958037649775767120703 := by
  unfold tailWord_4833596
  simp only [CollatzResearch.WordTrace]
  refine ⟨88147864698357339659752321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117530486264476452879669761 88147864698357339659752321)
  ·
    refine ⟨66110898523768004744814241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88147864698357339659752321 66110898523768004744814241)
    ·
      refine ⟨49583173892826003558610681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66110898523768004744814241 49583173892826003558610681)
      ·
        refine ⟨37187380419619502668958011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49583173892826003558610681 37187380419619502668958011)
        ·
          refine ⟨55781070629429254003437017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37187380419619502668958011 55781070629429254003437017)
          ·
            refine ⟨41835802972071940502577763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55781070629429254003437017 41835802972071940502577763)
            ·
              refine ⟨62753704458107910753866645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41835802972071940502577763 62753704458107910753866645)
              ·
                refine ⟨2941579896473808316587499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62753704458107910753866645 2941579896473808316587499)
                ·
                  refine ⟨4412369844710712474881249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2941579896473808316587499 4412369844710712474881249)
                  ·
                    refine ⟨3309277383533034356160937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4412369844710712474881249 3309277383533034356160937)
                    ·
                      refine ⟨2481958037649775767120703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3309277383533034356160937 2481958037649775767120703)
                      ·
                        rfl

theorem cell23_4833596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_4833596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833596 prefixEnd_4833596 := by exact prefixLift 4833596
  have htrace : WordTrace (prefixWord ++ tailWord_4833596) baseStart_4833596 baseEnd_4833596 := by
    simpa [prefixWord, tailWord_4833596, baseEnd_4833596] using wordTrace_append hprefix tailTrace_4833596
  have hstable : (prefixWord ++ tailWord_4833596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833596).length < 2 ^ (prefixWord ++ tailWord_4833596).sum := by decide
  have hdescent : baseEnd_4833596 < baseStart_4833596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833703 : List Nat := [1, 1, 6, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_4833703 : Nat := 118140960795 + 4833703 * 2 ^ 59
def prefixEnd_4833703 : Nat := 4983230072969 + 3 ^ 40 * 4833703 * 2
def baseEnd_4833703 : Nat := 2482012980079806848482711

theorem tailTrace_4833703 : CollatzResearch.WordTrace tailWord_4833703 prefixEnd_4833703 2482012980079806848482711 := by
  unfold tailWord_4833703
  simp only [CollatzResearch.WordTrace]
  refine ⟨176299632007327036593649763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117533088004884691062433175 176299632007327036593649763)
  ·
    refine ⟨264449448010990554890474645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176299632007327036593649763 264449448010990554890474645)
    ·
      refine ⟨12396067875515182260490999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 264449448010990554890474645 12396067875515182260490999)
      ·
        refine ⟨18594101813272773390736499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12396067875515182260490999 18594101813272773390736499)
        ·
          refine ⟨27891152719909160086104749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18594101813272773390736499 27891152719909160086104749)
          ·
            refine ⟨10459182269965935032289281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27891152719909160086104749 10459182269965935032289281)
            ·
              refine ⟨7844386702474451274216961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10459182269965935032289281 7844386702474451274216961)
              ·
                refine ⟨5883290026855838455662721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7844386702474451274216961 5883290026855838455662721)
                ·
                  refine ⟨4412467520141878841747041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5883290026855838455662721 4412467520141878841747041)
                  ·
                    refine ⟨3309350640106409131310281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4412467520141878841747041 3309350640106409131310281)
                    ·
                      refine ⟨2482012980079806848482711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3309350640106409131310281 2482012980079806848482711)
                      ·
                        rfl

theorem cell23_4833703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_4833703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833703 prefixEnd_4833703 := by exact prefixLift 4833703
  have htrace : WordTrace (prefixWord ++ tailWord_4833703) baseStart_4833703 baseEnd_4833703 := by
    simpa [prefixWord, tailWord_4833703, baseEnd_4833703] using wordTrace_append hprefix tailTrace_4833703
  have hstable : (prefixWord ++ tailWord_4833703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833703).length < 2 ^ (prefixWord ++ tailWord_4833703).sum := by decide
  have hdescent : baseEnd_4833703 < baseStart_4833703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833752 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 7, 4]
def baseStart_4833752 : Nat := 118140960795 + 4833752 * 2 ^ 59
def prefixEnd_4833752 : Nat := 4983230072969 + 3 ^ 40 * 4833752 * 2
def baseEnd_4833752 : Nat := 827346046877292385589995

theorem tailTrace_4833752 : CollatzResearch.WordTrace tailWord_4833752 prefixEnd_4833752 827346046877292385589995 := by
  unfold tailWord_4833752
  simp only [CollatzResearch.WordTrace]
  refine ⟨88150709592074758981091755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117534279456099678641455673 88150709592074758981091755)
  ·
    refine ⟨132226064388112138471637633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88150709592074758981091755 132226064388112138471637633)
    ·
      refine ⟨99169548291084103853728225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132226064388112138471637633 99169548291084103853728225)
      ·
        refine ⟨74377161218313077890296169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99169548291084103853728225 74377161218313077890296169)
        ·
          refine ⟨55782870913734808417722127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74377161218313077890296169 55782870913734808417722127)
          ·
            refine ⟨83674306370602212626583191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55782870913734808417722127 83674306370602212626583191)
            ·
              refine ⟨125511459555903318939874787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83674306370602212626583191 125511459555903318939874787)
              ·
                refine ⟨188267189333854978409812181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125511459555903318939874787 188267189333854978409812181)
                ·
                  refine ⟨4412512250012226056479973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 188267189333854978409812181 4412512250012226056479973)
                  ·
                    refine ⟨827346046877292385589995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4412512250012226056479973 827346046877292385589995)
                    ·
                      rfl

theorem cell23_4833752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_4833752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833752 prefixEnd_4833752 := by exact prefixLift 4833752
  have htrace : WordTrace (prefixWord ++ tailWord_4833752) baseStart_4833752 baseEnd_4833752 := by
    simpa [prefixWord, tailWord_4833752, baseEnd_4833752] using wordTrace_append hprefix tailTrace_4833752
  have hstable : (prefixWord ++ tailWord_4833752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833752).length < 2 ^ (prefixWord ++ tailWord_4833752).sum := by decide
  have hdescent : baseEnd_4833752 < baseStart_4833752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833759 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 2, 4, 2]
def baseStart_4833759 : Nat := 118140960795 + 4833759 * 2 ^ 59
def prefixEnd_4833759 : Nat := 4983230072969 + 3 ^ 40 * 4833759 * 2
def baseEnd_4833759 : Nat := 2482041734996458629382453

theorem tailTrace_4833759 : CollatzResearch.WordTrace tailWord_4833759 prefixEnd_4833759 2482041734996458629382453 := by
  unfold tailWord_4833759
  simp only [CollatzResearch.WordTrace]
  refine ⟨176301674495124158157688331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117534449663416105438458887 176301674495124158157688331)
  ·
    refine ⟨264452511742686237236532497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176301674495124158157688331 264452511742686237236532497)
    ·
      refine ⟨198339383807014677927399373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264452511742686237236532497 198339383807014677927399373)
      ·
        refine ⟨74377268927630504222774765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198339383807014677927399373 74377268927630504222774765)
        ·
          refine ⟨27891475847861439083540537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74377268927630504222774765 27891475847861439083540537)
          ·
            refine ⟨20918606885896079312655403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27891475847861439083540537 20918606885896079312655403)
            ·
              refine ⟨31377910328844118968983105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20918606885896079312655403 31377910328844118968983105)
              ·
                refine ⟨23533432746633089226737329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31377910328844118968983105 23533432746633089226737329)
                ·
                  refine ⟨17650074559974816920052997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23533432746633089226737329 17650074559974816920052997)
                  ·
                    refine ⟨3309388979995278172509937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17650074559974816920052997 3309388979995278172509937)
                    ·
                      refine ⟨2482041734996458629382453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3309388979995278172509937 2482041734996458629382453)
                      ·
                        rfl

theorem cell23_4833759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_4833759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833759 prefixEnd_4833759 := by exact prefixLift 4833759
  have htrace : WordTrace (prefixWord ++ tailWord_4833759) baseStart_4833759 baseEnd_4833759 := by
    simpa [prefixWord, tailWord_4833759, baseEnd_4833759] using wordTrace_append hprefix tailTrace_4833759
  have hstable : (prefixWord ++ tailWord_4833759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833759).length < 2 ^ (prefixWord ++ tailWord_4833759).sum := by decide
  have hdescent : baseEnd_4833759 < baseStart_4833759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833803 : List Nat := [1, 1, 1, 1, 7, 3, 1, 3, 1, 4]
def baseStart_4833803 : Nat := 118140960795 + 4833803 * 2 ^ 59
def prefixEnd_4833803 : Nat := 4983230072969 + 3 ^ 40 * 4833803 * 2
def baseEnd_4833803 : Nat := 827354776048418819077417

theorem tailTrace_4833803 : CollatzResearch.WordTrace tailWord_4833803 prefixEnd_4833803 827354776048418819077417 := by
  unfold tailWord_4833803
  simp only [CollatzResearch.WordTrace]
  refine ⟨176303279306964753672290063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117535519537976502448193375 176303279306964753672290063)
  ·
    refine ⟨264454918960447130508435095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176303279306964753672290063 264454918960447130508435095)
    ·
      refine ⟨396682378440670695762652643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264454918960447130508435095 396682378440670695762652643)
      ·
        refine ⟨595023567661006043643978965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396682378440670695762652643 595023567661006043643978965)
        ·
          refine ⟨13945864867054829147905757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 595023567661006043643978965 13945864867054829147905757)
          ·
            refine ⟨5229699325145560930464659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13945864867054829147905757 5229699325145560930464659)
            ·
              refine ⟨7844548987718341395696989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5229699325145560930464659 7844548987718341395696989)
              ·
                refine ⟨2941705870394378023386371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7844548987718341395696989 2941705870394378023386371)
                ·
                  refine ⟨4412558805591567035079557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2941705870394378023386371 4412558805591567035079557)
                  ·
                    refine ⟨827354776048418819077417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4412558805591567035079557 827354776048418819077417)
                    ·
                      rfl

theorem cell23_4833803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 1, 4].length) (baseStart_4833803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833803 prefixEnd_4833803 := by exact prefixLift 4833803
  have htrace : WordTrace (prefixWord ++ tailWord_4833803) baseStart_4833803 baseEnd_4833803 := by
    simpa [prefixWord, tailWord_4833803, baseEnd_4833803] using wordTrace_append hprefix tailTrace_4833803
  have hstable : (prefixWord ++ tailWord_4833803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833803).length < 2 ^ (prefixWord ++ tailWord_4833803).sum := by decide
  have hdescent : baseEnd_4833803 < baseStart_4833803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833846 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_4833846 : Nat := 118140960795 + 4833846 * 2 ^ 59
def prefixEnd_4833846 : Nat := 4983230072969 + 3 ^ 40 * 4833846 * 2
def baseEnd_4833846 : Nat := 827362135937799929664851

theorem tailTrace_4833846 : CollatzResearch.WordTrace tailWord_4833846 prefixEnd_4833846 827362135937799929664851 := by
  unfold tailWord_4833846
  simp only [CollatzResearch.WordTrace]
  refine ⟨11019052977863060751006587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117536565097205981344070261 11019052977863060751006587)
  ·
    refine ⟨16528579466794591126509881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11019052977863060751006587 16528579466794591126509881)
    ·
      refine ⟨12396434600095943344882411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16528579466794591126509881 12396434600095943344882411)
      ·
        refine ⟨18594651900143915017323617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12396434600095943344882411 18594651900143915017323617)
        ·
          refine ⟨13945988925107936262992713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18594651900143915017323617 13945988925107936262992713)
          ·
            refine ⟨10459491693830952197244535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13945988925107936262992713 10459491693830952197244535)
            ·
              refine ⟨15689237540746428295866803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10459491693830952197244535 15689237540746428295866803)
              ·
                refine ⟨23533856311119642443800205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15689237540746428295866803 23533856311119642443800205)
                ·
                  refine ⟨8825196116669865916425077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23533856311119642443800205 8825196116669865916425077)
                  ·
                    refine ⟨827362135937799929664851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8825196116669865916425077 827362135937799929664851)
                    ·
                      rfl

theorem cell23_4833846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_4833846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833846 prefixEnd_4833846 := by exact prefixLift 4833846
  have htrace : WordTrace (prefixWord ++ tailWord_4833846) baseStart_4833846 baseEnd_4833846 := by
    simpa [prefixWord, tailWord_4833846, baseEnd_4833846] using wordTrace_append hprefix tailTrace_4833846
  have hstable : (prefixWord ++ tailWord_4833846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833846).length < 2 ^ (prefixWord ++ tailWord_4833846).sum := by decide
  have hdescent : baseEnd_4833846 < baseStart_4833846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
