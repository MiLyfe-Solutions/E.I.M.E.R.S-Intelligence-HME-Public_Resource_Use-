import V185TrunkScan20Incremental

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_13 : List Nat := [1, 7, 1, 2, 1, 2, 1, 1, 5]
def baseStart_13 : Nat := 118140960795 + 13 * 2 ^ 59
def prefixEnd_13 : Nat := 4983230072969 + 3 ^ 40 * 13 * 2
def baseEnd_13 : Nat := 2966777161636816643

theorem tailTrace_13 : CollatzResearch.WordTrace tailWord_13 prefixEnd_13 2966777161636816643 := by
  unfold tailWord_13
  simp only [CollatzResearch.WordTrace]
  refine ⟨474148960378065332693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 316099306918710221795 474148960378065332693)
  ·
    refine ⟨11112866258860906235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 474148960378065332693 11112866258860906235)
    ·
      refine ⟨16669299388291359353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11112866258860906235 16669299388291359353)
      ·
        refine ⟨12501974541218519515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16669299388291359353 12501974541218519515)
        ·
          refine ⟨18752961811827779273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12501974541218519515 18752961811827779273)
          ·
            refine ⟨14064721358870834455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18752961811827779273 14064721358870834455)
            ·
              refine ⟨21097082038306251683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14064721358870834455 21097082038306251683)
              ·
                refine ⟨31645623057459377525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21097082038306251683 31645623057459377525)
                ·
                  refine ⟨2966777161636816643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31645623057459377525 2966777161636816643)
                  ·
                    rfl

theorem cell21_13_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_13 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_13 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_13 prefixEnd_13 := by exact prefixLift 13
  have htrace : WordTrace (prefixWord ++ tailWord_13) baseStart_13 baseEnd_13 := by
    simpa [prefixWord, tailWord_13, baseEnd_13] using wordTrace_append hprefix tailTrace_13
  have hstable : (prefixWord ++ tailWord_13).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13).length < 2 ^ (prefixWord ++ tailWord_13).sum := by decide
  have hdescent : baseEnd_13 < baseStart_13 := by decide
  rcases family_descends (prefixWord ++ tailWord_13) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86 : List Nat := [5, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_86 : Nat := 118140960795 + 86 * 2 ^ 59
def prefixEnd_86 : Nat := 4983230072969 + 3 ^ 40 * 86 * 2
def baseEnd_86 : Nat := 19626371729732099827

theorem tailTrace_86 : CollatzResearch.WordTrace tailWord_86 prefixEnd_86 19626371729732099827 := by
  unfold tailWord_86
  simp only [CollatzResearch.WordTrace]
  refine ⟨196042355994470796257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2091118463941021826741 196042355994470796257)
  ·
    refine ⟨147031766995853097193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196042355994470796257 147031766995853097193)
    ·
      refine ⟨110273825246889822895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147031766995853097193 110273825246889822895)
      ·
        refine ⟨165410737870334734343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110273825246889822895 165410737870334734343)
        ·
          refine ⟨248116106805502101515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165410737870334734343 248116106805502101515)
          ·
            refine ⟨372174160208253152273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248116106805502101515 372174160208253152273)
            ·
              refine ⟨279130620156189864205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 372174160208253152273 279130620156189864205)
              ·
                refine ⟨104673982558571199077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279130620156189864205 104673982558571199077)
                ·
                  refine ⟨19626371729732099827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104673982558571199077 19626371729732099827)
                  ·
                    rfl

theorem cell21_86_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_86 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86 prefixEnd_86 := by exact prefixLift 86
  have htrace : WordTrace (prefixWord ++ tailWord_86) baseStart_86 baseEnd_86 := by
    simpa [prefixWord, tailWord_86, baseEnd_86] using wordTrace_append hprefix tailTrace_86
  have hstable : (prefixWord ++ tailWord_86).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86).length < 2 ^ (prefixWord ++ tailWord_86).sum := by decide
  have hdescent : baseEnd_86 < baseStart_86 := by decide
  rcases family_descends (prefixWord ++ tailWord_86) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114 : List Nat := [3, 2, 1, 2, 2, 2, 1, 5, 3]
def baseStart_114 : Nat := 118140960795 + 114 * 2 ^ 59
def prefixEnd_114 : Nat := 4983230072969 + 3 ^ 40 * 114 * 2
def baseEnd_114 : Nat := 26016353207905633103

theorem tailTrace_114 : CollatzResearch.WordTrace tailWord_114 prefixEnd_114 26016353207905633103 := by
  unfold tailWord_114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1039480398618078689849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2771947729648209839597 1039480398618078689849)
  ·
    refine ⟨779610298963559017387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1039480398618078689849 779610298963559017387)
    ·
      refine ⟨1169415448445338526081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 779610298963559017387 1169415448445338526081)
      ·
        refine ⟨877061586334003894561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1169415448445338526081 877061586334003894561)
        ·
          refine ⟨657796189750502920921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 877061586334003894561 657796189750502920921)
          ·
            refine ⟨493347142312877190691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657796189750502920921 493347142312877190691)
            ·
              refine ⟨740020713469315786037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493347142312877190691 740020713469315786037)
              ·
                refine ⟨69376941887748354941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 740020713469315786037 69376941887748354941)
                ·
                  refine ⟨26016353207905633103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69376941887748354941 26016353207905633103)
                  ·
                    rfl

theorem cell21_114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114 prefixEnd_114 := by exact prefixLift 114
  have htrace : WordTrace (prefixWord ++ tailWord_114) baseStart_114 baseEnd_114 := by
    simpa [prefixWord, tailWord_114, baseEnd_114] using wordTrace_append hprefix tailTrace_114
  have hstable : (prefixWord ++ tailWord_114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114).length < 2 ^ (prefixWord ++ tailWord_114).sum := by decide
  have hdescent : baseEnd_114 < baseStart_114 := by decide
  rcases family_descends (prefixWord ++ tailWord_114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159 : List Nat := [1, 1, 2, 6, 1, 1, 4, 5]
def baseStart_159 : Nat := 118140960795 + 159 * 2 ^ 59
def prefixEnd_159 : Nat := 4983230072969 + 3 ^ 40 * 159 * 2
def baseEnd_159 : Nat := 12095322099275794337

theorem tailTrace_159 : CollatzResearch.WordTrace tailWord_159 prefixEnd_159 12095322099275794337 := by
  unfold tailWord_159
  simp only [CollatzResearch.WordTrace]
  refine ⟨5799206431445000147531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3866137620963333431687 5799206431445000147531)
  ·
    refine ⟨8698809647167500221297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5799206431445000147531 8698809647167500221297)
    ·
      refine ⟨6524107235375625165973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8698809647167500221297 6524107235375625165973)
      ·
        refine ⟨305817526658232429655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6524107235375625165973 305817526658232429655)
        ·
          refine ⟨458726289987348644483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305817526658232429655 458726289987348644483)
          ·
            refine ⟨688089434981022966725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458726289987348644483 688089434981022966725)
            ·
              refine ⟨129016769058941806261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 688089434981022966725 129016769058941806261)
              ·
                refine ⟨12095322099275794337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129016769058941806261 12095322099275794337)
                ·
                  rfl

theorem cell21_159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 5].length) (baseStart_159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159 prefixEnd_159 := by exact prefixLift 159
  have htrace : WordTrace (prefixWord ++ tailWord_159) baseStart_159 baseEnd_159 := by
    simpa [prefixWord, tailWord_159, baseEnd_159] using wordTrace_append hprefix tailTrace_159
  have hstable : (prefixWord ++ tailWord_159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159).length < 2 ^ (prefixWord ++ tailWord_159).sum := by decide
  have hdescent : baseEnd_159 < baseStart_159 := by decide
  rcases family_descends (prefixWord ++ tailWord_159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187 : List Nat := [1, 1, 1, 1, 1, 2, 6, 4, 4]
def baseStart_187 : Nat := 118140960795 + 187 * 2 ^ 59
def prefixEnd_187 : Nat := 4983230072969 + 3 ^ 40 * 187 * 2
def baseEnd_187 : Nat := 42675947776000916287

theorem tailTrace_187 : CollatzResearch.WordTrace tailWord_187 prefixEnd_187 42675947776000916287 := by
  unfold tailWord_187
  simp only [CollatzResearch.WordTrace]
  refine ⟨6820450330005782166815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4546966886670521444543 6820450330005782166815)
  ·
    refine ⟨10230675495008673250223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6820450330005782166815 10230675495008673250223)
    ·
      refine ⟨15346013242513009875335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10230675495008673250223 15346013242513009875335)
      ·
        refine ⟨23019019863769514813003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15346013242513009875335 23019019863769514813003)
        ·
          refine ⟨34528529795654272219505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23019019863769514813003 34528529795654272219505)
          ·
            refine ⟨25896397346740704164629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34528529795654272219505 25896397346740704164629)
            ·
              refine ⟨1213893625628470507717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25896397346740704164629 1213893625628470507717)
              ·
                refine ⟨227605054805338220197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1213893625628470507717 227605054805338220197)
                ·
                  refine ⟨42675947776000916287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227605054805338220197 42675947776000916287)
                  ·
                    rfl

theorem cell21_187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 4].length) (baseStart_187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_187 prefixEnd_187 := by exact prefixLift 187
  have htrace : WordTrace (prefixWord ++ tailWord_187) baseStart_187 baseEnd_187 := by
    simpa [prefixWord, tailWord_187, baseEnd_187] using wordTrace_append hprefix tailTrace_187
  have hstable : (prefixWord ++ tailWord_187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187).length < 2 ^ (prefixWord ++ tailWord_187).sum := by decide
  have hdescent : baseEnd_187 < baseStart_187 := by decide
  rcases family_descends (prefixWord ++ tailWord_187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277 : List Nat := [1, 3, 2, 1, 2, 1, 2, 9]
def baseStart_277 : Nat := 118140960795 + 277 * 2 ^ 59
def prefixEnd_277 : Nat := 4983230072969 + 3 ^ 40 * 277 * 2
def baseEnd_277 : Nat := 21071724651948138701

theorem tailTrace_277 : CollatzResearch.WordTrace tailWord_277 prefixEnd_277 21071724651948138701 := by
  unfold tailWord_277
  simp only [CollatzResearch.WordTrace]
  refine ⟨10103020003951152943085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6735346669300768628723 10103020003951152943085)
  ·
    refine ⟨3788632501481682353657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10103020003951152943085 3788632501481682353657)
    ·
      refine ⟨2841474376111261765243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3788632501481682353657 2841474376111261765243)
      ·
        refine ⟨4262211564166892647865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2841474376111261765243 4262211564166892647865)
        ·
          refine ⟨3196658673125169485899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4262211564166892647865 3196658673125169485899)
          ·
            refine ⟨4794988009687754228849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196658673125169485899 4794988009687754228849)
            ·
              refine ⟨3596241007265815671637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4794988009687754228849 3596241007265815671637)
              ·
                refine ⟨21071724651948138701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3596241007265815671637 21071724651948138701)
                ·
                  rfl

theorem cell21_277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 9].length) (baseStart_277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277 prefixEnd_277 := by exact prefixLift 277
  have htrace : WordTrace (prefixWord ++ tailWord_277) baseStart_277 baseEnd_277 := by
    simpa [prefixWord, tailWord_277, baseEnd_277] using wordTrace_append hprefix tailTrace_277
  have hstable : (prefixWord ++ tailWord_277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277).length < 2 ^ (prefixWord ++ tailWord_277).sum := by decide
  have hdescent : baseEnd_277 < baseStart_277 := by decide
  rcases family_descends (prefixWord ++ tailWord_277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359 : List Nat := [1, 1, 5, 1, 3, 2, 3, 2, 3]
def baseStart_359 : Nat := 118140960795 + 359 * 2 ^ 59
def prefixEnd_359 : Nat := 4983230072969 + 3 ^ 40 * 359 * 2
def baseEnd_359 : Nat := 81928691141924049269

theorem tailTrace_359 : CollatzResearch.WordTrace tailWord_359 prefixEnd_359 81928691141924049269 := by
  unfold tailWord_359
  simp only [CollatzResearch.WordTrace]
  refine ⟨13093805706879157428131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8729203804586104952087 13093805706879157428131)
  ·
    refine ⟨19640708560318736142197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13093805706879157428131 19640708560318736142197)
    ·
      refine ⟨1841316427529881513331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19640708560318736142197 1841316427529881513331)
      ·
        refine ⟨2761974641294822269997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1841316427529881513331 2761974641294822269997)
        ·
          refine ⟨1035740490485558351249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2761974641294822269997 1035740490485558351249)
          ·
            refine ⟨776805367864168763437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1035740490485558351249 776805367864168763437)
            ·
              refine ⟨291302012949063286289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 776805367864168763437 291302012949063286289)
              ·
                refine ⟨218476509711797464717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291302012949063286289 218476509711797464717)
                ·
                  refine ⟨81928691141924049269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218476509711797464717 81928691141924049269)
                  ·
                    rfl

theorem cell21_359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 3].length) (baseStart_359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359 prefixEnd_359 := by exact prefixLift 359
  have htrace : WordTrace (prefixWord ++ tailWord_359) baseStart_359 baseEnd_359 := by
    simpa [prefixWord, tailWord_359, baseEnd_359] using wordTrace_append hprefix tailTrace_359
  have hstable : (prefixWord ++ tailWord_359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359).length < 2 ^ (prefixWord ++ tailWord_359).sum := by decide
  have hdescent : baseEnd_359 < baseStart_359 := by decide
  rcases family_descends (prefixWord ++ tailWord_359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370 : List Nat := [3, 2, 1, 2, 1, 4, 2, 6]
def baseStart_370 : Nat := 118140960795 + 370 * 2 ^ 59
def prefixEnd_370 : Nat := 4983230072969 + 3 ^ 40 * 370 * 2
def baseEnd_370 : Nat := 28146347002783121971

theorem tailTrace_370 : CollatzResearch.WordTrace tailWord_370 prefixEnd_370 28146347002783121971 := by
  unfold tailWord_370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3373752166757009019641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8996672444685357385709 3373752166757009019641)
  ·
    refine ⟨2530314125067756764731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3373752166757009019641 2530314125067756764731)
    ·
      refine ⟨3795471187601635147097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2530314125067756764731 3795471187601635147097)
      ·
        refine ⟨2846603390701226360323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3795471187601635147097 2846603390701226360323)
        ·
          refine ⟨4269905086051839540485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2846603390701226360323 4269905086051839540485)
          ·
            refine ⟨800607203634719913841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4269905086051839540485 800607203634719913841)
            ·
              refine ⟨600455402726039935381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 800607203634719913841 600455402726039935381)
              ·
                refine ⟨28146347002783121971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 600455402726039935381 28146347002783121971)
                ·
                  rfl

theorem cell21_370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370 prefixEnd_370 := by exact prefixLift 370
  have htrace : WordTrace (prefixWord ++ tailWord_370) baseStart_370 baseEnd_370 := by
    simpa [prefixWord, tailWord_370, baseEnd_370] using wordTrace_append hprefix tailTrace_370
  have hstable : (prefixWord ++ tailWord_370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370).length < 2 ^ (prefixWord ++ tailWord_370).sum := by decide
  have hdescent : baseEnd_370 < baseStart_370 := by decide
  rcases family_descends (prefixWord ++ tailWord_370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373 : List Nat := [1, 3, 4, 1, 2, 1, 4, 1, 4]
def baseStart_373 : Nat := 118140960795 + 373 * 2 ^ 59
def prefixEnd_373 : Nat := 4983230072969 + 3 ^ 40 * 373 * 2
def baseEnd_373 : Nat := 85123681881010815907

theorem tailTrace_373 : CollatzResearch.WordTrace tailWord_373 prefixEnd_373 85123681881010815907 := by
  unfold tailWord_373
  simp only [CollatzResearch.WordTrace]
  refine ⟨13604427656159548437773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9069618437439698958515 13604427656159548437773)
  ·
    refine ⟨5101660371059830664165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13604427656159548437773 5101660371059830664165)
    ·
      refine ⟨956561319573718249531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5101660371059830664165 956561319573718249531)
      ·
        refine ⟨1434841979360577374297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 956561319573718249531 1434841979360577374297)
        ·
          refine ⟨1076131484520433030723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1434841979360577374297 1076131484520433030723)
          ·
            refine ⟨1614197226780649546085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076131484520433030723 1614197226780649546085)
            ·
              refine ⟨302661980021371789891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1614197226780649546085 302661980021371789891)
              ·
                refine ⟨453992970032057684837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302661980021371789891 453992970032057684837)
                ·
                  refine ⟨85123681881010815907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 453992970032057684837 85123681881010815907)
                  ·
                    rfl

theorem cell21_373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373 prefixEnd_373 := by exact prefixLift 373
  have htrace : WordTrace (prefixWord ++ tailWord_373) baseStart_373 baseEnd_373 := by
    simpa [prefixWord, tailWord_373, baseEnd_373] using wordTrace_append hprefix tailTrace_373
  have hstable : (prefixWord ++ tailWord_373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373).length < 2 ^ (prefixWord ++ tailWord_373).sum := by decide
  have hdescent : baseEnd_373 < baseStart_373 := by decide
  rcases family_descends (prefixWord ++ tailWord_373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418 : List Nat := [3, 3, 1, 2, 1, 1, 3, 4, 3]
def baseStart_418 : Nat := 118140960795 + 418 * 2 ^ 59
def prefixEnd_418 : Nat := 4983230072969 + 3 ^ 40 * 418 * 2
def baseEnd_418 : Nat := 95393294970932565815

theorem tailTrace_418 : CollatzResearch.WordTrace tailWord_418 prefixEnd_418 95393294970932565815 := by
  unfold tailWord_418
  simp only [CollatzResearch.WordTrace]
  refine ⟨3811428123283058456477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10163808328754822550605 3811428123283058456477)
  ·
    refine ⟨1429285546231146921179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3811428123283058456477 1429285546231146921179)
    ·
      refine ⟨2143928319346720381769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1429285546231146921179 2143928319346720381769)
      ·
        refine ⟨1607946239510040286327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2143928319346720381769 1607946239510040286327)
        ·
          refine ⟨2411919359265060429491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1607946239510040286327 2411919359265060429491)
          ·
            refine ⟨3617879038897590644237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2411919359265060429491 3617879038897590644237)
            ·
              refine ⟨1356704639586596491589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3617879038897590644237 1356704639586596491589)
              ·
                refine ⟨254382119922486842173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1356704639586596491589 254382119922486842173)
                ·
                  refine ⟨95393294970932565815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254382119922486842173 95393294970932565815)
                  ·
                    rfl

theorem cell21_418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_418 prefixEnd_418 := by exact prefixLift 418
  have htrace : WordTrace (prefixWord ++ tailWord_418) baseStart_418 baseEnd_418 := by
    simpa [prefixWord, tailWord_418, baseEnd_418] using wordTrace_append hprefix tailTrace_418
  have hstable : (prefixWord ++ tailWord_418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418).length < 2 ^ (prefixWord ++ tailWord_418).sum := by decide
  have hdescent : baseEnd_418 < baseStart_418 := by decide
  rcases family_descends (prefixWord ++ tailWord_418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466 : List Nat := [3, 2, 2, 4, 1, 2, 1, 2, 4]
def baseStart_466 : Nat := 118140960795 + 466 * 2 ^ 59
def prefixEnd_466 : Nat := 4983230072969 + 3 ^ 40 * 466 * 2
def baseEnd_466 : Nat := 106347548933515765717

theorem tailTrace_466 : CollatzResearch.WordTrace tailWord_466 prefixEnd_466 106347548933515765717 := by
  unfold tailWord_466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4249104079809107893313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11330944212824287715501 4249104079809107893313)
  ·
    refine ⟨3186828059856830919985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4249104079809107893313 3186828059856830919985)
    ·
      refine ⟨2390121044892623189989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3186828059856830919985 2390121044892623189989)
      ·
        refine ⟨448147695917366848123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2390121044892623189989 448147695917366848123)
        ·
          refine ⟨672221543876050272185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448147695917366848123 672221543876050272185)
          ·
            refine ⟨504166157907037704139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 672221543876050272185 504166157907037704139)
            ·
              refine ⟨756249236860556556209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504166157907037704139 756249236860556556209)
              ·
                refine ⟨567186927645417417157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 756249236860556556209 567186927645417417157)
                ·
                  refine ⟨106347548933515765717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 567186927645417417157 106347548933515765717)
                  ·
                    rfl

theorem cell21_466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_466 prefixEnd_466 := by exact prefixLift 466
  have htrace : WordTrace (prefixWord ++ tailWord_466) baseStart_466 baseEnd_466 := by
    simpa [prefixWord, tailWord_466, baseEnd_466] using wordTrace_append hprefix tailTrace_466
  have hstable : (prefixWord ++ tailWord_466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466).length < 2 ^ (prefixWord ++ tailWord_466).sum := by decide
  have hdescent : baseEnd_466 < baseStart_466 := by decide
  rcases family_descends (prefixWord ++ tailWord_466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477 : List Nat := [1, 4, 3, 1, 1, 1, 4, 1, 5]
def baseStart_477 : Nat := 118140960795 + 477 * 2 ^ 59
def prefixEnd_477 : Nat := 4983230072969 + 3 ^ 40 * 477 * 2
def baseEnd_477 : Nat := 108857898799941082361

theorem tailTrace_477 : CollatzResearch.WordTrace tailWord_477 prefixEnd_477 108857898799941082361 := by
  unfold tailWord_477
  simp only [CollatzResearch.WordTrace]
  refine ⟨17397619279385310223685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11598412852923540149123 17397619279385310223685)
  ·
    refine ⟨3262053614884745666941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17397619279385310223685 3262053614884745666941)
    ·
      refine ⟨1223270105581779625103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3262053614884745666941 1223270105581779625103)
      ·
        refine ⟨1834905158372669437655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1223270105581779625103 1834905158372669437655)
        ·
          refine ⟨2752357737559004156483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1834905158372669437655 2752357737559004156483)
          ·
            refine ⟨4128536606338506234725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2752357737559004156483 4128536606338506234725)
            ·
              refine ⟨774100613688469919011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4128536606338506234725 774100613688469919011)
              ·
                refine ⟨1161150920532704878517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774100613688469919011 1161150920532704878517)
                ·
                  refine ⟨108857898799941082361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1161150920532704878517 108857898799941082361)
                  ·
                    rfl

theorem cell21_477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_477 prefixEnd_477 := by exact prefixLift 477
  have htrace : WordTrace (prefixWord ++ tailWord_477) baseStart_477 baseEnd_477 := by
    simpa [prefixWord, tailWord_477, baseEnd_477] using wordTrace_append hprefix tailTrace_477
  have hstable : (prefixWord ++ tailWord_477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477).length < 2 ^ (prefixWord ++ tailWord_477).sum := by decide
  have hdescent : baseEnd_477 < baseStart_477 := by decide
  rcases family_descends (prefixWord ++ tailWord_477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 6]
def baseStart_525 : Nat := 118140960795 + 525 * 2 ^ 59
def prefixEnd_525 : Nat := 4983230072969 + 3 ^ 40 * 525 * 2
def baseEnd_525 : Nat := 119812152762524282263

theorem tailTrace_525 : CollatzResearch.WordTrace tailWord_525 prefixEnd_525 119812152762524282263 := by
  unfold tailWord_525
  simp only [CollatzResearch.WordTrace]
  refine ⟨19148323105489507971029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12765548736993005314019 19148323105489507971029)
  ·
    refine ⟨448788822784910343071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 19148323105489507971029 448788822784910343071)
    ·
      refine ⟨673183234177365514607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448788822784910343071 673183234177365514607)
      ·
        refine ⟨1009774851266048271911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673183234177365514607 1009774851266048271911)
        ·
          refine ⟨1514662276899072407867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009774851266048271911 1514662276899072407867)
          ·
            refine ⟨2271993415348608611801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514662276899072407867 2271993415348608611801)
            ·
              refine ⟨1703995061511456458851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2271993415348608611801 1703995061511456458851)
              ·
                refine ⟨2555992592267184688277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1703995061511456458851 2555992592267184688277)
                ·
                  refine ⟨119812152762524282263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2555992592267184688277 119812152762524282263)
                  ·
                    rfl

theorem cell21_525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_525 prefixEnd_525 := by exact prefixLift 525
  have htrace : WordTrace (prefixWord ++ tailWord_525) baseStart_525 baseEnd_525 := by
    simpa [prefixWord, tailWord_525, baseEnd_525] using wordTrace_append hprefix tailTrace_525
  have hstable : (prefixWord ++ tailWord_525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525).length < 2 ^ (prefixWord ++ tailWord_525).sum := by decide
  have hdescent : baseEnd_525 < baseStart_525 := by decide
  rcases family_descends (prefixWord ++ tailWord_525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612 : List Nat := [2, 3, 1, 1, 2, 2, 3, 2, 5]
def baseStart_612 : Nat := 118140960795 + 612 * 2 ^ 59
def prefixEnd_612 : Nat := 4983230072969 + 3 ^ 40 * 612 * 2
def baseEnd_612 : Nat := 139666738069706332085

theorem tailTrace_612 : CollatzResearch.WordTrace tailWord_612 prefixEnd_612 139666738069706332085 := by
  unfold tailWord_612
  simp only [CollatzResearch.WordTrace]
  refine ⟨11160736895151683194045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14880982526868910925393 11160736895151683194045)
  ·
    refine ⟨4185276335681881197767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11160736895151683194045 4185276335681881197767)
    ·
      refine ⟨6277914503522821796651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4185276335681881197767 6277914503522821796651)
      ·
        refine ⟨9416871755284232694977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6277914503522821796651 9416871755284232694977)
        ·
          refine ⟨7062653816463174521233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9416871755284232694977 7062653816463174521233)
          ·
            refine ⟨5296990362347380890925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7062653816463174521233 5296990362347380890925)
            ·
              refine ⟨1986371385880267834097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5296990362347380890925 1986371385880267834097)
              ·
                refine ⟨1489778539410200875573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1986371385880267834097 1489778539410200875573)
                ·
                  refine ⟨139666738069706332085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1489778539410200875573 139666738069706332085)
                  ·
                    rfl

theorem cell21_612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_612 prefixEnd_612 := by exact prefixLift 612
  have htrace : WordTrace (prefixWord ++ tailWord_612) baseStart_612 baseEnd_612 := by
    simpa [prefixWord, tailWord_612, baseEnd_612] using wordTrace_append hprefix tailTrace_612
  have hstable : (prefixWord ++ tailWord_612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612).length < 2 ^ (prefixWord ++ tailWord_612).sum := by decide
  have hdescent : baseEnd_612 < baseStart_612 := by decide
  rcases family_descends (prefixWord ++ tailWord_612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643 : List Nat := [1, 1, 1, 3, 3, 1, 5, 2, 4]
def baseStart_643 : Nat := 118140960795 + 643 * 2 ^ 59
def prefixEnd_643 : Nat := 4983230072969 + 3 ^ 40 * 643 * 2
def baseEnd_643 : Nat := 146741360420541315355

theorem tailTrace_643 : CollatzResearch.WordTrace tailWord_643 prefixEnd_643 146741360420541315355 := by
  unfold tailWord_643
  simp only [CollatzResearch.WordTrace]
  refine ⟨23452136677995660766583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15634757785330440511055 23452136677995660766583)
  ·
    refine ⟨35178205016993491149875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23452136677995660766583 35178205016993491149875)
    ·
      refine ⟨52767307525490236724813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35178205016993491149875 52767307525490236724813)
      ·
        refine ⟨19787740322058838771805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52767307525490236724813 19787740322058838771805)
        ·
          refine ⟨7420402620772064539427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19787740322058838771805 7420402620772064539427)
          ·
            refine ⟨11130603931158096809141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7420402620772064539427 11130603931158096809141)
            ·
              refine ⟨1043494118546071575857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11130603931158096809141 1043494118546071575857)
              ·
                refine ⟨782620588909553681893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1043494118546071575857 782620588909553681893)
                ·
                  refine ⟨146741360420541315355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 782620588909553681893 146741360420541315355)
                  ·
                    rfl

theorem cell21_643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 4].length) (baseStart_643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_643 prefixEnd_643 := by exact prefixLift 643
  have htrace : WordTrace (prefixWord ++ tailWord_643) baseStart_643 baseEnd_643 := by
    simpa [prefixWord, tailWord_643, baseEnd_643] using wordTrace_append hprefix tailTrace_643
  have hstable : (prefixWord ++ tailWord_643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643).length < 2 ^ (prefixWord ++ tailWord_643).sum := by decide
  have hdescent : baseEnd_643 < baseStart_643 := by decide
  rcases family_descends (prefixWord ++ tailWord_643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756 : List Nat := [2, 6, 1, 1, 2, 1, 1, 4, 3]
def baseStart_756 : Nat := 118140960795 + 756 * 2 ^ 59
def prefixEnd_756 : Nat := 4983230072969 + 3 ^ 40 * 756 * 2
def baseEnd_756 : Nat := 172529499957455931791

theorem tailTrace_756 : CollatzResearch.WordTrace tailWord_756 prefixEnd_756 172529499957455931791 := by
  unfold tailWord_756
  simp only [CollatzResearch.WordTrace]
  refine ⟨13786792634307979815061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18382390179077306420081 13786792634307979815061)
  ·
    refine ⟨646255904733186553831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13786792634307979815061 646255904733186553831)
    ·
      refine ⟨969383857099779830747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 646255904733186553831 969383857099779830747)
      ·
        refine ⟨1454075785649669746121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 969383857099779830747 1454075785649669746121)
        ·
          refine ⟨1090556839237252309591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1454075785649669746121 1090556839237252309591)
          ·
            refine ⟨1635835258855878464387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090556839237252309591 1635835258855878464387)
            ·
              refine ⟨2453752888283817696581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1635835258855878464387 2453752888283817696581)
              ·
                refine ⟨460078666553215818109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2453752888283817696581 460078666553215818109)
                ·
                  refine ⟨172529499957455931791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 460078666553215818109 172529499957455931791)
                  ·
                    rfl

theorem cell21_756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_756 prefixEnd_756 := by exact prefixLift 756
  have htrace : WordTrace (prefixWord ++ tailWord_756) baseStart_756 baseEnd_756 := by
    simpa [prefixWord, tailWord_756, baseEnd_756] using wordTrace_append hprefix tailTrace_756
  have hstable : (prefixWord ++ tailWord_756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756).length < 2 ^ (prefixWord ++ tailWord_756).sum := by decide
  have hdescent : baseEnd_756 < baseStart_756 := by decide
  rcases family_descends (prefixWord ++ tailWord_756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829 : List Nat := [1, 4, 1, 4, 2, 1, 3, 1, 4]
def baseStart_829 : Nat := 118140960795 + 829 * 2 ^ 59
def prefixEnd_829 : Nat := 4983230072969 + 3 ^ 40 * 829 * 2
def baseEnd_829 : Nat := 189189094525551214975

theorem tailTrace_829 : CollatzResearch.WordTrace tailWord_829 prefixEnd_829 189189094525551214975 := by
  unfold tailWord_829
  simp only [CollatzResearch.WordTrace]
  refine ⟨30236114004149427037541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20157409336099618025027 30236114004149427037541)
  ·
    refine ⟨5669271375778017569539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30236114004149427037541 5669271375778017569539)
    ·
      refine ⟨8503907063667026354309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5669271375778017569539 8503907063667026354309)
      ·
        refine ⟨1594482574437567441433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8503907063667026354309 1594482574437567441433)
        ·
          refine ⟨1195861930828175581075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1594482574437567441433 1195861930828175581075)
          ·
            refine ⟨1793792896242263371613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1195861930828175581075 1793792896242263371613)
            ·
              refine ⟨672672336090848764355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1793792896242263371613 672672336090848764355)
              ·
                refine ⟨1009008504136273146533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672672336090848764355 1009008504136273146533)
                ·
                  refine ⟨189189094525551214975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1009008504136273146533 189189094525551214975)
                  ·
                    rfl

theorem cell21_829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829 prefixEnd_829 := by exact prefixLift 829
  have htrace : WordTrace (prefixWord ++ tailWord_829) baseStart_829 baseEnd_829 := by
    simpa [prefixWord, tailWord_829, baseEnd_829] using wordTrace_append hprefix tailTrace_829
  have hstable : (prefixWord ++ tailWord_829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829).length < 2 ^ (prefixWord ++ tailWord_829).sum := by decide
  have hdescent : baseEnd_829 < baseStart_829 := by decide
  rcases family_descends (prefixWord ++ tailWord_829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857 : List Nat := [1, 2, 1, 2, 2, 4, 3, 3, 3]
def baseStart_857 : Nat := 118140960795 + 857 * 2 ^ 59
def prefixEnd_857 : Nat := 4983230072969 + 3 ^ 40 * 857 * 2
def baseEnd_857 : Nat := 195579076003724748251

theorem tailTrace_857 : CollatzResearch.WordTrace tailWord_857 prefixEnd_857 195579076003724748251 := by
  unfold tailWord_857
  simp only [CollatzResearch.WordTrace]
  refine ⟨31257357902710209056825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20838238601806806037883 31257357902710209056825)
  ·
    refine ⟨23443018427032656792619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31257357902710209056825 23443018427032656792619)
    ·
      refine ⟨35164527640548985188929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23443018427032656792619 35164527640548985188929)
      ·
        refine ⟨26373395730411738891697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35164527640548985188929 26373395730411738891697)
        ·
          refine ⟨19780046797808804168773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26373395730411738891697 19780046797808804168773)
          ·
            refine ⟨3708758774589150781645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19780046797808804168773 3708758774589150781645)
            ·
              refine ⟨1390784540470931543117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3708758774589150781645 1390784540470931543117)
              ·
                refine ⟨521544202676599328669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1390784540470931543117 521544202676599328669)
                ·
                  refine ⟨195579076003724748251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 521544202676599328669 195579076003724748251)
                  ·
                    rfl

theorem cell21_857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 3].length) (baseStart_857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_857 prefixEnd_857 := by exact prefixLift 857
  have htrace : WordTrace (prefixWord ++ tailWord_857) baseStart_857 baseEnd_857 := by
    simpa [prefixWord, tailWord_857, baseEnd_857] using wordTrace_append hprefix tailTrace_857
  have hstable : (prefixWord ++ tailWord_857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857).length < 2 ^ (prefixWord ++ tailWord_857).sum := by decide
  have hdescent : baseEnd_857 < baseStart_857 := by decide
  rcases family_descends (prefixWord ++ tailWord_857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885 : List Nat := [1, 3, 4, 1, 1, 2, 1, 8]
def baseStart_885 : Nat := 118140960795 + 885 * 2 ^ 59
def prefixEnd_885 : Nat := 4983230072969 + 3 ^ 40 * 885 * 2
def baseEnd_885 : Nat := 67323019160632760509

theorem tailTrace_885 : CollatzResearch.WordTrace tailWord_885 prefixEnd_885 67323019160632760509 := by
  unfold tailWord_885
  simp only [CollatzResearch.WordTrace]
  refine ⟨32278601801270991076109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21519067867513994050739 32278601801270991076109)
  ·
    refine ⟨12104475675476621653541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32278601801270991076109 12104475675476621653541)
    ·
      refine ⟨2269589189151866560039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12104475675476621653541 2269589189151866560039)
      ·
        refine ⟨3404383783727799840059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2269589189151866560039 3404383783727799840059)
        ·
          refine ⟨5106575675591699760089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3404383783727799840059 5106575675591699760089)
          ·
            refine ⟨3829931756693774820067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5106575675591699760089 3829931756693774820067)
            ·
              refine ⟨5744897635040662230101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3829931756693774820067 5744897635040662230101)
              ·
                refine ⟨67323019160632760509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5744897635040662230101 67323019160632760509)
                ·
                  rfl

theorem cell21_885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 8].length) (baseStart_885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885 prefixEnd_885 := by exact prefixLift 885
  have htrace : WordTrace (prefixWord ++ tailWord_885) baseStart_885 baseEnd_885 := by
    simpa [prefixWord, tailWord_885, baseEnd_885] using wordTrace_append hprefix tailTrace_885
  have hstable : (prefixWord ++ tailWord_885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885).length < 2 ^ (prefixWord ++ tailWord_885).sum := by decide
  have hdescent : baseEnd_885 < baseStart_885 := by decide
  rcases family_descends (prefixWord ++ tailWord_885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 7]
def baseStart_899 : Nat := 118140960795 + 899 * 2 ^ 59
def prefixEnd_899 : Nat := 4983230072969 + 3 ^ 40 * 899 * 2
def baseEnd_899 : Nat := 205164048220985048165

theorem tailTrace_899 : CollatzResearch.WordTrace tailWord_899 prefixEnd_899 205164048220985048165 := by
  unfold tailWord_899
  simp only [CollatzResearch.WordTrace]
  refine ⟨32789223750551382085751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21859482500367588057167 32789223750551382085751)
  ·
    refine ⟨49183835625827073128627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32789223750551382085751 49183835625827073128627)
    ·
      refine ⟨73775753438740609692941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49183835625827073128627 73775753438740609692941)
      ·
        refine ⟨27665907539527728634853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73775753438740609692941 27665907539527728634853)
        ·
          refine ⟨5187357663661449119035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27665907539527728634853 5187357663661449119035)
          ·
            refine ⟨7781036495492173678553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5187357663661449119035 7781036495492173678553)
            ·
              refine ⟨5835777371619130258915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7781036495492173678553 5835777371619130258915)
              ·
                refine ⟨8753666057428695388373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5835777371619130258915 8753666057428695388373)
                ·
                  refine ⟨205164048220985048165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8753666057428695388373 205164048220985048165)
                  ·
                    rfl

theorem cell21_899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 7].length) (baseStart_899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_899 prefixEnd_899 := by exact prefixLift 899
  have htrace : WordTrace (prefixWord ++ tailWord_899) baseStart_899 baseEnd_899 := by
    simpa [prefixWord, tailWord_899, baseEnd_899] using wordTrace_append hprefix tailTrace_899
  have hstable : (prefixWord ++ tailWord_899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899).length < 2 ^ (prefixWord ++ tailWord_899).sum := by decide
  have hdescent : baseEnd_899 < baseStart_899 := by decide
  rcases family_descends (prefixWord ++ tailWord_899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981 : List Nat := [1, 3, 2, 3, 4, 1, 1, 2, 4]
def baseStart_981 : Nat := 118140960795 + 981 * 2 ^ 59
def prefixEnd_981 : Nat := 4983230072969 + 3 ^ 40 * 981 * 2
def baseEnd_981 : Nat := 223877565407064681331

theorem tailTrace_981 : CollatzResearch.WordTrace tailWord_981 prefixEnd_981 223877565407064681331 := by
  unfold tailWord_981
  simp only [CollatzResearch.WordTrace]
  refine ⟨35780009453479386570797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23853339635652924380531 35780009453479386570797)
  ·
    refine ⟨13417503545054769964049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35780009453479386570797 13417503545054769964049)
    ·
      refine ⟨10063127658791077473037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13417503545054769964049 10063127658791077473037)
      ·
        refine ⟨3773672872046654052389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10063127658791077473037 3773672872046654052389)
        ·
          refine ⟨707563663508747634823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3773672872046654052389 707563663508747634823)
          ·
            refine ⟨1061345495263121452235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707563663508747634823 1061345495263121452235)
            ·
              refine ⟨1592018242894682178353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061345495263121452235 1592018242894682178353)
              ·
                refine ⟨1194013682171011633765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1592018242894682178353 1194013682171011633765)
                ·
                  refine ⟨223877565407064681331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1194013682171011633765 223877565407064681331)
                  ·
                    rfl

theorem cell21_981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981 prefixEnd_981 := by exact prefixLift 981
  have htrace : WordTrace (prefixWord ++ tailWord_981) baseStart_981 baseEnd_981 := by
    simpa [prefixWord, tailWord_981, baseEnd_981] using wordTrace_append hprefix tailTrace_981
  have hstable : (prefixWord ++ tailWord_981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981).length < 2 ^ (prefixWord ++ tailWord_981).sum := by decide
  have hdescent : baseEnd_981 < baseStart_981 := by decide
  rcases family_descends (prefixWord ++ tailWord_981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 7]
def baseStart_1127 : Nat := 118140960795 + 1127 * 2 ^ 59
def prefixEnd_1127 : Nat := 4983230072969 + 3 ^ 40 * 1127 * 2
def baseEnd_1127 : Nat := 257196754543255247699

theorem tailTrace_1127 : CollatzResearch.WordTrace tailWord_1127 prefixEnd_1127 257196754543255247699 := by
  unfold tailWord_1127
  simp only [CollatzResearch.WordTrace]
  refine ⟨41105066924546321385635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27403377949697547590423 41105066924546321385635)
  ·
    refine ⟨61657600386819482078453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41105066924546321385635 61657600386819482078453)
    ·
      refine ⟨5780400036264326444855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61657600386819482078453 5780400036264326444855)
      ·
        refine ⟨8670600054396489667283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5780400036264326444855 8670600054396489667283)
        ·
          refine ⟨13005900081594734500925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8670600054396489667283 13005900081594734500925)
          ·
            refine ⟨4877212530598025437847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13005900081594734500925 4877212530598025437847)
            ·
              refine ⟨7315818795897038156771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4877212530598025437847 7315818795897038156771)
              ·
                refine ⟨10973728193845557235157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7315818795897038156771 10973728193845557235157)
                ·
                  refine ⟨257196754543255247699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10973728193845557235157 257196754543255247699)
                  ·
                    rfl

theorem cell21_1127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 7].length) (baseStart_1127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1127 prefixEnd_1127 := by exact prefixLift 1127
  have htrace : WordTrace (prefixWord ++ tailWord_1127) baseStart_1127 baseEnd_1127 := by
    simpa [prefixWord, tailWord_1127, baseEnd_1127] using wordTrace_append hprefix tailTrace_1127
  have hstable : (prefixWord ++ tailWord_1127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127).length < 2 ^ (prefixWord ++ tailWord_1127).sum := by decide
  have hdescent : baseEnd_1127 < baseStart_1127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130 : List Nat := [3, 1, 3, 2, 2, 2, 3, 5]
def baseStart_1130 : Nat := 118140960795 + 1130 * 2 ^ 59
def prefixEnd_1130 : Nat := 4983230072969 + 3 ^ 40 * 1130 * 2
def baseEnd_1130 : Nat := 85960465138638899231

theorem tailTrace_1130 : CollatzResearch.WordTrace tailWord_1130 prefixEnd_1130 85960465138638899231 := by
  unfold tailWord_1130
  simp only [CollatzResearch.WordTrace]
  refine ⟨10303621478419458436211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27476323942451889163229 10303621478419458436211)
  ·
    refine ⟨15455432217629187654317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10303621478419458436211 15455432217629187654317)
    ·
      refine ⟨5795787081610945370369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15455432217629187654317 5795787081610945370369)
      ·
        refine ⟨4346840311208209027777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5795787081610945370369 4346840311208209027777)
        ·
          refine ⟨3260130233406156770833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4346840311208209027777 3260130233406156770833)
          ·
            refine ⟨2445097675054617578125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3260130233406156770833 2445097675054617578125)
            ·
              refine ⟨916911628145481591797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2445097675054617578125 916911628145481591797)
              ·
                refine ⟨85960465138638899231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 916911628145481591797 85960465138638899231)
                ·
                  rfl

theorem cell21_1130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_1130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1130 prefixEnd_1130 := by exact prefixLift 1130
  have htrace : WordTrace (prefixWord ++ tailWord_1130) baseStart_1130 baseEnd_1130 := by
    simpa [prefixWord, tailWord_1130, baseEnd_1130] using wordTrace_append hprefix tailTrace_1130
  have hstable : (prefixWord ++ tailWord_1130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130).length < 2 ^ (prefixWord ++ tailWord_1130).sum := by decide
  have hdescent : baseEnd_1130 < baseStart_1130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144 : List Nat := [2, 1, 2, 1, 1, 1, 5, 5, 3]
def baseStart_1144 : Nat := 118140960795 + 1144 * 2 ^ 59
def prefixEnd_1144 : Nat := 4983230072969 + 3 ^ 40 * 1144 * 2
def baseEnd_1144 : Nat := 261076386155003464331

theorem tailTrace_1144 : CollatzResearch.WordTrace tailWord_1144 prefixEnd_1144 261076386155003464331 := by
  unfold tailWord_1144
  simp only [CollatzResearch.WordTrace]
  refine ⟨20862553931479112377243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27816738575305483169657 20862553931479112377243)
  ·
    refine ⟨31293830897218668565865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20862553931479112377243 31293830897218668565865)
    ·
      refine ⟨23470373172914001424399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31293830897218668565865 23470373172914001424399)
      ·
        refine ⟨35205559759371002136599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23470373172914001424399 35205559759371002136599)
        ·
          refine ⟨52808339639056503204899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35205559759371002136599 52808339639056503204899)
          ·
            refine ⟨79212509458584754807349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52808339639056503204899 79212509458584754807349)
            ·
              refine ⟨7426172761742320763189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79212509458584754807349 7426172761742320763189)
              ·
                refine ⟨696203696413342571549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7426172761742320763189 696203696413342571549)
                ·
                  refine ⟨261076386155003464331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696203696413342571549 261076386155003464331)
                  ·
                    rfl

theorem cell21_1144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 3].length) (baseStart_1144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1144 prefixEnd_1144 := by exact prefixLift 1144
  have htrace : WordTrace (prefixWord ++ tailWord_1144) baseStart_1144 baseEnd_1144 := by
    simpa [prefixWord, tailWord_1144, baseEnd_1144] using wordTrace_append hprefix tailTrace_1144
  have hstable : (prefixWord ++ tailWord_1144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144).length < 2 ^ (prefixWord ++ tailWord_1144).sum := by decide
  have hdescent : baseEnd_1144 < baseStart_1144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189 : List Nat := [1, 3, 1, 2, 1, 4, 4, 5]
def baseStart_1189 : Nat := 118140960795 + 1189 * 2 ^ 59
def prefixEnd_1189 : Nat := 4983230072969 + 3 ^ 40 * 1189 * 2
def baseEnd_1189 : Nat := 90448666414975071413

theorem tailTrace_1189 : CollatzResearch.WordTrace tailWord_1189 prefixEnd_1189 90448666414975071413 := by
  unfold tailWord_1189
  simp only [CollatzResearch.WordTrace]
  refine ⟨43366392699930910142621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28910928466620606761747 43366392699930910142621)
  ·
    refine ⟨16262397262474091303483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43366392699930910142621 16262397262474091303483)
    ·
      refine ⟨24393595893711136955225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16262397262474091303483 24393595893711136955225)
      ·
        refine ⟨18295196920283352716419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24393595893711136955225 18295196920283352716419)
        ·
          refine ⟨27442795380425029074629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18295196920283352716419 27442795380425029074629)
          ·
            refine ⟨5145524133829692951493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27442795380425029074629 5145524133829692951493)
            ·
              refine ⟨964785775093067428405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5145524133829692951493 964785775093067428405)
              ·
                refine ⟨90448666414975071413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 964785775093067428405 90448666414975071413)
                ·
                  rfl

theorem cell21_1189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 5].length) (baseStart_1189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189 prefixEnd_1189 := by exact prefixLift 1189
  have htrace : WordTrace (prefixWord ++ tailWord_1189) baseStart_1189 baseEnd_1189 := by
    simpa [prefixWord, tailWord_1189, baseEnd_1189] using wordTrace_append hprefix tailTrace_1189
  have hstable : (prefixWord ++ tailWord_1189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189).length < 2 ^ (prefixWord ++ tailWord_1189).sum := by decide
  have hdescent : baseEnd_1189 < baseStart_1189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248 : List Nat := [2, 1, 1, 3, 1, 4, 2, 7]
def baseStart_1248 : Nat := 118140960795 + 1248 * 2 ^ 59
def prefixEnd_1248 : Nat := 4983230072969 + 3 ^ 40 * 1248 * 2
def baseEnd_1248 : Nat := 94936867691311243595

theorem tailTrace_1248 : CollatzResearch.WordTrace tailWord_1248 prefixEnd_1248 94936867691311243595 := by
  unfold tailWord_1248
  simp only [CollatzResearch.WordTrace]
  refine ⟨22759149743091993270199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30345532990789324360265 22759149743091993270199)
  ·
    refine ⟨34138724614637989905299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22759149743091993270199 34138724614637989905299)
    ·
      refine ⟨51208086921956984857949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34138724614637989905299 51208086921956984857949)
      ·
        refine ⟨19203032595733869321731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51208086921956984857949 19203032595733869321731)
        ·
          refine ⟨28804548893600803982597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19203032595733869321731 28804548893600803982597)
          ·
            refine ⟨5400852917550150746737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28804548893600803982597 5400852917550150746737)
            ·
              refine ⟨4050639688162613060053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5400852917550150746737 4050639688162613060053)
              ·
                refine ⟨94936867691311243595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4050639688162613060053 94936867691311243595)
                ·
                  rfl

theorem cell21_1248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 7].length) (baseStart_1248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1248 prefixEnd_1248 := by exact prefixLift 1248
  have htrace : WordTrace (prefixWord ++ tailWord_1248) baseStart_1248 baseEnd_1248 := by
    simpa [prefixWord, tailWord_1248, baseEnd_1248] using wordTrace_append hprefix tailTrace_1248
  have hstable : (prefixWord ++ tailWord_1248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248).length < 2 ^ (prefixWord ++ tailWord_1248).sum := by decide
  have hdescent : baseEnd_1248 < baseStart_1248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 6]
def baseStart_1369 : Nat := 118140960795 + 1369 * 2 ^ 59
def prefixEnd_1369 : Nat := 4983230072969 + 3 ^ 40 * 1369 * 2
def baseEnd_1369 : Nat := 312424451604612213871

theorem tailTrace_1369 : CollatzResearch.WordTrace tailWord_1369 prefixEnd_1369 312424451604612213871 := by
  unfold tailWord_1369
  simp only [CollatzResearch.WordTrace]
  refine ⟨49931532047821651695161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33287688031881101130107 49931532047821651695161)
  ·
    refine ⟨37448649035866238771371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49931532047821651695161 37448649035866238771371)
    ·
      refine ⟨56172973553799358157057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37448649035866238771371 56172973553799358157057)
      ·
        refine ⟨42129730165349518617793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56172973553799358157057 42129730165349518617793)
        ·
          refine ⟨31597297624012138963345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42129730165349518617793 31597297624012138963345)
          ·
            refine ⟨23697973218009104222509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31597297624012138963345 23697973218009104222509)
            ·
              refine ⟨8886739956753414083441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23697973218009104222509 8886739956753414083441)
              ·
                refine ⟨6665054967565060562581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8886739956753414083441 6665054967565060562581)
                ·
                  refine ⟨312424451604612213871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6665054967565060562581 312424451604612213871)
                  ·
                    rfl

theorem cell21_1369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_1369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1369 prefixEnd_1369 := by exact prefixLift 1369
  have htrace : WordTrace (prefixWord ++ tailWord_1369) baseStart_1369 baseEnd_1369 := by
    simpa [prefixWord, tailWord_1369, baseEnd_1369] using wordTrace_append hprefix tailTrace_1369
  have hstable : (prefixWord ++ tailWord_1369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369).length < 2 ^ (prefixWord ++ tailWord_1369).sum := by decide
  have hdescent : baseEnd_1369 < baseStart_1369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507 : List Nat := [1, 1, 1, 6, 2, 1, 1, 3, 5]
def baseStart_1507 : Nat := 118140960795 + 1507 * 2 ^ 59
def prefixEnd_1507 : Nat := 4983230072969 + 3 ^ 40 * 1507 * 2
def baseEnd_1507 : Nat := 343917931747038913589

theorem tailTrace_1507 : CollatzResearch.WordTrace tailWord_1507 prefixEnd_1507 343917931747038913589 := by
  unfold tailWord_1507
  simp only [CollatzResearch.WordTrace]
  refine ⟨54964805547871220218775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36643203698580813479183 54964805547871220218775)
  ·
    refine ⟨82447208321806830328163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54964805547871220218775 82447208321806830328163)
    ·
      refine ⟨123670812482710245492245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82447208321806830328163 123670812482710245492245)
      ·
        refine ⟨5797069335127042757449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 123670812482710245492245 5797069335127042757449)
        ·
          refine ⟨4347802001345282068087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5797069335127042757449 4347802001345282068087)
          ·
            refine ⟨6521703002017923102131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4347802001345282068087 6521703002017923102131)
            ·
              refine ⟨9782554503026884653197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6521703002017923102131 9782554503026884653197)
              ·
                refine ⟨3668457938635081744949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9782554503026884653197 3668457938635081744949)
                ·
                  refine ⟨343917931747038913589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3668457938635081744949 343917931747038913589)
                  ·
                    rfl

theorem cell21_1507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 5].length) (baseStart_1507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1507 prefixEnd_1507 := by exact prefixLift 1507
  have htrace : WordTrace (prefixWord ++ tailWord_1507) baseStart_1507 baseEnd_1507 := by
    simpa [prefixWord, tailWord_1507, baseEnd_1507] using wordTrace_append hprefix tailTrace_1507
  have hstable : (prefixWord ++ tailWord_1507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507).length < 2 ^ (prefixWord ++ tailWord_1507).sum := by decide
  have hdescent : baseEnd_1507 < baseStart_1507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741 : List Nat := [1, 6, 2, 1, 1, 3, 2, 1, 4]
def baseStart_1741 : Nat := 118140960795 + 1741 * 2 ^ 59
def prefixEnd_1741 : Nat := 4983230072969 + 3 ^ 40 * 1741 * 2
def baseEnd_1741 : Nat := 397319919814632013111

theorem tailTrace_1741 : CollatzResearch.WordTrace tailWord_1741 prefixEnd_1741 397319919814632013111 := by
  unfold tailWord_1741
  simp only [CollatzResearch.WordTrace]
  refine ⟨63499486700129184237077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42332991133419456158051 63499486700129184237077)
  ·
    refine ⟨2976538439068555511113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63499486700129184237077 2976538439068555511113)
    ·
      refine ⟨2232403829301416633335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2976538439068555511113 2232403829301416633335)
      ·
        refine ⟨3348605743952124950003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2232403829301416633335 3348605743952124950003)
        ·
          refine ⟨5022908615928187425005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3348605743952124950003 5022908615928187425005)
          ·
            refine ⟨1883590730973070284377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5022908615928187425005 1883590730973070284377)
            ·
              refine ⟨1412693048229802713283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1883590730973070284377 1412693048229802713283)
              ·
                refine ⟨2119039572344704069925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412693048229802713283 2119039572344704069925)
                ·
                  refine ⟨397319919814632013111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2119039572344704069925 397319919814632013111)
                  ·
                    rfl

theorem cell21_1741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_1741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1741 prefixEnd_1741 := by exact prefixLift 1741
  have htrace : WordTrace (prefixWord ++ tailWord_1741) baseStart_1741 baseEnd_1741 := by
    simpa [prefixWord, tailWord_1741, baseEnd_1741] using wordTrace_append hprefix tailTrace_1741
  have hstable : (prefixWord ++ tailWord_1741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741).length < 2 ^ (prefixWord ++ tailWord_1741).sum := by decide
  have hdescent : baseEnd_1741 < baseStart_1741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828 : List Nat := [2, 3, 1, 3, 2, 1, 1, 5, 3]
def baseStart_1828 : Nat := 118140960795 + 1828 * 2 ^ 59
def prefixEnd_1828 : Nat := 4983230072969 + 3 ^ 40 * 1828 * 2
def baseEnd_1828 : Nat := 417174505121814062933

theorem tailTrace_1828 : CollatzResearch.WordTrace tailWord_1828 prefixEnd_1828 417174505121814062933 := by
  unfold tailWord_1828
  simp only [CollatzResearch.WordTrace]
  refine ⟨33336318692471521327069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44448424923295361769425 33336318692471521327069)
  ·
    refine ⟨12501119509676820497651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33336318692471521327069 12501119509676820497651)
    ·
      refine ⟨18751679264515230746477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12501119509676820497651 18751679264515230746477)
      ·
        refine ⟨7031879724193211529929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18751679264515230746477 7031879724193211529929)
        ·
          refine ⟨5273909793144908647447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7031879724193211529929 5273909793144908647447)
          ·
            refine ⟨7910864689717362971171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5273909793144908647447 7910864689717362971171)
            ·
              refine ⟨11866297034576044456757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7910864689717362971171 11866297034576044456757)
              ·
                refine ⟨1112465346991504167821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11866297034576044456757 1112465346991504167821)
                ·
                  refine ⟨417174505121814062933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112465346991504167821 417174505121814062933)
                  ·
                    rfl

theorem cell21_1828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_1828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1828 prefixEnd_1828 := by exact prefixLift 1828
  have htrace : WordTrace (prefixWord ++ tailWord_1828) baseStart_1828 baseEnd_1828 := by
    simpa [prefixWord, tailWord_1828, baseEnd_1828] using wordTrace_append hprefix tailTrace_1828
  have hstable : (prefixWord ++ tailWord_1828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828).length < 2 ^ (prefixWord ++ tailWord_1828).sum := by decide
  have hdescent : baseEnd_1828 < baseStart_1828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842 : List Nat := [3, 2, 1, 1, 3, 2, 3, 2, 4]
def baseStart_1842 : Nat := 118140960795 + 1842 * 2 ^ 59
def prefixEnd_1842 : Nat := 4983230072969 + 3 ^ 40 * 1842 * 2
def baseEnd_1842 : Nat := 420369495860900829571

theorem tailTrace_1842 : CollatzResearch.WordTrace tailWord_1842 prefixEnd_1842 420369495860900829571 := by
  unfold tailWord_1842
  simp only [CollatzResearch.WordTrace]
  refine ⟨16795814833555858415945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44788839556148955775853 16795814833555858415945)
  ·
    refine ⟨12596861125166893811959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16795814833555858415945 12596861125166893811959)
    ·
      refine ⟨18895291687750340717939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12596861125166893811959 18895291687750340717939)
      ·
        refine ⟨28342937531625511076909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18895291687750340717939 28342937531625511076909)
        ·
          refine ⟨10628601574359566653841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28342937531625511076909 10628601574359566653841)
          ·
            refine ⟨7971451180769674990381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10628601574359566653841 7971451180769674990381)
            ·
              refine ⟨2989294192788628121393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7971451180769674990381 2989294192788628121393)
              ·
                refine ⟨2241970644591471091045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2989294192788628121393 2241970644591471091045)
                ·
                  refine ⟨420369495860900829571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2241970644591471091045 420369495860900829571)
                  ·
                    rfl

theorem cell21_1842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_1842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1842 prefixEnd_1842 := by exact prefixLift 1842
  have htrace : WordTrace (prefixWord ++ tailWord_1842) baseStart_1842 baseEnd_1842 := by
    simpa [prefixWord, tailWord_1842, baseEnd_1842] using wordTrace_append hprefix tailTrace_1842
  have hstable : (prefixWord ++ tailWord_1842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842).length < 2 ^ (prefixWord ++ tailWord_1842).sum := by decide
  have hdescent : baseEnd_1842 < baseStart_1842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873 : List Nat := [1, 2, 2, 1, 5, 3, 2, 5]
def baseStart_1873 : Nat := 118140960795 + 1873 * 2 ^ 59
def prefixEnd_1873 : Nat := 4983230072969 + 3 ^ 40 * 1873 * 2
def baseEnd_1873 : Nat := 142481372737245270947

theorem tailTrace_1873 : CollatzResearch.WordTrace tailWord_1873 prefixEnd_1873 142481372737245270947 := by
  unfold tailWord_1873
  simp only [CollatzResearch.WordTrace]
  refine ⟨68313922221915728042273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45542614814610485361515 68313922221915728042273)
  ·
    refine ⟨51235441666436796031705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68313922221915728042273 51235441666436796031705)
    ·
      refine ⟨38426581249827597023779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51235441666436796031705 38426581249827597023779)
      ·
        refine ⟨57639871874741395535669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38426581249827597023779 57639871874741395535669)
        ·
          refine ⟨5403737988257005831469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57639871874741395535669 5403737988257005831469)
          ·
            refine ⟨2026401745596377186801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5403737988257005831469 2026401745596377186801)
            ·
              refine ⟨1519801309197282890101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026401745596377186801 1519801309197282890101)
              ·
                refine ⟨142481372737245270947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1519801309197282890101 142481372737245270947)
                ·
                  rfl

theorem cell21_1873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 5].length) (baseStart_1873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873 prefixEnd_1873 := by exact prefixLift 1873
  have htrace : WordTrace (prefixWord ++ tailWord_1873) baseStart_1873 baseEnd_1873 := by
    simpa [prefixWord, tailWord_1873, baseEnd_1873] using wordTrace_append hprefix tailTrace_1873
  have hstable : (prefixWord ++ tailWord_1873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873).length < 2 ^ (prefixWord ++ tailWord_1873).sum := by decide
  have hdescent : baseEnd_1873 < baseStart_1873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 6]
def baseStart_1901 : Nat := 118140960795 + 1901 * 2 ^ 59
def prefixEnd_1901 : Nat := 4983230072969 + 3 ^ 40 * 1901 * 2
def baseEnd_1901 : Nat := 433834099689909346117

theorem tailTrace_1901 : CollatzResearch.WordTrace tailWord_1901 prefixEnd_1901 433834099689909346117 := by
  unfold tailWord_1901
  simp only [CollatzResearch.WordTrace]
  refine ⟨69335166120476510061557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46223444080317673374371 69335166120476510061557)
  ·
    refine ⟨6500171823794672818271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69335166120476510061557 6500171823794672818271)
    ·
      refine ⟨9750257735692009227407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6500171823794672818271 9750257735692009227407)
      ·
        refine ⟨14625386603538013841111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9750257735692009227407 14625386603538013841111)
        ·
          refine ⟨21938079905307020761667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14625386603538013841111 21938079905307020761667)
          ·
            refine ⟨32907119857960531142501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21938079905307020761667 32907119857960531142501)
            ·
              refine ⟨6170084973367599589219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32907119857960531142501 6170084973367599589219)
              ·
                refine ⟨9255127460051399383829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6170084973367599589219 9255127460051399383829)
                ·
                  refine ⟨433834099689909346117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9255127460051399383829 433834099689909346117)
                  ·
                    rfl

theorem cell21_1901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_1901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901 prefixEnd_1901 := by exact prefixLift 1901
  have htrace : WordTrace (prefixWord ++ tailWord_1901) baseStart_1901 baseEnd_1901 := by
    simpa [prefixWord, tailWord_1901, baseEnd_1901] using wordTrace_append hprefix tailTrace_1901
  have hstable : (prefixWord ++ tailWord_1901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901).length < 2 ^ (prefixWord ++ tailWord_1901).sum := by decide
  have hdescent : baseEnd_1901 < baseStart_1901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977 : List Nat := [1, 2, 1, 4, 2, 1, 1, 5, 4]
def baseStart_1977 : Nat := 118140960795 + 1977 * 2 ^ 59
def prefixEnd_1977 : Nat := 4983230072969 + 3 ^ 40 * 1977 * 2
def baseEnd_1977 : Nat := 451178335130666079295

theorem tailTrace_1977 : CollatzResearch.WordTrace tailWord_1977 prefixEnd_1977 451178335130666079295 := by
  unfold tailWord_1977
  simp only [CollatzResearch.WordTrace]
  refine ⟨72107113845141489828185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48071409230094326552123 72107113845141489828185)
  ·
    refine ⟨54080335383856117371139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72107113845141489828185 54080335383856117371139)
    ·
      refine ⟨81120503075784176056709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54080335383856117371139 81120503075784176056709)
      ·
        refine ⟨15210094326709533010633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81120503075784176056709 15210094326709533010633)
        ·
          refine ⟨11407570745032149757975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15210094326709533010633 11407570745032149757975)
          ·
            refine ⟨17111356117548224636963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11407570745032149757975 17111356117548224636963)
            ·
              refine ⟨25667034176322336955445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17111356117548224636963 25667034176322336955445)
              ·
                refine ⟨2406284454030219089573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25667034176322336955445 2406284454030219089573)
                ·
                  refine ⟨451178335130666079295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2406284454030219089573 451178335130666079295)
                  ·
                    rfl

theorem cell21_1977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_1977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1977 prefixEnd_1977 := by exact prefixLift 1977
  have htrace : WordTrace (prefixWord ++ tailWord_1977) baseStart_1977 baseEnd_1977 := by
    simpa [prefixWord, tailWord_1977, baseEnd_1977] using wordTrace_append hprefix tailTrace_1977
  have hstable : (prefixWord ++ tailWord_1977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977).length < 2 ^ (prefixWord ++ tailWord_1977).sum := by decide
  have hdescent : baseEnd_1977 < baseStart_1977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980 : List Nat := [2, 2, 2, 5, 1, 1, 1, 2, 5]
def baseStart_1980 : Nat := 118140960795 + 1980 * 2 ^ 59
def prefixEnd_1980 : Nat := 4983230072969 + 3 ^ 40 * 1980 * 2
def baseEnd_1980 : Nat := 451862976003327529289

theorem tailTrace_1980 : CollatzResearch.WordTrace tailWord_1980 prefixEnd_1980 451862976003327529289 := by
  unfold tailWord_1980
  simp only [CollatzResearch.WordTrace]
  refine ⟨36108266417136501093697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48144355222848668124929 36108266417136501093697)
  ·
    refine ⟨27081199812852375820273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36108266417136501093697 27081199812852375820273)
    ·
      refine ⟨20310899859639281865205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27081199812852375820273 20310899859639281865205)
      ·
        refine ⟨1904146861841182674863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20310899859639281865205 1904146861841182674863)
        ·
          refine ⟨2856220292761774012295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1904146861841182674863 2856220292761774012295)
          ·
            refine ⟨4284330439142661018443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2856220292761774012295 4284330439142661018443)
            ·
              refine ⟨6426495658713991527665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4284330439142661018443 6426495658713991527665)
              ·
                refine ⟨4819871744035493645749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6426495658713991527665 4819871744035493645749)
                ·
                  refine ⟨451862976003327529289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4819871744035493645749 451862976003327529289)
                  ·
                    rfl

theorem cell21_1980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_1980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1980 prefixEnd_1980 := by exact prefixLift 1980
  have htrace : WordTrace (prefixWord ++ tailWord_1980) baseStart_1980 baseEnd_1980 := by
    simpa [prefixWord, tailWord_1980, baseEnd_1980] using wordTrace_append hprefix tailTrace_1980
  have hstable : (prefixWord ++ tailWord_1980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980).length < 2 ^ (prefixWord ++ tailWord_1980).sum := by decide
  have hdescent : baseEnd_1980 < baseStart_1980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087 : List Nat := [1, 1, 7, 1, 2, 1, 1, 3, 4]
def baseStart_2087 : Nat := 118140960795 + 2087 * 2 ^ 59
def prefixEnd_2087 : Nat := 4983230072969 + 3 ^ 40 * 2087 * 2
def baseEnd_2087 : Nat := 476281833794919245737

theorem tailTrace_2087 : CollatzResearch.WordTrace tailWord_2087 prefixEnd_2087 476281833794919245737 := by
  unfold tailWord_2087
  simp only [CollatzResearch.WordTrace]
  refine ⟨76119143446630276332515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50746095631086850888343 76119143446630276332515)
  ·
    refine ⟨114178715169945414498773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76119143446630276332515 114178715169945414498773)
    ·
      refine ⟨2676063636795595652315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 114178715169945414498773 2676063636795595652315)
      ·
        refine ⟨4014095455193393478473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2676063636795595652315 4014095455193393478473)
        ·
          refine ⟨3010571591395045108855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4014095455193393478473 3010571591395045108855)
          ·
            refine ⟨4515857387092567663283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010571591395045108855 4515857387092567663283)
            ·
              refine ⟨6773786080638851494925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4515857387092567663283 6773786080638851494925)
              ·
                refine ⟨2540169780239569310597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6773786080638851494925 2540169780239569310597)
                ·
                  refine ⟨476281833794919245737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2540169780239569310597 476281833794919245737)
                  ·
                    rfl

theorem cell21_2087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 4].length) (baseStart_2087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087 prefixEnd_2087 := by exact prefixLift 2087
  have htrace : WordTrace (prefixWord ++ tailWord_2087) baseStart_2087 baseEnd_2087 := by
    simpa [prefixWord, tailWord_2087, baseEnd_2087] using wordTrace_append hprefix tailTrace_2087
  have hstable : (prefixWord ++ tailWord_2087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087).length < 2 ^ (prefixWord ++ tailWord_2087).sum := by decide
  have hdescent : baseEnd_2087 < baseStart_2087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160 : List Nat := [2, 1, 1, 1, 5, 3, 3, 5]
def baseStart_2160 : Nat := 118140960795 + 2160 * 2 ^ 59
def prefixEnd_2160 : Nat := 4983230072969 + 3 ^ 40 * 2160 * 2
def baseEnd_2160 : Nat := 164313809454338176307

theorem tailTrace_2160 : CollatzResearch.WordTrace tailWord_2160 prefixEnd_2160 164313809454338176307 := by
  unfold tailWord_2160
  simp only [CollatzResearch.WordTrace]
  refine ⟨39390836091081871869967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52521114788109162493289 39390836091081871869967)
  ·
    refine ⟨59086254136622807804951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39390836091081871869967 59086254136622807804951)
    ·
      refine ⟨88629381204934211707427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59086254136622807804951 88629381204934211707427)
      ·
        refine ⟨132944071807401317561141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88629381204934211707427 132944071807401317561141)
        ·
          refine ⟨12463506731943873521357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132944071807401317561141 12463506731943873521357)
          ·
            refine ⟨4673815024478952570509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12463506731943873521357 4673815024478952570509)
            ·
              refine ⟨1752680634179607213941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4673815024478952570509 1752680634179607213941)
              ·
                refine ⟨164313809454338176307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1752680634179607213941 164313809454338176307)
                ·
                  rfl

theorem cell21_2160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 5].length) (baseStart_2160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2160 prefixEnd_2160 := by exact prefixLift 2160
  have htrace : WordTrace (prefixWord ++ tailWord_2160) baseStart_2160 baseEnd_2160 := by
    simpa [prefixWord, tailWord_2160, baseEnd_2160] using wordTrace_append hprefix tailTrace_2160
  have hstable : (prefixWord ++ tailWord_2160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160).length < 2 ^ (prefixWord ++ tailWord_2160).sum := by decide
  have hdescent : baseEnd_2160 < baseStart_2160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2225 : List Nat := [1, 2, 2, 5, 2, 2, 1, 3, 3]
def baseStart_2225 : Nat := 118140960795 + 2225 * 2 ^ 59
def prefixEnd_2225 : Nat := 4983230072969 + 3 ^ 40 * 2225 * 2
def baseEnd_2225 : Nat := 507775313937345945455

theorem tailTrace_2225 : CollatzResearch.WordTrace tailWord_2225 prefixEnd_2225 507775313937345945455 := by
  unfold tailWord_2225
  simp only [CollatzResearch.WordTrace]
  refine ⟨81152416946679844856129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54101611297786563237419 81152416946679844856129)
  ·
    refine ⟨60864312710009883642097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81152416946679844856129 60864312710009883642097)
    ·
      refine ⟨45648234532507412731573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60864312710009883642097 45648234532507412731573)
      ·
        refine ⟨4279521987422569943585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45648234532507412731573 4279521987422569943585)
        ·
          refine ⟨3209641490566927457689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4279521987422569943585 3209641490566927457689)
          ·
            refine ⟨2407231117925195593267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3209641490566927457689 2407231117925195593267)
            ·
              refine ⟨3610846676887793389901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2407231117925195593267 3610846676887793389901)
              ·
                refine ⟨1354067503832922521213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3610846676887793389901 1354067503832922521213)
                ·
                  refine ⟨507775313937345945455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1354067503832922521213 507775313937345945455)
                  ·
                    rfl

theorem cell21_2225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 3].length) (baseStart_2225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2225 prefixEnd_2225 := by exact prefixLift 2225
  have htrace : WordTrace (prefixWord ++ tailWord_2225) baseStart_2225 baseEnd_2225 := by
    simpa [prefixWord, tailWord_2225, baseEnd_2225] using wordTrace_append hprefix tailTrace_2225
  have hstable : (prefixWord ++ tailWord_2225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2225).length < 2 ^ (prefixWord ++ tailWord_2225).sum := by decide
  have hdescent : baseEnd_2225 < baseStart_2225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2236 : List Nat := [2, 2, 2, 3, 3, 2, 7]
def baseStart_2236 : Nat := 118140960795 + 2236 * 2 ^ 59
def prefixEnd_2236 : Nat := 4983230072969 + 3 ^ 40 * 2236 * 2
def baseEnd_2236 : Nat := 56698407089307918011

theorem tailTrace_2236 : CollatzResearch.WordTrace tailWord_2236 prefixEnd_2236 56698407089307918011 := by
  unfold tailWord_2236
  simp only [CollatzResearch.WordTrace]
  refine ⟨40776809953414361753281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54369079937885815671041 40776809953414361753281)
  ·
    refine ⟨30582607465060771314961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40776809953414361753281 30582607465060771314961)
    ·
      refine ⟨22936955598795578486221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30582607465060771314961 22936955598795578486221)
      ·
        refine ⟨8601358349548341932333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22936955598795578486221 8601358349548341932333)
        ·
          refine ⟨3225509381080628224625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8601358349548341932333 3225509381080628224625)
          ·
            refine ⟨2419132035810471168469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3225509381080628224625 2419132035810471168469)
            ·
              refine ⟨56698407089307918011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2419132035810471168469 56698407089307918011)
              ·
                rfl

theorem cell21_2236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 7].length) (baseStart_2236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2236 prefixEnd_2236 := by exact prefixLift 2236
  have htrace : WordTrace (prefixWord ++ tailWord_2236) baseStart_2236 baseEnd_2236 := by
    simpa [prefixWord, tailWord_2236, baseEnd_2236] using wordTrace_append hprefix tailTrace_2236
  have hstable : (prefixWord ++ tailWord_2236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2236).length < 2 ^ (prefixWord ++ tailWord_2236).sum := by decide
  have hdescent : baseEnd_2236 < baseStart_2236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2312 : List Nat := [2, 1, 3, 2, 3, 3, 1, 6]
def baseStart_2312 : Nat := 118140960795 + 2312 * 2 ^ 59
def prefixEnd_2312 : Nat := 4983230072969 + 3 ^ 40 * 2312 * 2
def baseEnd_2312 : Nat := 175876633081509331759

theorem tailTrace_2312 : CollatzResearch.WordTrace tailWord_2312 prefixEnd_2312 175876633081509331759 := by
  unfold tailWord_2312
  simp only [CollatzResearch.WordTrace]
  refine ⟨42162783815746851636595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56217045087662468848793 42162783815746851636595)
  ·
    refine ⟨63244175723620277454893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42162783815746851636595 63244175723620277454893)
    ·
      refine ⟨23716565896357604045585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63244175723620277454893 23716565896357604045585)
      ·
        refine ⟨17787424422268203034189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23716565896357604045585 17787424422268203034189)
        ·
          refine ⟨6670284158350576137821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17787424422268203034189 6670284158350576137821)
          ·
            refine ⟨2501356559381466051683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6670284158350576137821 2501356559381466051683)
            ·
              refine ⟨3752034839072199077525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2501356559381466051683 3752034839072199077525)
              ·
                refine ⟨175876633081509331759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3752034839072199077525 175876633081509331759)
                ·
                  rfl

theorem cell21_2312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 6].length) (baseStart_2312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2312 prefixEnd_2312 := by exact prefixLift 2312
  have htrace : WordTrace (prefixWord ++ tailWord_2312) baseStart_2312 baseEnd_2312 := by
    simpa [prefixWord, tailWord_2312, baseEnd_2312] using wordTrace_append hprefix tailTrace_2312
  have hstable : (prefixWord ++ tailWord_2312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2312).length < 2 ^ (prefixWord ++ tailWord_2312).sum := by decide
  have hdescent : baseEnd_2312 < baseStart_2312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388 : List Nat := [2, 4, 1, 1, 2, 2, 4, 5]
def baseStart_2388 : Nat := 118140960795 + 2388 * 2 ^ 59
def prefixEnd_2388 : Nat := 4983230072969 + 3 ^ 40 * 2388 * 2
def baseEnd_2388 : Nat := 181658044895094909485

theorem tailTrace_2388 : CollatzResearch.WordTrace tailWord_2388 prefixEnd_2388 181658044895094909485 := by
  unfold tailWord_2388
  simp only [CollatzResearch.WordTrace]
  refine ⟨43548757678079341519909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58065010237439122026545 43548757678079341519909)
  ·
    refine ⟨8165392064639876534983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43548757678079341519909 8165392064639876534983)
    ·
      refine ⟨12248088096959814802475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8165392064639876534983 12248088096959814802475)
      ·
        refine ⟨18372132145439722203713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12248088096959814802475 18372132145439722203713)
        ·
          refine ⟨13779099109079791652785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18372132145439722203713 13779099109079791652785)
          ·
            refine ⟨10334324331809843739589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13779099109079791652785 10334324331809843739589)
            ·
              refine ⟨1937685812214345701173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10334324331809843739589 1937685812214345701173)
              ·
                refine ⟨181658044895094909485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1937685812214345701173 181658044895094909485)
                ·
                  rfl

theorem cell21_2388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 5].length) (baseStart_2388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2388 prefixEnd_2388 := by exact prefixLift 2388
  have htrace : WordTrace (prefixWord ++ tailWord_2388) baseStart_2388 baseEnd_2388 := by
    simpa [prefixWord, tailWord_2388, baseEnd_2388] using wordTrace_append hprefix tailTrace_2388
  have hstable : (prefixWord ++ tailWord_2388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388).length < 2 ^ (prefixWord ++ tailWord_2388).sum := by decide
  have hdescent : baseEnd_2388 < baseStart_2388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 6]
def baseStart_2416 : Nat := 118140960795 + 2416 * 2 ^ 59
def prefixEnd_2416 : Nat := 4983230072969 + 3 ^ 40 * 2416 * 2
def baseEnd_2416 : Nat := 551364116163458261731

theorem tailTrace_2416 : CollatzResearch.WordTrace tailWord_2416 prefixEnd_2416 551364116163458261731 := by
  unfold tailWord_2416
  simp only [CollatzResearch.WordTrace]
  refine ⟨44059379627359732529551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58745839503146310039401 44059379627359732529551)
  ·
    refine ⟨66089069441039598794327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44059379627359732529551 66089069441039598794327)
    ·
      refine ⟨99133604161559398191491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66089069441039598794327 99133604161559398191491)
      ·
        refine ⟨148700406242339097287237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99133604161559398191491 148700406242339097287237)
        ·
          refine ⟨27881326170438580741357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148700406242339097287237 27881326170438580741357)
          ·
            refine ⟨10455497313914467778009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27881326170438580741357 10455497313914467778009)
            ·
              refine ⟨7841622985435850833507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10455497313914467778009 7841622985435850833507)
              ·
                refine ⟨11762434478153776250261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7841622985435850833507 11762434478153776250261)
                ·
                  refine ⟨551364116163458261731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11762434478153776250261 551364116163458261731)
                  ·
                    rfl

theorem cell21_2416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_2416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2416 prefixEnd_2416 := by exact prefixLift 2416
  have htrace : WordTrace (prefixWord ++ tailWord_2416) baseStart_2416 baseEnd_2416 := by
    simpa [prefixWord, tailWord_2416, baseEnd_2416] using wordTrace_append hprefix tailTrace_2416
  have hstable : (prefixWord ++ tailWord_2416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416).length < 2 ^ (prefixWord ++ tailWord_2416).sum := by decide
  have hdescent : baseEnd_2416 < baseStart_2416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571 : List Nat := [1, 1, 1, 1, 7, 1, 3, 3, 3]
def baseStart_2571 : Nat := 118140960795 + 2571 * 2 ^ 59
def prefixEnd_2571 : Nat := 4983230072969 + 3 ^ 40 * 2571 * 2
def baseEnd_2571 : Nat := 586737227917633178081

theorem tailTrace_2571 : CollatzResearch.WordTrace tailWord_2571 prefixEnd_2571 586737227917633178081 := by
  unfold tailWord_2571
  simp only [CollatzResearch.WordTrace]
  refine ⟨93772073693180936951567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62514715795453957967711 93772073693180936951567)
  ·
    refine ⟨140658110539771405427351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93772073693180936951567 140658110539771405427351)
    ·
      refine ⟨210987165809657108141027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140658110539771405427351 210987165809657108141027)
      ·
        refine ⟨316480748714485662211541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210987165809657108141027 316480748714485662211541)
        ·
          refine ⟨7417517547995757708083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 316480748714485662211541 7417517547995757708083)
          ·
            refine ⟨11126276321993636562125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7417517547995757708083 11126276321993636562125)
            ·
              refine ⟨4172353620747613710797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11126276321993636562125 4172353620747613710797)
              ·
                refine ⟨1564632607780355141549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4172353620747613710797 1564632607780355141549)
                ·
                  refine ⟨586737227917633178081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1564632607780355141549 586737227917633178081)
                  ·
                    rfl

theorem cell21_2571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 3].length) (baseStart_2571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2571 prefixEnd_2571 := by exact prefixLift 2571
  have htrace : WordTrace (prefixWord ++ tailWord_2571) baseStart_2571 baseEnd_2571 := by
    simpa [prefixWord, tailWord_2571, baseEnd_2571] using wordTrace_append hprefix tailTrace_2571
  have hstable : (prefixWord ++ tailWord_2571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571).length < 2 ^ (prefixWord ++ tailWord_2571).sum := by decide
  have hdescent : baseEnd_2571 < baseStart_2571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2588 : List Nat := [2, 2, 3, 1, 2, 3, 3, 2, 3]
def baseStart_2588 : Nat := 118140960795 + 2588 * 2 ^ 59
def prefixEnd_2588 : Nat := 4983230072969 + 3 ^ 40 * 2588 * 2
def baseEnd_2588 : Nat := 590616859529381394713

theorem tailTrace_2588 : CollatzResearch.WordTrace tailWord_2588 prefixEnd_2588 590616859529381394713 := by
  unfold tailWord_2588
  simp only [CollatzResearch.WordTrace]
  refine ⟨47196057315796420160209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62928076421061893546945 47196057315796420160209)
  ·
    refine ⟨35397042986847315120157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47196057315796420160209 35397042986847315120157)
    ·
      refine ⟨13273891120067743170059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35397042986847315120157 13273891120067743170059)
      ·
        refine ⟨19910836680101614755089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13273891120067743170059 19910836680101614755089)
        ·
          refine ⟨14933127510076211066317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19910836680101614755089 14933127510076211066317)
          ·
            refine ⟨5599922816278579149869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14933127510076211066317 5599922816278579149869)
            ·
              refine ⟨2099971056104467181201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5599922816278579149869 2099971056104467181201)
              ·
                refine ⟨1574978292078350385901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2099971056104467181201 1574978292078350385901)
                ·
                  refine ⟨590616859529381394713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1574978292078350385901 590616859529381394713)
                  ·
                    rfl

theorem cell21_2588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_2588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2588 prefixEnd_2588 := by exact prefixLift 2588
  have htrace : WordTrace (prefixWord ++ tailWord_2588) baseStart_2588 baseEnd_2588 := by
    simpa [prefixWord, tailWord_2588, baseEnd_2588] using wordTrace_append hprefix tailTrace_2588
  have hstable : (prefixWord ++ tailWord_2588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2588).length < 2 ^ (prefixWord ++ tailWord_2588).sum := by decide
  have hdescent : baseEnd_2588 < baseStart_2588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602 : List Nat := [3, 1, 4, 1, 1, 2, 4, 1, 4]
def baseStart_2602 : Nat := 118140960795 + 2602 * 2 ^ 59
def prefixEnd_2602 : Nat := 4983230072969 + 3 ^ 40 * 2602 * 2
def baseEnd_2602 : Nat := 593811850268468161351

theorem tailTrace_2602 : CollatzResearch.WordTrace tailWord_2602 prefixEnd_2602 593811850268468161351 := by
  unfold tailWord_2602
  simp only [CollatzResearch.WordTrace]
  refine ⟨23725684145218307832515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63268491053915487553373 23725684145218307832515)
  ·
    refine ⟨35588526217827461748773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23725684145218307832515 35588526217827461748773)
    ·
      refine ⟨6672848665842649077895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35588526217827461748773 6672848665842649077895)
      ·
        refine ⟨10009272998763973616843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6672848665842649077895 10009272998763973616843)
        ·
          refine ⟨15013909498145960425265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10009272998763973616843 15013909498145960425265)
          ·
            refine ⟨11260432123609470318949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15013909498145960425265 11260432123609470318949)
            ·
              refine ⟨2111331023176775684803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11260432123609470318949 2111331023176775684803)
              ·
                refine ⟨3166996534765163527205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2111331023176775684803 3166996534765163527205)
                ·
                  refine ⟨593811850268468161351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3166996534765163527205 593811850268468161351)
                  ·
                    rfl

theorem cell21_2602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_2602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2602 prefixEnd_2602 := by exact prefixLift 2602
  have htrace : WordTrace (prefixWord ++ tailWord_2602) baseStart_2602 baseEnd_2602 := by
    simpa [prefixWord, tailWord_2602, baseEnd_2602] using wordTrace_append hprefix tailTrace_2602
  have hstable : (prefixWord ++ tailWord_2602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602).length < 2 ^ (prefixWord ++ tailWord_2602).sum := by decide
  have hdescent : baseEnd_2602 < baseStart_2602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 7]
def baseStart_2613 : Nat := 118140960795 + 2613 * 2 ^ 59
def prefixEnd_2613 : Nat := 4983230072969 + 3 ^ 40 * 2613 * 2
def baseEnd_2613 : Nat := 596322200134893477995

theorem tailTrace_2613 : CollatzResearch.WordTrace tailWord_2613 prefixEnd_2613 596322200134893477995 := by
  unfold tailWord_2613
  simp only [CollatzResearch.WordTrace]
  refine ⟨95303939541022109980493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63535959694014739986995 95303939541022109980493)
  ·
    refine ⟨35738977327883291242685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95303939541022109980493 35738977327883291242685)
    ·
      refine ⟨13402116497956234216007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35738977327883291242685 13402116497956234216007)
      ·
        refine ⟨20103174746934351324011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13402116497956234216007 20103174746934351324011)
        ·
          refine ⟨30154762120401526986017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20103174746934351324011 30154762120401526986017)
          ·
            refine ⟨22616071590301145239513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30154762120401526986017 22616071590301145239513)
            ·
              refine ⟨16962053692725858929635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22616071590301145239513 16962053692725858929635)
              ·
                refine ⟨25443080539088788394453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16962053692725858929635 25443080539088788394453)
                ·
                  refine ⟨596322200134893477995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 25443080539088788394453 596322200134893477995)
                  ·
                    rfl

theorem cell21_2613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_2613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2613 prefixEnd_2613 := by exact prefixLift 2613
  have htrace : WordTrace (prefixWord ++ tailWord_2613) baseStart_2613 baseEnd_2613 := by
    simpa [prefixWord, tailWord_2613, baseEnd_2613] using wordTrace_append hprefix tailTrace_2613
  have hstable : (prefixWord ++ tailWord_2613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613).length < 2 ^ (prefixWord ++ tailWord_2613).sum := by decide
  have hdescent : baseEnd_2613 < baseStart_2613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 8]
def baseStart_2627 : Nat := 118140960795 + 2627 * 2 ^ 59
def prefixEnd_2627 : Nat := 4983230072969 + 3 ^ 40 * 2627 * 2
def baseEnd_2627 : Nat := 599517190873980244633

theorem tailTrace_2627 : CollatzResearch.WordTrace tailWord_2627 prefixEnd_2627 599517190873980244633 := by
  unfold tailWord_2627
  simp only [CollatzResearch.WordTrace]
  refine ⟨95814561490302500990135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63876374326868333993423 95814561490302500990135)
  ·
    refine ⟨143721842235453751485203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95814561490302500990135 143721842235453751485203)
    ·
      refine ⟨215582763353180627227805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143721842235453751485203 215582763353180627227805)
      ·
        refine ⟨80843536257442735210427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215582763353180627227805 80843536257442735210427)
        ·
          refine ⟨121265304386164102815641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80843536257442735210427 121265304386164102815641)
          ·
            refine ⟨90948978289623077111731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121265304386164102815641 90948978289623077111731)
            ·
              refine ⟨136423467434434615667597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90948978289623077111731 136423467434434615667597)
              ·
                refine ⟨51158800287912980875349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136423467434434615667597 51158800287912980875349)
                ·
                  refine ⟨599517190873980244633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 51158800287912980875349 599517190873980244633)
                  ·
                    rfl

theorem cell21_2627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 8].length) (baseStart_2627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2627 prefixEnd_2627 := by exact prefixLift 2627
  have htrace : WordTrace (prefixWord ++ tailWord_2627) baseStart_2627 baseEnd_2627 := by
    simpa [prefixWord, tailWord_2627, baseEnd_2627] using wordTrace_append hprefix tailTrace_2627
  have hstable : (prefixWord ++ tailWord_2627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627).length < 2 ^ (prefixWord ++ tailWord_2627).sum := by decide
  have hdescent : baseEnd_2627 < baseStart_2627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 7]
def baseStart_2689 : Nat := 118140960795 + 2689 * 2 ^ 59
def prefixEnd_2689 : Nat := 4983230072969 + 3 ^ 40 * 2689 * 2
def baseEnd_2689 : Nat := 613666435575650211173

theorem tailTrace_2689 : CollatzResearch.WordTrace tailWord_2689 prefixEnd_2689 613666435575650211173 := by
  unfold tailWord_2689
  simp only [CollatzResearch.WordTrace]
  refine ⟨98075887265687089747121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65383924843791393164747 98075887265687089747121)
  ·
    refine ⟨73556915449265317310341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98075887265687089747121 73556915449265317310341)
    ·
      refine ⟨13791921646737246995689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73556915449265317310341 13791921646737246995689)
      ·
        refine ⟨10343941235052935246767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13791921646737246995689 10343941235052935246767)
        ·
          refine ⟨15515911852579402870151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10343941235052935246767 15515911852579402870151)
          ·
            refine ⟨23273867778869104305227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15515911852579402870151 23273867778869104305227)
            ·
              refine ⟨34910801668303656457841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23273867778869104305227 34910801668303656457841)
              ·
                refine ⟨26183101251227742343381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34910801668303656457841 26183101251227742343381)
                ·
                  refine ⟨613666435575650211173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 26183101251227742343381 613666435575650211173)
                  ·
                    rfl

theorem cell21_2689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_2689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2689 prefixEnd_2689 := by exact prefixLift 2689
  have htrace : WordTrace (prefixWord ++ tailWord_2689) baseStart_2689 baseEnd_2689 := by
    simpa [prefixWord, tailWord_2689, baseEnd_2689] using wordTrace_append hprefix tailTrace_2689
  have hstable : (prefixWord ++ tailWord_2689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689).length < 2 ^ (prefixWord ++ tailWord_2689).sum := by decide
  have hdescent : baseEnd_2689 < baseStart_2689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 6]
def baseStart_2703 : Nat := 118140960795 + 2703 * 2 ^ 59
def prefixEnd_2703 : Nat := 4983230072969 + 3 ^ 40 * 2703 * 2
def baseEnd_2703 : Nat := 616861426314736977811

theorem tailTrace_2703 : CollatzResearch.WordTrace tailWord_2703 prefixEnd_2703 616861426314736977811 := by
  unfold tailWord_2703
  simp only [CollatzResearch.WordTrace]
  refine ⟨98586509214967480756763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65724339476644987171175 98586509214967480756763)
  ·
    refine ⟨147879763822451221135145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98586509214967480756763 147879763822451221135145)
    ·
      refine ⟨110909822866838415851359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147879763822451221135145 110909822866838415851359)
      ·
        refine ⟨166364734300257623777039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110909822866838415851359 166364734300257623777039)
        ·
          refine ⟨249547101450386435665559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166364734300257623777039 249547101450386435665559)
          ·
            refine ⟨374320652175579653498339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249547101450386435665559 374320652175579653498339)
            ·
              refine ⟨561480978263369480247509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374320652175579653498339 561480978263369480247509)
              ·
                refine ⟨13159710428047722193301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 561480978263369480247509 13159710428047722193301)
                ·
                  refine ⟨616861426314736977811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13159710428047722193301 616861426314736977811)
                  ·
                    rfl

theorem cell21_2703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 6].length) (baseStart_2703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2703 prefixEnd_2703 := by exact prefixLift 2703
  have htrace : WordTrace (prefixWord ++ tailWord_2703) baseStart_2703 baseEnd_2703 := by
    simpa [prefixWord, tailWord_2703, baseEnd_2703] using wordTrace_append hprefix tailTrace_2703
  have hstable : (prefixWord ++ tailWord_2703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703).length < 2 ^ (prefixWord ++ tailWord_2703).sum := by decide
  have hdescent : baseEnd_2703 < baseStart_2703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706 : List Nat := [3, 2, 3, 1, 2, 1, 1, 3, 5]
def baseStart_2706 : Nat := 118140960795 + 2706 * 2 ^ 59
def prefixEnd_2706 : Nat := 4983230072969 + 3 ^ 40 * 2706 * 2
def baseEnd_2706 : Nat := 617546067187398427805

theorem tailTrace_2706 : CollatzResearch.WordTrace tailWord_2706 prefixEnd_2706 617546067187398427805 := by
  unfold tailWord_2706
  simp only [CollatzResearch.WordTrace]
  refine ⟨24673982051024748278993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65797285469399328743981 24673982051024748278993)
  ·
    refine ⟨18505486538268561209245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24673982051024748278993 18505486538268561209245)
    ·
      refine ⟨6939557451850710453467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18505486538268561209245 6939557451850710453467)
      ·
        refine ⟨10409336177776065680201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6939557451850710453467 10409336177776065680201)
        ·
          refine ⟨7807002133332049260151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10409336177776065680201 7807002133332049260151)
          ·
            refine ⟨11710503199998073890227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7807002133332049260151 11710503199998073890227)
            ·
              refine ⟨17565754799997110835341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11710503199998073890227 17565754799997110835341)
              ·
                refine ⟨6587158049998916563253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17565754799997110835341 6587158049998916563253)
                ·
                  refine ⟨617546067187398427805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6587158049998916563253 617546067187398427805)
                  ·
                    rfl

theorem cell21_2706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_2706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2706 prefixEnd_2706 := by exact prefixLift 2706
  have htrace : WordTrace (prefixWord ++ tailWord_2706) baseStart_2706 baseEnd_2706 := by
    simpa [prefixWord, tailWord_2706, baseEnd_2706] using wordTrace_append hprefix tailTrace_2706
  have hstable : (prefixWord ++ tailWord_2706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706).length < 2 ^ (prefixWord ++ tailWord_2706).sum := by decide
  have hdescent : baseEnd_2706 < baseStart_2706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889 : List Nat := [1, 2, 1, 1, 2, 6, 3, 1, 4]
def baseStart_2889 : Nat := 118140960795 + 2889 * 2 ^ 59
def prefixEnd_2889 : Nat := 4983230072969 + 3 ^ 40 * 2889 * 2
def baseEnd_2889 : Nat := 659309160419746877431

theorem tailTrace_2889 : CollatzResearch.WordTrace tailWord_2889 prefixEnd_2889 659309160419746877431 := by
  unfold tailWord_2889
  simp only [CollatzResearch.WordTrace]
  refine ⟨105370486541121247027721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70246991027414164685147 105370486541121247027721)
  ·
    refine ⟨79027864905840935270791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105370486541121247027721 79027864905840935270791)
    ·
      refine ⟨118541797358761402906187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79027864905840935270791 118541797358761402906187)
      ·
        refine ⟨177812696038142104359281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118541797358761402906187 177812696038142104359281)
        ·
          refine ⟨133359522028606578269461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177812696038142104359281 133359522028606578269461)
          ·
            refine ⟨6251227595090933356381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 133359522028606578269461 6251227595090933356381)
            ·
              refine ⟨2344210348159100008643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6251227595090933356381 2344210348159100008643)
              ·
                refine ⟨3516315522238650012965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2344210348159100008643 3516315522238650012965)
                ·
                  refine ⟨659309160419746877431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3516315522238650012965 659309160419746877431)
                  ·
                    rfl

theorem cell21_2889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 4].length) (baseStart_2889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2889 prefixEnd_2889 := by exact prefixLift 2889
  have htrace : WordTrace (prefixWord ++ tailWord_2889) baseStart_2889 baseEnd_2889 := by
    simpa [prefixWord, tailWord_2889, baseEnd_2889] using wordTrace_append hprefix tailTrace_2889
  have hstable : (prefixWord ++ tailWord_2889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889).length < 2 ^ (prefixWord ++ tailWord_2889).sum := by decide
  have hdescent : baseEnd_2889 < baseStart_2889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2903 : List Nat := [1, 1, 3, 2, 4, 1, 4, 5]
def baseStart_2903 : Nat := 118140960795 + 2903 * 2 ^ 59
def prefixEnd_2903 : Nat := 4983230072969 + 3 ^ 40 * 2903 * 2
def baseEnd_2903 : Nat := 220834717052944548023

theorem tailTrace_2903 : CollatzResearch.WordTrace tailWord_2903 prefixEnd_2903 220834717052944548023 := by
  unfold tailWord_2903
  simp only [CollatzResearch.WordTrace]
  refine ⟨105881108490401638037363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70587405660267758691575 105881108490401638037363)
  ·
    refine ⟨158821662735602457056045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105881108490401638037363 158821662735602457056045)
    ·
      refine ⟨59558123525850921396017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158821662735602457056045 59558123525850921396017)
      ·
        refine ⟨44668592644388191047013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59558123525850921396017 44668592644388191047013)
        ·
          refine ⟨8375361120822785821315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44668592644388191047013 8375361120822785821315)
          ·
            refine ⟨12563041681234178731973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8375361120822785821315 12563041681234178731973)
            ·
              refine ⟨2355570315231408512245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12563041681234178731973 2355570315231408512245)
              ·
                refine ⟨220834717052944548023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2355570315231408512245 220834717052944548023)
                ·
                  rfl

theorem cell21_2903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 5].length) (baseStart_2903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2903 prefixEnd_2903 := by exact prefixLift 2903
  have htrace : WordTrace (prefixWord ++ tailWord_2903) baseStart_2903 baseEnd_2903 := by
    simpa [prefixWord, tailWord_2903, baseEnd_2903] using wordTrace_append hprefix tailTrace_2903
  have hstable : (prefixWord ++ tailWord_2903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2903).length < 2 ^ (prefixWord ++ tailWord_2903).sum := by decide
  have hdescent : baseEnd_2903 < baseStart_2903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 6]
def baseStart_2931 : Nat := 118140960795 + 2931 * 2 ^ 59
def prefixEnd_2931 : Nat := 4983230072969 + 3 ^ 40 * 2931 * 2
def baseEnd_2931 : Nat := 668894132637007177345

theorem tailTrace_2931 : CollatzResearch.WordTrace tailWord_2931 prefixEnd_2931 668894132637007177345 := by
  unfold tailWord_2931
  simp only [CollatzResearch.WordTrace]
  refine ⟨106902352388962420056647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71268234925974946704431 106902352388962420056647)
  ·
    refine ⟨160353528583443630084971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106902352388962420056647 160353528583443630084971)
    ·
      refine ⟨240530292875165445127457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160353528583443630084971 240530292875165445127457)
      ·
        refine ⟨180397719656374083845593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240530292875165445127457 180397719656374083845593)
        ·
          refine ⟨135298289742280562884195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180397719656374083845593 135298289742280562884195)
          ·
            refine ⟨202947434613420844326293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135298289742280562884195 202947434613420844326293)
            ·
              refine ⟨9513160997504102077795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 202947434613420844326293 9513160997504102077795)
              ·
                refine ⟨14269741496256153116693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9513160997504102077795 14269741496256153116693)
                ·
                  refine ⟨668894132637007177345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14269741496256153116693 668894132637007177345)
                  ·
                    rfl

theorem cell21_2931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 6].length) (baseStart_2931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2931 prefixEnd_2931 := by exact prefixLift 2931
  have htrace : WordTrace (prefixWord ++ tailWord_2931) baseStart_2931 baseEnd_2931 := by
    simpa [prefixWord, tailWord_2931, baseEnd_2931] using wordTrace_append hprefix tailTrace_2931
  have hstable : (prefixWord ++ tailWord_2931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931).length < 2 ^ (prefixWord ++ tailWord_2931).sum := by decide
  have hdescent : baseEnd_2931 < baseStart_2931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996 : List Nat := [2, 5, 2, 1, 1, 1, 3, 6]
def baseStart_2996 : Nat := 118140960795 + 2996 * 2 ^ 59
def prefixEnd_2996 : Nat := 4983230072969 + 3 ^ 40 * 2996 * 2
def baseEnd_2996 : Nat := 227909339403779531293

theorem tailTrace_2996 : CollatzResearch.WordTrace tailWord_2996 prefixEnd_2996 227909339403779531293 := by
  unfold tailWord_2996
  simp only [CollatzResearch.WordTrace]
  refine ⟨54636548576739260586421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72848731435652347448561 54636548576739260586421)
  ·
    refine ⟨5122176429069305679977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54636548576739260586421 5122176429069305679977)
    ·
      refine ⟨3841632321801979259983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5122176429069305679977 3841632321801979259983)
      ·
        refine ⟨5762448482702968889975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3841632321801979259983 5762448482702968889975)
        ·
          refine ⟨8643672724054453334963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5762448482702968889975 8643672724054453334963)
          ·
            refine ⟨12965509086081680002445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8643672724054453334963 12965509086081680002445)
            ·
              refine ⟨4862065907280630000917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12965509086081680002445 4862065907280630000917)
              ·
                refine ⟨227909339403779531293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4862065907280630000917 227909339403779531293)
                ·
                  rfl

theorem cell21_2996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 6].length) (baseStart_2996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2996 prefixEnd_2996 := by exact prefixLift 2996
  have htrace : WordTrace (prefixWord ++ tailWord_2996) baseStart_2996 baseEnd_2996 := by
    simpa [prefixWord, tailWord_2996, baseEnd_2996] using wordTrace_append hprefix tailTrace_2996
  have hstable : (prefixWord ++ tailWord_2996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996).length < 2 ^ (prefixWord ++ tailWord_2996).sum := by decide
  have hdescent : baseEnd_2996 < baseStart_2996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3083 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 6]
def baseStart_3083 : Nat := 118140960795 + 3083 * 2 ^ 59
def prefixEnd_3083 : Nat := 4983230072969 + 3 ^ 40 * 3083 * 2
def baseEnd_3083 : Nat := 703582603518520643701

theorem tailTrace_3083 : CollatzResearch.WordTrace tailWord_3083 prefixEnd_3083 703582603518520643701 := by
  unfold tailWord_3083
  simp only [CollatzResearch.WordTrace]
  refine ⟨112446247838292379589903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74964165225528253059935 112446247838292379589903)
  ·
    refine ⟨168669371757438569384855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112446247838292379589903 168669371757438569384855)
    ·
      refine ⟨253004057636157854077283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168669371757438569384855 253004057636157854077283)
      ·
        refine ⟨379506086454236781115925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253004057636157854077283 379506086454236781115925)
        ·
          refine ⟨17789347802542349114809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 379506086454236781115925 17789347802542349114809)
          ·
            refine ⟨13342010851906761836107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17789347802542349114809 13342010851906761836107)
            ·
              refine ⟨20013016277860142754161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13342010851906761836107 20013016277860142754161)
              ·
                refine ⟨15009762208395107065621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20013016277860142754161 15009762208395107065621)
                ·
                  refine ⟨703582603518520643701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15009762208395107065621 703582603518520643701)
                  ·
                    rfl

theorem cell21_3083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 6].length) (baseStart_3083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3083 prefixEnd_3083 := by exact prefixLift 3083
  have htrace : WordTrace (prefixWord ++ tailWord_3083) baseStart_3083 baseEnd_3083 := by
    simpa [prefixWord, tailWord_3083, baseEnd_3083] using wordTrace_append hprefix tailTrace_3083
  have hstable : (prefixWord ++ tailWord_3083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3083).length < 2 ^ (prefixWord ++ tailWord_3083).sum := by decide
  have hdescent : baseEnd_3083 < baseStart_3083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097 : List Nat := [1, 2, 1, 2, 1, 1, 13]
def baseStart_3097 : Nat := 118140960795 + 3097 * 2 ^ 59
def prefixEnd_3097 : Nat := 4983230072969 + 3 ^ 40 * 3097 * 2
def baseEnd_3097 : Nat := 78530843806400823371

theorem tailTrace_3097 : CollatzResearch.WordTrace tailWord_3097 prefixEnd_3097 78530843806400823371 := by
  unfold tailWord_3097
  simp only [CollatzResearch.WordTrace]
  refine ⟨112956869787572770599545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75304579858381847066363 112956869787572770599545)
  ·
    refine ⟨84717652340679577949659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112956869787572770599545 84717652340679577949659)
    ·
      refine ⟨127076478511019366924489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84717652340679577949659 127076478511019366924489)
      ·
        refine ⟨95307358883264525193367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127076478511019366924489 95307358883264525193367)
        ·
          refine ⟨142961038324896787790051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95307358883264525193367 142961038324896787790051)
          ·
            refine ⟨214441557487345181685077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142961038324896787790051 214441557487345181685077)
            ·
              refine ⟨78530843806400823371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 214441557487345181685077 78530843806400823371)
              ·
                rfl

theorem cell21_3097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 13].length) (baseStart_3097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3097 prefixEnd_3097 := by exact prefixLift 3097
  have htrace : WordTrace (prefixWord ++ tailWord_3097) baseStart_3097 baseEnd_3097 := by
    simpa [prefixWord, tailWord_3097, baseEnd_3097] using wordTrace_append hprefix tailTrace_3097
  have hstable : (prefixWord ++ tailWord_3097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097).length < 2 ^ (prefixWord ++ tailWord_3097).sum := by decide
  have hdescent : baseEnd_3097 < baseStart_3097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103 : List Nat := [1, 1, 2, 4, 1, 4, 3, 2, 3]
def baseStart_3103 : Nat := 118140960795 + 3103 * 2 ^ 59
def prefixEnd_3103 : Nat := 4983230072969 + 3 ^ 40 * 3103 * 2
def baseEnd_3103 : Nat := 708146876002930310327

theorem tailTrace_3103 : CollatzResearch.WordTrace tailWord_3103 prefixEnd_3103 708146876002930310327 := by
  unfold tailWord_3103
  simp only [CollatzResearch.WordTrace]
  refine ⟨113175707765835795317963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75450471843890530211975 113175707765835795317963)
  ·
    refine ⟨169763561648753692976945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113175707765835795317963 169763561648753692976945)
    ·
      refine ⟨127322671236565269732709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169763561648753692976945 127322671236565269732709)
      ·
        refine ⟨23873000856855988074883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127322671236565269732709 23873000856855988074883)
        ·
          refine ⟨35809501285283982112325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23873000856855988074883 35809501285283982112325)
          ·
            refine ⟨6714281490990746646061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35809501285283982112325 6714281490990746646061)
            ·
              refine ⟨2517855559121529992273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6714281490990746646061 2517855559121529992273)
              ·
                refine ⟨1888391669341147494205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2517855559121529992273 1888391669341147494205)
                ·
                  refine ⟨708146876002930310327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1888391669341147494205 708146876002930310327)
                  ·
                    rfl

theorem cell21_3103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 3].length) (baseStart_3103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3103 prefixEnd_3103 := by exact prefixLift 3103
  have htrace : WordTrace (prefixWord ++ tailWord_3103) baseStart_3103 baseEnd_3103 := by
    simpa [prefixWord, tailWord_3103, baseEnd_3103] using wordTrace_append hprefix tailTrace_3103
  have hstable : (prefixWord ++ tailWord_3103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103).length < 2 ^ (prefixWord ++ tailWord_3103).sum := by decide
  have hdescent : baseEnd_3103 < baseStart_3103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3165 : List Nat := [1, 4, 4, 1, 3, 1, 1, 6]
def baseStart_3165 : Nat := 118140960795 + 3165 * 2 ^ 59
def prefixEnd_3165 : Nat := 4983230072969 + 3 ^ 40 * 3165 * 2
def baseEnd_3165 : Nat := 240765373568200092289

theorem tailTrace_3165 : CollatzResearch.WordTrace tailWord_3165 prefixEnd_3165 240765373568200092289 := by
  unfold tailWord_3165
  simp only [CollatzResearch.WordTrace]
  refine ⟨115437033541220384074949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76958022360813589383299 115437033541220384074949)
  ·
    refine ⟨21644443788978822014053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115437033541220384074949 21644443788978822014053)
    ·
      refine ⟨4058333210433529127635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21644443788978822014053 4058333210433529127635)
      ·
        refine ⟨6087499815650293691453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4058333210433529127635 6087499815650293691453)
        ·
          refine ⟨2282812430868860134295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6087499815650293691453 2282812430868860134295)
          ·
            refine ⟨3424218646303290201443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2282812430868860134295 3424218646303290201443)
            ·
              refine ⟨5136327969454935302165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3424218646303290201443 5136327969454935302165)
              ·
                refine ⟨240765373568200092289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5136327969454935302165 240765373568200092289)
                ·
                  rfl

theorem cell21_3165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 6].length) (baseStart_3165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3165 prefixEnd_3165 := by exact prefixLift 3165
  have htrace : WordTrace (prefixWord ++ tailWord_3165) baseStart_3165 baseEnd_3165 := by
    simpa [prefixWord, tailWord_3165, baseEnd_3165] using wordTrace_append hprefix tailTrace_3165
  have hstable : (prefixWord ++ tailWord_3165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3165).length < 2 ^ (prefixWord ++ tailWord_3165).sum := by decide
  have hdescent : baseEnd_3165 < baseStart_3165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235 : List Nat := [1, 1, 1, 4, 1, 1, 1, 7, 4]
def baseStart_3235 : Nat := 118140960795 + 3235 * 2 ^ 59
def prefixEnd_3235 : Nat := 4983230072969 + 3 ^ 40 * 3235 * 2
def baseEnd_3235 : Nat := 738271074400034110057

theorem tailTrace_3235 : CollatzResearch.WordTrace tailWord_3235 prefixEnd_3235 738271074400034110057 := by
  unfold tailWord_3235
  simp only [CollatzResearch.WordTrace]
  refine ⟨117990143287622339123159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78660095525081559415439 117990143287622339123159)
  ·
    refine ⟨176985214931433508684739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117990143287622339123159 176985214931433508684739)
    ·
      refine ⟨265477822397150263027109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176985214931433508684739 265477822397150263027109)
      ·
        refine ⟨49777091699465674317583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265477822397150263027109 49777091699465674317583)
        ·
          refine ⟨74665637549198511476375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49777091699465674317583 74665637549198511476375)
          ·
            refine ⟨111998456323797767214563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74665637549198511476375 111998456323797767214563)
            ·
              refine ⟨167997684485696650821845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111998456323797767214563 167997684485696650821845)
              ·
                refine ⟨3937445730133515253637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 167997684485696650821845 3937445730133515253637)
                ·
                  refine ⟨738271074400034110057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3937445730133515253637 738271074400034110057)
                  ·
                    rfl

theorem cell21_3235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 4].length) (baseStart_3235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3235 prefixEnd_3235 := by exact prefixLift 3235
  have htrace : WordTrace (prefixWord ++ tailWord_3235) baseStart_3235 baseEnd_3235 := by
    simpa [prefixWord, tailWord_3235, baseEnd_3235] using wordTrace_append hprefix tailTrace_3235
  have hstable : (prefixWord ++ tailWord_3235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235).length < 2 ^ (prefixWord ++ tailWord_3235).sum := by decide
  have hdescent : baseEnd_3235 < baseStart_3235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3286 : List Nat := [5, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_3286 : Nat := 118140960795 + 3286 * 2 ^ 59
def prefixEnd_3286 : Nat := 4983230072969 + 3 ^ 40 * 3286 * 2
def baseEnd_3286 : Nat := 749909969235278759953

theorem tailTrace_3286 : CollatzResearch.WordTrace tailWord_3286 prefixEnd_3286 749909969235278759953 := by
  unfold tailWord_3286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7490641631428628076857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79900177401905366153141 7490641631428628076857)
  ·
    refine ⟨5617981223571471057643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7490641631428628076857 5617981223571471057643)
    ·
      refine ⟨8426971835357206586465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5617981223571471057643 8426971835357206586465)
      ·
        refine ⟨6320228876517904939849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8426971835357206586465 6320228876517904939849)
        ·
          refine ⟨4740171657388428704887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6320228876517904939849 4740171657388428704887)
          ·
            refine ⟨7110257486082643057331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4740171657388428704887 7110257486082643057331)
            ·
              refine ⟨10665386229123964585997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7110257486082643057331 10665386229123964585997)
              ·
                refine ⟨3999519835921486719749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10665386229123964585997 3999519835921486719749)
                ·
                  refine ⟨749909969235278759953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3999519835921486719749 749909969235278759953)
                  ·
                    rfl

theorem cell21_3286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_3286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3286 prefixEnd_3286 := by exact prefixLift 3286
  have htrace : WordTrace (prefixWord ++ tailWord_3286) baseStart_3286 baseEnd_3286 := by
    simpa [prefixWord, tailWord_3286, baseEnd_3286] using wordTrace_append hprefix tailTrace_3286
  have hstable : (prefixWord ++ tailWord_3286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3286).length < 2 ^ (prefixWord ++ tailWord_3286).sum := by decide
  have hdescent : baseEnd_3286 < baseStart_3286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3331 : List Nat := [1, 1, 1, 3, 2, 6, 2, 2, 3]
def baseStart_3331 : Nat := 118140960795 + 3331 * 2 ^ 59
def prefixEnd_3331 : Nat := 4983230072969 + 3 ^ 40 * 3331 * 2
def baseEnd_3331 : Nat := 760179582325200509861

theorem tailTrace_3331 : CollatzResearch.WordTrace tailWord_3331 prefixEnd_3331 760179582325200509861 := by
  unfold tailWord_3331
  simp only [CollatzResearch.WordTrace]
  refine ⟨121491550939830734617847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80994367293220489745231 121491550939830734617847)
  ·
    refine ⟨182237326409746101926771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121491550939830734617847 182237326409746101926771)
    ·
      refine ⟨273355989614619152890157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182237326409746101926771 273355989614619152890157)
      ·
        refine ⟨102508496105482182333809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273355989614619152890157 102508496105482182333809)
        ·
          refine ⟨76881372079111636750357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102508496105482182333809 76881372079111636750357)
          ·
            refine ⟨3603814316208357972673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 76881372079111636750357 3603814316208357972673)
            ·
              refine ⟨2702860737156268479505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3603814316208357972673 2702860737156268479505)
              ·
                refine ⟨2027145552867201359629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2702860737156268479505 2027145552867201359629)
                ·
                  refine ⟨760179582325200509861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2027145552867201359629 760179582325200509861)
                  ·
                    rfl

theorem cell21_3331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 3].length) (baseStart_3331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3331 prefixEnd_3331 := by exact prefixLift 3331
  have htrace : WordTrace (prefixWord ++ tailWord_3331) baseStart_3331 baseEnd_3331 := by
    simpa [prefixWord, tailWord_3331, baseEnd_3331] using wordTrace_append hprefix tailTrace_3331
  have hstable : (prefixWord ++ tailWord_3331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3331).length < 2 ^ (prefixWord ++ tailWord_3331).sum := by decide
  have hdescent : baseEnd_3331 < baseStart_3331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3342 : List Nat := [4, 1, 1, 2, 1, 3, 3, 6]
def baseStart_3342 : Nat := 118140960795 + 3342 * 2 ^ 59
def prefixEnd_3342 : Nat := 4983230072969 + 3 ^ 40 * 3342 * 2
def baseEnd_3342 : Nat := 254229977397208608835

theorem tailTrace_3342 : CollatzResearch.WordTrace tailWord_3342 prefixEnd_3342 254229977397208608835 := by
  unfold tailWord_3342
  simp only [CollatzResearch.WordTrace]
  refine ⟨15236594237497451658535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81261835933319742178853 15236594237497451658535)
  ·
    refine ⟨22854891356246177487803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15236594237497451658535 22854891356246177487803)
    ·
      refine ⟨34282337034369266231705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22854891356246177487803 34282337034369266231705)
      ·
        refine ⟨25711752775776949673779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34282337034369266231705 25711752775776949673779)
        ·
          refine ⟨38567629163665424510669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25711752775776949673779 38567629163665424510669)
          ·
            refine ⟨14462860936374534191501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38567629163665424510669 14462860936374534191501)
            ·
              refine ⟨5423572851140450321813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14462860936374534191501 5423572851140450321813)
              ·
                refine ⟨254229977397208608835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5423572851140450321813 254229977397208608835)
                ·
                  rfl

theorem cell21_3342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_3342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3342 prefixEnd_3342 := by exact prefixLift 3342
  have htrace : WordTrace (prefixWord ++ tailWord_3342) baseStart_3342 baseEnd_3342 := by
    simpa [prefixWord, tailWord_3342, baseEnd_3342] using wordTrace_append hprefix tailTrace_3342
  have hstable : (prefixWord ++ tailWord_3342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3342).length < 2 ^ (prefixWord ++ tailWord_3342).sum := by decide
  have hdescent : baseEnd_3342 < baseStart_3342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 7]
def baseStart_3356 : Nat := 118140960795 + 3356 * 2 ^ 59
def prefixEnd_3356 : Nat := 4983230072969 + 3 ^ 40 * 3356 * 2
def baseEnd_3356 : Nat := 765884922930712593143

theorem tailTrace_3356 : CollatzResearch.WordTrace tailWord_3356 prefixEnd_3356 765884922930712593143 := by
  unfold tailWord_3356
  simp only [CollatzResearch.WordTrace]
  refine ⟨61201687924630002138961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81602250566173336185281 61201687924630002138961)
  ·
    refine ⟨45901265943472501604221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61201687924630002138961 45901265943472501604221)
    ·
      refine ⟨17212974728802188101583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45901265943472501604221 17212974728802188101583)
      ·
        refine ⟨25819462093203282152375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17212974728802188101583 25819462093203282152375)
        ·
          refine ⟨38729193139804923228563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25819462093203282152375 38729193139804923228563)
          ·
            refine ⟨58093789709707384842845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38729193139804923228563 58093789709707384842845)
            ·
              refine ⟨21785171141140269316067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58093789709707384842845 21785171141140269316067)
              ·
                refine ⟨32677756711710403974101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21785171141140269316067 32677756711710403974101)
                ·
                  refine ⟨765884922930712593143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 32677756711710403974101 765884922930712593143)
                  ·
                    rfl

theorem cell21_3356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_3356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3356 prefixEnd_3356 := by exact prefixLift 3356
  have htrace : WordTrace (prefixWord ++ tailWord_3356) baseStart_3356 baseEnd_3356 := by
    simpa [prefixWord, tailWord_3356, baseEnd_3356] using wordTrace_append hprefix tailTrace_3356
  have hstable : (prefixWord ++ tailWord_3356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356).length < 2 ^ (prefixWord ++ tailWord_3356).sum := by decide
  have hdescent : baseEnd_3356 < baseStart_3356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359 : List Nat := [1, 1, 2, 4, 4, 1, 3, 5]
def baseStart_3359 : Nat := 118140960795 + 3359 * 2 ^ 59
def prefixEnd_3359 : Nat := 4983230072969 + 3 ^ 40 * 3359 * 2
def baseEnd_3359 : Nat := 255523187934458014379

theorem tailTrace_3359 : CollatzResearch.WordTrace tailWord_3359 prefixEnd_3359 255523187934458014379 := by
  unfold tailWord_3359
  simp only [CollatzResearch.WordTrace]
  refine ⟨122512794838391516637131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81675196558927677758087 122512794838391516637131)
  ·
    refine ⟨183769192257587274955697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122512794838391516637131 183769192257587274955697)
    ·
      refine ⟨137826894193190456216773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183769192257587274955697 137826894193190456216773)
      ·
        refine ⟨25842542661223210540645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137826894193190456216773 25842542661223210540645)
        ·
          refine ⟨4845476748979351976371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25842542661223210540645 4845476748979351976371)
          ·
            refine ⟨7268215123469027964557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4845476748979351976371 7268215123469027964557)
            ·
              refine ⟨2725580671300885486709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7268215123469027964557 2725580671300885486709)
              ·
                refine ⟨255523187934458014379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2725580671300885486709 255523187934458014379)
                ·
                  rfl

theorem cell21_3359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 5].length) (baseStart_3359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3359 prefixEnd_3359 := by exact prefixLift 3359
  have htrace : WordTrace (prefixWord ++ tailWord_3359) baseStart_3359 baseEnd_3359 := by
    simpa [prefixWord, tailWord_3359, baseEnd_3359] using wordTrace_append hprefix tailTrace_3359
  have hstable : (prefixWord ++ tailWord_3359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359).length < 2 ^ (prefixWord ++ tailWord_3359).sum := by decide
  have hdescent : baseEnd_3359 < baseStart_3359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390 : List Nat := [4, 2, 1, 2, 1, 1, 1, 6, 3]
def baseStart_3390 : Nat := 118140960795 + 3390 * 2 ^ 59
def prefixEnd_3390 : Nat := 4983230072969 + 3 ^ 40 * 3390 * 2
def baseEnd_3390 : Nat := 773644186154209026407

theorem tailTrace_3390 : CollatzResearch.WordTrace tailWord_3390 prefixEnd_3390 773644186154209026407 := by
  unfold tailWord_3390
  simp only [CollatzResearch.WordTrace]
  refine ⟨15455432215760476376953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82428971817389207343749 15455432215760476376953)
  ·
    refine ⟨11591574161820357282715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15455432215760476376953 11591574161820357282715)
    ·
      refine ⟨17387361242730535924073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11591574161820357282715 17387361242730535924073)
      ·
        refine ⟨13040520932047901943055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17387361242730535924073 13040520932047901943055)
        ·
          refine ⟨19560781398071852914583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13040520932047901943055 19560781398071852914583)
          ·
            refine ⟨29341172097107779371875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19560781398071852914583 29341172097107779371875)
            ·
              refine ⟨44011758145661669057813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29341172097107779371875 44011758145661669057813)
              ·
                refine ⟨2063051163077890737085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44011758145661669057813 2063051163077890737085)
                ·
                  refine ⟨773644186154209026407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2063051163077890737085 773644186154209026407)
                  ·
                    rfl

theorem cell21_3390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_3390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3390 prefixEnd_3390 := by exact prefixLift 3390
  have htrace : WordTrace (prefixWord ++ tailWord_3390) baseStart_3390 baseEnd_3390 := by
    simpa [prefixWord, tailWord_3390, baseEnd_3390] using wordTrace_append hprefix tailTrace_3390
  have hstable : (prefixWord ++ tailWord_3390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390).length < 2 ^ (prefixWord ++ tailWord_3390).sum := by decide
  have hdescent : baseEnd_3390 < baseStart_3390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418 : List Nat := [3, 1, 1, 2, 1, 2, 6, 5]
def baseStart_3418 : Nat := 118140960795 + 3418 * 2 ^ 59
def prefixEnd_3418 : Nat := 4983230072969 + 3 ^ 40 * 3418 * 2
def baseEnd_3418 : Nat := 260011389210794186561

theorem tailTrace_3418 : CollatzResearch.WordTrace tailWord_3418 prefixEnd_3418 260011389210794186561 := by
  unfold tailWord_3418
  simp only [CollatzResearch.WordTrace]
  refine ⟨31166175406161148258727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83109801083096395356605 31166175406161148258727)
  ·
    refine ⟨46749263109241722388091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31166175406161148258727 46749263109241722388091)
    ·
      refine ⟨70123894663862583582137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46749263109241722388091 70123894663862583582137)
      ·
        refine ⟨52592920997896937686603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70123894663862583582137 52592920997896937686603)
        ·
          refine ⟨78889381496845406529905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52592920997896937686603 78889381496845406529905)
          ·
            refine ⟨59167036122634054897429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78889381496845406529905 59167036122634054897429)
            ·
              refine ⟨2773454818248471323317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59167036122634054897429 2773454818248471323317)
              ·
                refine ⟨260011389210794186561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2773454818248471323317 260011389210794186561)
                ·
                  rfl

theorem cell21_3418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_3418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3418 prefixEnd_3418 := by exact prefixLift 3418
  have htrace : WordTrace (prefixWord ++ tailWord_3418) baseStart_3418 baseEnd_3418 := by
    simpa [prefixWord, tailWord_3418, baseEnd_3418] using wordTrace_append hprefix tailTrace_3418
  have hstable : (prefixWord ++ tailWord_3418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418).length < 2 ^ (prefixWord ++ tailWord_3418).sum := by decide
  have hdescent : baseEnd_3418 < baseStart_3418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449 : List Nat := [1, 2, 1, 3, 2, 1, 2, 6, 3]
def baseStart_3449 : Nat := 118140960795 + 3449 * 2 ^ 59
def prefixEnd_3449 : Nat := 4983230072969 + 3 ^ 40 * 3449 * 2
def baseEnd_3449 : Nat := 787108789983217542953

theorem tailTrace_3449 : CollatzResearch.WordTrace tailWord_3449 prefixEnd_3449 787108789983217542953 := by
  unfold tailWord_3449
  simp only [CollatzResearch.WordTrace]
  refine ⟨125795364512336887413401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83863576341557924942267 125795364512336887413401)
  ·
    refine ⟨94346523384252665560051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125795364512336887413401 94346523384252665560051)
    ·
      refine ⟨141519785076378998340077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94346523384252665560051 141519785076378998340077)
      ·
        refine ⟨53069919403642124377529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141519785076378998340077 53069919403642124377529)
        ·
          refine ⟨39802439552731593283147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53069919403642124377529 39802439552731593283147)
          ·
            refine ⟨59703659329097389924721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39802439552731593283147 59703659329097389924721)
            ·
              refine ⟨44777744496823042443541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59703659329097389924721 44777744496823042443541)
              ·
                refine ⟨2098956773288580114541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44777744496823042443541 2098956773288580114541)
                ·
                  refine ⟨787108789983217542953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2098956773288580114541 787108789983217542953)
                  ·
                    rfl

theorem cell21_3449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 3].length) (baseStart_3449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3449 prefixEnd_3449 := by exact prefixLift 3449
  have htrace : WordTrace (prefixWord ++ tailWord_3449) baseStart_3449 baseEnd_3449 := by
    simpa [prefixWord, tailWord_3449, baseEnd_3449] using wordTrace_append hprefix tailTrace_3449
  have hstable : (prefixWord ++ tailWord_3449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449).length < 2 ^ (prefixWord ++ tailWord_3449).sum := by decide
  have hdescent : baseEnd_3449 < baseStart_3449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477 : List Nat := [1, 3, 2, 1, 1, 2, 4, 7]
def baseStart_3477 : Nat := 118140960795 + 3477 * 2 ^ 59
def prefixEnd_3477 : Nat := 4983230072969 + 3 ^ 40 * 3477 * 2
def baseEnd_3477 : Nat := 264499590487130358743

theorem tailTrace_3477 : CollatzResearch.WordTrace tailWord_3477 prefixEnd_3477 264499590487130358743 := by
  unfold tailWord_3477
  simp only [CollatzResearch.WordTrace]
  refine ⟨126816608410897669432685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84544405607265112955123 126816608410897669432685)
  ·
    refine ⟨47556228154086626037257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126816608410897669432685 47556228154086626037257)
    ·
      refine ⟨35667171115564969527943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47556228154086626037257 35667171115564969527943)
      ·
        refine ⟨53500756673347454291915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35667171115564969527943 53500756673347454291915)
        ·
          refine ⟨80251135010021181437873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53500756673347454291915 80251135010021181437873)
          ·
            refine ⟨60188351257515886078405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80251135010021181437873 60188351257515886078405)
            ·
              refine ⟨11285315860784228639701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60188351257515886078405 11285315860784228639701)
              ·
                refine ⟨264499590487130358743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11285315860784228639701 264499590487130358743)
                ·
                  rfl

theorem cell21_3477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 7].length) (baseStart_3477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3477 prefixEnd_3477 := by exact prefixLift 3477
  have htrace : WordTrace (prefixWord ++ tailWord_3477) baseStart_3477 baseEnd_3477 := by
    simpa [prefixWord, tailWord_3477, baseEnd_3477] using wordTrace_append hprefix tailTrace_3477
  have hstable : (prefixWord ++ tailWord_3477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477).length < 2 ^ (prefixWord ++ tailWord_3477).sum := by decide
  have hdescent : baseEnd_3477 < baseStart_3477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553 : List Nat := [1, 2, 3, 1, 2, 4, 8]
def baseStart_3553 : Nat := 118140960795 + 3553 * 2 ^ 59
def prefixEnd_3553 : Nat := 4983230072969 + 3 ^ 40 * 3553 * 2
def baseEnd_3553 : Nat := 90093667433571978823

theorem tailTrace_3553 : CollatzResearch.WordTrace tailWord_3553 prefixEnd_3553 90093667433571978823 := by
  unfold tailWord_3553
  simp only [CollatzResearch.WordTrace]
  refine ⟨129588556135562649199313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86392370757041766132875 129588556135562649199313)
  ·
    refine ⟨97191417101671986899485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129588556135562649199313 97191417101671986899485)
    ·
      refine ⟨36446781413126995087307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97191417101671986899485 36446781413126995087307)
      ·
        refine ⟨54670172119690492630961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36446781413126995087307 54670172119690492630961)
        ·
          refine ⟨41002629089767869473221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54670172119690492630961 41002629089767869473221)
          ·
            refine ⟨7687992954331475526229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41002629089767869473221 7687992954331475526229)
            ·
              refine ⟨90093667433571978823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 7687992954331475526229 90093667433571978823)
              ·
                rfl

theorem cell21_3553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 8].length) (baseStart_3553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3553 prefixEnd_3553 := by exact prefixLift 3553
  have htrace : WordTrace (prefixWord ++ tailWord_3553) baseStart_3553 baseEnd_3553 := by
    simpa [prefixWord, tailWord_3553, baseEnd_3553] using wordTrace_append hprefix tailTrace_3553
  have hstable : (prefixWord ++ tailWord_3553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553).length < 2 ^ (prefixWord ++ tailWord_3553).sum := by decide
  have hdescent : baseEnd_3553 < baseStart_3553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604 : List Nat := [2, 4, 3, 1, 3, 1, 7]
def baseStart_3604 : Nat := 118140960795 + 3604 * 2 ^ 59
def prefixEnd_3604 : Nat := 4983230072969 + 3 ^ 40 * 3604 * 2
def baseEnd_3604 : Nat := 91386877970821384367

theorem tailTrace_3604 : CollatzResearch.WordTrace tailWord_3604 prefixEnd_3604 91386877970821384367 := by
  unfold tailWord_3604
  simp only [CollatzResearch.WordTrace]
  refine ⟨65724339475399179652933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87632452633865572870577 65724339475399179652933)
  ·
    refine ⟨12323313651637346184925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65724339475399179652933 12323313651637346184925)
    ·
      refine ⟨4621242619364004819347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12323313651637346184925 4621242619364004819347)
      ·
        refine ⟨6931863929046007229021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4621242619364004819347 6931863929046007229021)
        ·
          refine ⟨2599448973392252710883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6931863929046007229021 2599448973392252710883)
          ·
            refine ⟨3899173460088379066325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2599448973392252710883 3899173460088379066325)
            ·
              refine ⟨91386877970821384367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3899173460088379066325 91386877970821384367)
              ·
                rfl

theorem cell21_3604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 7].length) (baseStart_3604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3604 prefixEnd_3604 := by exact prefixLift 3604
  have htrace : WordTrace (prefixWord ++ tailWord_3604) baseStart_3604 baseEnd_3604 := by
    simpa [prefixWord, tailWord_3604, baseEnd_3604] using wordTrace_append hprefix tailTrace_3604
  have hstable : (prefixWord ++ tailWord_3604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604).length < 2 ^ (prefixWord ++ tailWord_3604).sum := by decide
  have hdescent : baseEnd_3604 < baseStart_3604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 6]
def baseStart_3674 : Nat := 118140960795 + 3674 * 2 ^ 59
def prefixEnd_3674 : Nat := 4983230072969 + 3 ^ 40 * 3674 * 2
def baseEnd_3674 : Nat := 838456855432826292493

theorem tailTrace_3674 : CollatzResearch.WordTrace tailWord_3674 prefixEnd_3674 838456855432826292493 := by
  unfold tailWord_3674
  simp only [CollatzResearch.WordTrace]
  refine ⟨33500447174300078588519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89334525798133542902717 33500447174300078588519)
  ·
    refine ⟨50250670761450117882779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33500447174300078588519 50250670761450117882779)
    ·
      refine ⟨75376006142175176824169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50250670761450117882779 75376006142175176824169)
      ·
        refine ⟨56532004606631382618127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75376006142175176824169 56532004606631382618127)
        ·
          refine ⟨84798006909947073927191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56532004606631382618127 84798006909947073927191)
          ·
            refine ⟨127197010364920610890787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84798006909947073927191 127197010364920610890787)
            ·
              refine ⟨190795515547380916336181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127197010364920610890787 190795515547380916336181)
              ·
                refine ⟨17887079582566960906517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190795515547380916336181 17887079582566960906517)
                ·
                  refine ⟨838456855432826292493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17887079582566960906517 838456855432826292493)
                  ·
                    rfl

theorem cell21_3674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_3674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3674 prefixEnd_3674 := by exact prefixLift 3674
  have htrace : WordTrace (prefixWord ++ tailWord_3674) baseStart_3674 baseEnd_3674 := by
    simpa [prefixWord, tailWord_3674, baseEnd_3674] using wordTrace_append hprefix tailTrace_3674
  have hstable : (prefixWord ++ tailWord_3674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674).length < 2 ^ (prefixWord ++ tailWord_3674).sum := by decide
  have hdescent : baseEnd_3674 < baseStart_3674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736 : List Nat := [2, 1, 2, 4, 1, 2, 1, 3, 5]
def baseStart_3736 : Nat := 118140960795 + 3736 * 2 ^ 59
def prefixEnd_3736 : Nat := 4983230072969 + 3 ^ 40 * 3736 * 2
def baseEnd_3736 : Nat := 852606100134496259033

theorem tailTrace_3736 : CollatzResearch.WordTrace tailWord_3736 prefixEnd_3736 852606100134496259033 := by
  unfold tailWord_3736
  simp only [CollatzResearch.WordTrace]
  refine ⟨68131557236292451555531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90842076315056602074041 68131557236292451555531)
  ·
    refine ⟨102197335854438677333297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68131557236292451555531 102197335854438677333297)
    ·
      refine ⟨76648001890829007999973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102197335854438677333297 76648001890829007999973)
      ·
        refine ⟨14371500354530438999995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76648001890829007999973 14371500354530438999995)
        ·
          refine ⟨21557250531795658499993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14371500354530438999995 21557250531795658499993)
          ·
            refine ⟨16167937898846743874995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21557250531795658499993 16167937898846743874995)
            ·
              refine ⟨24251906848270115812493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16167937898846743874995 24251906848270115812493)
              ·
                refine ⟨9094465068101293429685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24251906848270115812493 9094465068101293429685)
                ·
                  refine ⟨852606100134496259033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9094465068101293429685 852606100134496259033)
                  ·
                    rfl

theorem cell21_3736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_3736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3736 prefixEnd_3736 := by exact prefixLift 3736
  have htrace : WordTrace (prefixWord ++ tailWord_3736) baseStart_3736 baseEnd_3736 := by
    simpa [prefixWord, tailWord_3736, baseEnd_3736] using wordTrace_append hprefix tailTrace_3736
  have hstable : (prefixWord ++ tailWord_3736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736).length < 2 ^ (prefixWord ++ tailWord_3736).sum := by decide
  have hdescent : baseEnd_3736 < baseStart_3736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3770 : List Nat := [3, 1, 1, 1, 2, 6, 1, 3, 3]
def baseStart_3770 : Nat := 118140960795 + 3770 * 2 ^ 59
def prefixEnd_3770 : Nat := 4983230072969 + 3 ^ 40 * 3770 * 2
def baseEnd_3770 : Nat := 860365363357992692297

theorem tailTrace_3770 : CollatzResearch.WordTrace tailWord_3770 prefixEnd_3770 860365363357992692297 := by
  unfold tailWord_3770
  simp only [CollatzResearch.WordTrace]
  refine ⟨34375799087352177462191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91668797566272473232509 34375799087352177462191)
  ·
    refine ⟨51563698631028266193287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34375799087352177462191 51563698631028266193287)
    ·
      refine ⟨77345547946542399289931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51563698631028266193287 77345547946542399289931)
      ·
        refine ⟨116018321919813598934897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77345547946542399289931 116018321919813598934897)
        ·
          refine ⟨87013741439860199201173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116018321919813598934897 87013741439860199201173)
          ·
            refine ⟨4078769129993446837555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87013741439860199201173 4078769129993446837555)
            ·
              refine ⟨6118153694990170256333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4078769129993446837555 6118153694990170256333)
              ·
                refine ⟨2294307635621313846125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6118153694990170256333 2294307635621313846125)
                ·
                  refine ⟨860365363357992692297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2294307635621313846125 860365363357992692297)
                  ·
                    rfl

theorem cell21_3770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_3770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3770 prefixEnd_3770 := by exact prefixLift 3770
  have htrace : WordTrace (prefixWord ++ tailWord_3770) baseStart_3770 baseEnd_3770 := by
    simpa [prefixWord, tailWord_3770, baseEnd_3770] using wordTrace_append hprefix tailTrace_3770
  have hstable : (prefixWord ++ tailWord_3770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3770).length < 2 ^ (prefixWord ++ tailWord_3770).sum := by decide
  have hdescent : baseEnd_3770 < baseStart_3770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874 : List Nat := [3, 3, 1, 1, 2, 1, 5, 5]
def baseStart_3874 : Nat := 118140960795 + 3874 * 2 ^ 59
def prefixEnd_3874 : Nat := 4983230072969 + 3 ^ 40 * 3874 * 2
def baseEnd_3874 : Nat := 294699860092307652917

theorem tailTrace_3874 : CollatzResearch.WordTrace tailWord_3874 prefixEnd_3874 294699860092307652917 := by
  unfold tailWord_3874
  simp only [CollatzResearch.WordTrace]
  refine ⟨35324096993158617908669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94197591981756314423117 35324096993158617908669)
  ·
    refine ⟨13246536372434481715751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35324096993158617908669 13246536372434481715751)
    ·
      refine ⟨19869804558651722573627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13246536372434481715751 19869804558651722573627)
      ·
        refine ⟨29804706837977583860441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19869804558651722573627 29804706837977583860441)
        ·
          refine ⟨22353530128483187895331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29804706837977583860441 22353530128483187895331)
          ·
            refine ⟨33530295192724781842997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22353530128483187895331 33530295192724781842997)
            ·
              refine ⟨3143465174317948297781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33530295192724781842997 3143465174317948297781)
              ·
                refine ⟨294699860092307652917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3143465174317948297781 294699860092307652917)
                ·
                  rfl

theorem cell21_3874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_3874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3874 prefixEnd_3874 := by exact prefixLift 3874
  have htrace : WordTrace (prefixWord ++ tailWord_3874) baseStart_3874 baseEnd_3874 := by
    simpa [prefixWord, tailWord_3874, baseEnd_3874] using wordTrace_append hprefix tailTrace_3874
  have hstable : (prefixWord ++ tailWord_3874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874).length < 2 ^ (prefixWord ++ tailWord_3874).sum := by decide
  have hdescent : baseEnd_3874 < baseStart_3874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3939 : List Nat := [1, 1, 1, 5, 5, 1, 1, 3, 3]
def baseStart_3939 : Nat := 118140960795 + 3939 * 2 ^ 59
def prefixEnd_3939 : Nat := 4983230072969 + 3 ^ 40 * 3939 * 2
def baseEnd_3939 : Nat := 898933465851254375285

theorem tailTrace_3939 : CollatzResearch.WordTrace tailWord_3939 prefixEnd_3939 898933465851254375285 := by
  unfold tailWord_3939
  simp only [CollatzResearch.WordTrace]
  refine ⟨143667132737150572750871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95778088491433715167247 143667132737150572750871)
  ·
    refine ⟨215500699105725859126307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143667132737150572750871 215500699105725859126307)
    ·
      refine ⟨323251048658588788689461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215500699105725859126307 323251048658588788689461)
      ·
        refine ⟨30304785811742698939637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 323251048658588788689461 30304785811742698939637)
        ·
          refine ⟨2841073669850878025591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30304785811742698939637 2841073669850878025591)
          ·
            refine ⟨4261610504776317038387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2841073669850878025591 4261610504776317038387)
            ·
              refine ⟨6392415757164475557581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261610504776317038387 6392415757164475557581)
              ·
                refine ⟨2397155908936678334093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6392415757164475557581 2397155908936678334093)
                ·
                  refine ⟨898933465851254375285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2397155908936678334093 898933465851254375285)
                  ·
                    rfl

theorem cell21_3939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 3].length) (baseStart_3939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3939 prefixEnd_3939 := by exact prefixLift 3939
  have htrace : WordTrace (prefixWord ++ tailWord_3939) baseStart_3939 baseEnd_3939 := by
    simpa [prefixWord, tailWord_3939, baseEnd_3939] using wordTrace_append hprefix tailTrace_3939
  have hstable : (prefixWord ++ tailWord_3939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3939).length < 2 ^ (prefixWord ++ tailWord_3939).sum := by decide
  have hdescent : baseEnd_3939 < baseStart_3939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950 : List Nat := [4, 1, 2, 3, 1, 3, 7]
def baseStart_3950 : Nat := 118140960795 + 3950 * 2 ^ 59
def prefixEnd_3950 : Nat := 4983230072969 + 3 ^ 40 * 3950 * 2
def baseEnd_3950 : Nat := 100160423968631076881

theorem tailTrace_3950 : CollatzResearch.WordTrace tailWord_3950 prefixEnd_3950 100160423968631076881 := by
  unfold tailWord_3950
  simp only [CollatzResearch.WordTrace]
  refine ⟨18008541962162431425163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96045557131532967600869 18008541962162431425163)
  ·
    refine ⟨27012812943243647137745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18008541962162431425163 27012812943243647137745)
    ·
      refine ⟨20259609707432735353309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27012812943243647137745 20259609707432735353309)
      ·
        refine ⟨7597353640287275757491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20259609707432735353309 7597353640287275757491)
        ·
          refine ⟨11396030460430913636237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7597353640287275757491 11396030460430913636237)
          ·
            refine ⟨4273511422661592613589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11396030460430913636237 4273511422661592613589)
            ·
              refine ⟨100160423968631076881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4273511422661592613589 100160423968631076881)
              ·
                rfl

theorem cell21_3950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 7].length) (baseStart_3950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_3950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_3950 prefixEnd_3950 := by exact prefixLift 3950
  have htrace : WordTrace (prefixWord ++ tailWord_3950) baseStart_3950 baseEnd_3950 := by
    simpa [prefixWord, tailWord_3950, baseEnd_3950] using wordTrace_append hprefix tailTrace_3950
  have hstable : (prefixWord ++ tailWord_3950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950).length < 2 ^ (prefixWord ++ tailWord_3950).sum := by decide
  have hdescent : baseEnd_3950 < baseStart_3950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4023 : List Nat := [1, 1, 3, 1, 3, 1, 1, 5, 5]
def baseStart_4023 : Nat := 118140960795 + 4023 * 2 ^ 59
def prefixEnd_4023 : Nat := 4983230072969 + 3 ^ 40 * 4023 * 2
def baseEnd_4023 : Nat := 918103410285774975113

theorem tailTrace_4023 : CollatzResearch.WordTrace tailWord_4023 prefixEnd_4023 918103410285774975113 := by
  unfold tailWord_4023
  simp only [CollatzResearch.WordTrace]
  refine ⟨146730864432832918808723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97820576288555279205815 146730864432832918808723)
  ·
    refine ⟨220096296649249378213085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146730864432832918808723 220096296649249378213085)
    ·
      refine ⟨82536111243468516829907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220096296649249378213085 82536111243468516829907)
      ·
        refine ⟨123804166865202775244861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82536111243468516829907 123804166865202775244861)
        ·
          refine ⟨46426562574451040716823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123804166865202775244861 46426562574451040716823)
          ·
            refine ⟨69639843861676561075235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46426562574451040716823 69639843861676561075235)
            ·
              refine ⟨104459765792514841612853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69639843861676561075235 104459765792514841612853)
              ·
                refine ⟨9793103043048266401205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104459765792514841612853 9793103043048266401205)
                ·
                  refine ⟨918103410285774975113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9793103043048266401205 918103410285774975113)
                  ·
                    rfl

theorem cell21_4023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 5].length) (baseStart_4023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4023 prefixEnd_4023 := by exact prefixLift 4023
  have htrace : WordTrace (prefixWord ++ tailWord_4023) baseStart_4023 baseEnd_4023 := by
    simpa [prefixWord, tailWord_4023, baseEnd_4023] using wordTrace_append hprefix tailTrace_4023
  have hstable : (prefixWord ++ tailWord_4023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4023).length < 2 ^ (prefixWord ++ tailWord_4023).sum := by decide
  have hdescent : baseEnd_4023 < baseStart_4023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4040 : List Nat := [2, 1, 3, 1, 4, 2, 1, 2, 5]
def baseStart_4040 : Nat := 118140960795 + 4040 * 2 ^ 59
def prefixEnd_4040 : Nat := 4983230072969 + 3 ^ 40 * 4040 * 2
def baseEnd_4040 : Nat := 921983041897523191745

theorem tailTrace_4040 : CollatzResearch.WordTrace tailWord_4040 prefixEnd_4040 921983041897523191745 := by
  unfold tailWord_4040
  simp only [CollatzResearch.WordTrace]
  refine ⟨73675452685622411088787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98233936914163214785049 73675452685622411088787)
  ·
    refine ⟨110513179028433616633181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73675452685622411088787 110513179028433616633181)
    ·
      refine ⟨41442442135662606237443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110513179028433616633181 41442442135662606237443)
      ·
        refine ⟨62163663203493909356165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41442442135662606237443 62163663203493909356165)
        ·
          refine ⟨11655686850655108004281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62163663203493909356165 11655686850655108004281)
          ·
            refine ⟨8741765137991331003211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11655686850655108004281 8741765137991331003211)
            ·
              refine ⟨13112647706986996504817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8741765137991331003211 13112647706986996504817)
              ·
                refine ⟨9834485780240247378613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13112647706986996504817 9834485780240247378613)
                ·
                  refine ⟨921983041897523191745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9834485780240247378613 921983041897523191745)
                  ·
                    rfl

theorem cell21_4040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_4040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4040 prefixEnd_4040 := by exact prefixLift 4040
  have htrace : WordTrace (prefixWord ++ tailWord_4040) baseStart_4040 baseEnd_4040 := by
    simpa [prefixWord, tailWord_4040, baseEnd_4040] using wordTrace_append hprefix tailTrace_4040
  have hstable : (prefixWord ++ tailWord_4040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4040).length < 2 ^ (prefixWord ++ tailWord_4040).sum := by decide
  have hdescent : baseEnd_4040 < baseStart_4040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068 : List Nat := [2, 3, 1, 1, 1, 1, 12]
def baseStart_4068 : Nat := 118140960795 + 4068 * 2 ^ 59
def prefixEnd_4068 : Nat := 4983230072969 + 3 ^ 40 * 4068 * 2
def baseEnd_4068 : Nat := 103152558152855191669

theorem tailTrace_4068 : CollatzResearch.WordTrace tailWord_4068 prefixEnd_4068 103152558152855191669 := by
  unfold tailWord_4068
  simp only [CollatzResearch.WordTrace]
  refine ⟨74186074634902802098429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98914766179870402797905 74186074634902802098429)
  ·
    refine ⟨27819777988088550786911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74186074634902802098429 27819777988088550786911)
    ·
      refine ⟨41729666982132826180367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27819777988088550786911 41729666982132826180367)
      ·
        refine ⟨62594500473199239270551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41729666982132826180367 62594500473199239270551)
        ·
          refine ⟨93891750709798858905827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62594500473199239270551 93891750709798858905827)
          ·
            refine ⟨140837626064698288358741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93891750709798858905827 140837626064698288358741)
            ·
              refine ⟨103152558152855191669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 140837626064698288358741 103152558152855191669)
              ·
                rfl

theorem cell21_4068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 12].length) (baseStart_4068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4068 prefixEnd_4068 := by exact prefixLift 4068
  have htrace : WordTrace (prefixWord ++ tailWord_4068) baseStart_4068 baseEnd_4068 := by
    simpa [prefixWord, tailWord_4068, baseEnd_4068] using wordTrace_append hprefix tailTrace_4068
  have hstable : (prefixWord ++ tailWord_4068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068).length < 2 ^ (prefixWord ++ tailWord_4068).sum := by decide
  have hdescent : baseEnd_4068 < baseStart_4068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4071 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 6]
def baseStart_4071 : Nat := 118140960795 + 4071 * 2 ^ 59
def prefixEnd_4071 : Nat := 4983230072969 + 3 ^ 40 * 4071 * 2
def baseEnd_4071 : Nat := 929057664248358175015

theorem tailTrace_4071 : CollatzResearch.WordTrace tailWord_4071 prefixEnd_4071 929057664248358175015 := by
  unfold tailWord_4071
  simp only [CollatzResearch.WordTrace]
  refine ⟨148481568258937116556067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98987712172624744370711 148481568258937116556067)
  ·
    refine ⟨222722352388405674834101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148481568258937116556067 222722352388405674834101)
    ·
      refine ⟨20880220536413032015697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222722352388405674834101 20880220536413032015697)
      ·
        refine ⟨15660165402309774011773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20880220536413032015697 15660165402309774011773)
        ·
          refine ⟨5872562025866165254415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15660165402309774011773 5872562025866165254415)
          ·
            refine ⟨8808843038799247881623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5872562025866165254415 8808843038799247881623)
            ·
              refine ⟨13213264558198871822435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8808843038799247881623 13213264558198871822435)
              ·
                refine ⟨19819896837298307733653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13213264558198871822435 19819896837298307733653)
                ·
                  refine ⟨929057664248358175015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19819896837298307733653 929057664248358175015)
                  ·
                    rfl

theorem cell21_4071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 6].length) (baseStart_4071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4071 prefixEnd_4071 := by exact prefixLift 4071
  have htrace : WordTrace (prefixWord ++ tailWord_4071) baseStart_4071 baseEnd_4071 := by
    simpa [prefixWord, tailWord_4071, baseEnd_4071] using wordTrace_append hprefix tailTrace_4071
  have hstable : (prefixWord ++ tailWord_4071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4071).length < 2 ^ (prefixWord ++ tailWord_4071).sum := by decide
  have hdescent : baseEnd_4071 < baseStart_4071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 6]
def baseStart_4130 : Nat := 118140960795 + 4130 * 2 ^ 59
def prefixEnd_4130 : Nat := 4983230072969 + 3 ^ 40 * 4130 * 2
def baseEnd_4130 : Nat := 942522268077366691561

theorem tailTrace_4130 : CollatzResearch.WordTrace tailWord_4130 prefixEnd_4130 942522268077366691561 := by
  unfold tailWord_4130
  simp only [CollatzResearch.WordTrace]
  refine ⟨37658368761297548238461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100422316696793461969229 37658368761297548238461)
  ·
    refine ⟨14121888285486580589423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37658368761297548238461 14121888285486580589423)
    ·
      refine ⟨21182832428229870884135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14121888285486580589423 21182832428229870884135)
      ·
        refine ⟨31774248642344806326203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21182832428229870884135 31774248642344806326203)
        ·
          refine ⟨47661372963517209489305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31774248642344806326203 47661372963517209489305)
          ·
            refine ⟨35746029722637907116979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47661372963517209489305 35746029722637907116979)
            ·
              refine ⟨53619044583956860675469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35746029722637907116979 53619044583956860675469)
              ·
                refine ⟨20107141718983822753301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53619044583956860675469 20107141718983822753301)
                ·
                  refine ⟨942522268077366691561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20107141718983822753301 942522268077366691561)
                  ·
                    rfl

theorem cell21_4130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_4130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4130 prefixEnd_4130 := by exact prefixLift 4130
  have htrace : WordTrace (prefixWord ++ tailWord_4130) baseStart_4130 baseEnd_4130 := by
    simpa [prefixWord, tailWord_4130, baseEnd_4130] using wordTrace_append hprefix tailTrace_4130
  have hstable : (prefixWord ++ tailWord_4130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130).length < 2 ^ (prefixWord ++ tailWord_4130).sum := by decide
  have hdescent : baseEnd_4130 < baseStart_4130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144 : List Nat := [2, 1, 1, 1, 2, 5, 1, 8]
def baseStart_4144 : Nat := 118140960795 + 4144 * 2 ^ 59
def prefixEnd_4144 : Nat := 4983230072969 + 3 ^ 40 * 4144 * 2
def baseEnd_4144 : Nat := 315239086272151152733

theorem tailTrace_4144 : CollatzResearch.WordTrace tailWord_4144 prefixEnd_4144 315239086272151152733 := by
  unfold tailWord_4144
  simp only [CollatzResearch.WordTrace]
  refine ⟨75572048497235291981743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100762731329647055975657 75572048497235291981743)
  ·
    refine ⟨113358072745852937972615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75572048497235291981743 113358072745852937972615)
    ·
      refine ⟨170037109118779406958923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113358072745852937972615 170037109118779406958923)
      ·
        refine ⟨255055663678169110438385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170037109118779406958923 255055663678169110438385)
        ·
          refine ⟨191291747758626832828789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255055663678169110438385 191291747758626832828789)
          ·
            refine ⟨17933601352371265577699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191291747758626832828789 17933601352371265577699)
            ·
              refine ⟨26900402028556898366549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17933601352371265577699 26900402028556898366549)
              ·
                refine ⟨315239086272151152733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 26900402028556898366549 315239086272151152733)
                ·
                  rfl

theorem cell21_4144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 8].length) (baseStart_4144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4144 prefixEnd_4144 := by exact prefixLift 4144
  have htrace : WordTrace (prefixWord ++ tailWord_4144) baseStart_4144 baseEnd_4144 := by
    simpa [prefixWord, tailWord_4144, baseEnd_4144] using wordTrace_append hprefix tailTrace_4144
  have hstable : (prefixWord ++ tailWord_4144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144).length < 2 ^ (prefixWord ++ tailWord_4144).sum := by decide
  have hdescent : baseEnd_4144 < baseStart_4144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147 : List Nat := [1, 1, 1, 2, 4, 1, 6, 1, 4]
def baseStart_4147 : Nat := 118140960795 + 4147 * 2 ^ 59
def prefixEnd_4147 : Nat := 4983230072969 + 3 ^ 40 * 4147 * 2
def baseEnd_4147 : Nat := 946401899689114908193

theorem tailTrace_4147 : CollatzResearch.WordTrace tailWord_4147 prefixEnd_4147 946401899689114908193 := by
  unfold tailWord_4147
  simp only [CollatzResearch.WordTrace]
  refine ⟨151253515983602096322695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100835677322401397548463 151253515983602096322695)
  ·
    refine ⟨226880273975403144484043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151253515983602096322695 226880273975403144484043)
    ·
      refine ⟨340320410963104716726065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226880273975403144484043 340320410963104716726065)
      ·
        refine ⟨255240308222328537544549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340320410963104716726065 255240308222328537544549)
        ·
          refine ⟨47857557791686600789603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255240308222328537544549 47857557791686600789603)
          ·
            refine ⟨71786336687529901184405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47857557791686600789603 71786336687529901184405)
            ·
              refine ⟨3364984532227964118019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71786336687529901184405 3364984532227964118019)
              ·
                refine ⟨5047476798341946177029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3364984532227964118019 5047476798341946177029)
                ·
                  refine ⟨946401899689114908193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5047476798341946177029 946401899689114908193)
                  ·
                    rfl

theorem cell21_4147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 4].length) (baseStart_4147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4147 prefixEnd_4147 := by exact prefixLift 4147
  have htrace : WordTrace (prefixWord ++ tailWord_4147) baseStart_4147 baseEnd_4147 := by
    simpa [prefixWord, tailWord_4147, baseEnd_4147] using wordTrace_append hprefix tailTrace_4147
  have hstable : (prefixWord ++ tailWord_4147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147).length < 2 ^ (prefixWord ++ tailWord_4147).sum := by decide
  have hdescent : baseEnd_4147 < baseStart_4147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161 : List Nat := [1, 2, 5, 1, 2, 1, 2, 7]
def baseStart_4161 : Nat := 118140960795 + 4161 * 2 ^ 59
def prefixEnd_4161 : Nat := 4983230072969 + 3 ^ 40 * 4161 * 2
def baseEnd_4161 : Nat := 316532296809400558277

theorem tailTrace_4161 : CollatzResearch.WordTrace tailWord_4161 prefixEnd_4161 316532296809400558277 := by
  unfold tailWord_4161
  simp only [CollatzResearch.WordTrace]
  refine ⟨151764137932882487332337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101176091955254991554891 151764137932882487332337)
  ·
    refine ⟨113823103449661865499253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151764137932882487332337 113823103449661865499253)
    ·
      refine ⟨10670915948405799890555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113823103449661865499253 10670915948405799890555)
      ·
        refine ⟨16006373922608699835833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10670915948405799890555 16006373922608699835833)
        ·
          refine ⟨12004780441956524876875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16006373922608699835833 12004780441956524876875)
          ·
            refine ⟨18007170662934787315313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12004780441956524876875 18007170662934787315313)
            ·
              refine ⟨13505377997201090486485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18007170662934787315313 13505377997201090486485)
              ·
                refine ⟨316532296809400558277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13505377997201090486485 316532296809400558277)
                ·
                  rfl

theorem cell21_4161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 7].length) (baseStart_4161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4161 prefixEnd_4161 := by exact prefixLift 4161
  have htrace : WordTrace (prefixWord ++ tailWord_4161) baseStart_4161 baseEnd_4161 := by
    simpa [prefixWord, tailWord_4161, baseEnd_4161] using wordTrace_append hprefix tailTrace_4161
  have hstable : (prefixWord ++ tailWord_4161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161).length < 2 ^ (prefixWord ++ tailWord_4161).sum := by decide
  have hdescent : baseEnd_4161 < baseStart_4161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302 : List Nat := [4, 1, 1, 1, 4, 2, 3, 2, 3]
def baseStart_4302 : Nat := 118140960795 + 4302 * 2 ^ 59
def prefixEnd_4302 : Nat := 4983230072969 + 3 ^ 40 * 4302 * 2
def baseEnd_4302 : Nat := 981775011443289824543

theorem tailTrace_4302 : CollatzResearch.WordTrace tailWord_4302 prefixEnd_4302 981775011443289824543 := by
  unfold tailWord_4302
  simp only [CollatzResearch.WordTrace]
  refine ⟨19613353802757946026895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104604553614709045476773 19613353802757946026895)
  ·
    refine ⟨29420030704136919040343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19613353802757946026895 29420030704136919040343)
    ·
      refine ⟨44130046056205378560515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29420030704136919040343 44130046056205378560515)
      ·
        refine ⟨66195069084308067840773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44130046056205378560515 66195069084308067840773)
        ·
          refine ⟨12411575453307762720145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66195069084308067840773 12411575453307762720145)
          ·
            refine ⟨9308681589980822040109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12411575453307762720145 9308681589980822040109)
            ·
              refine ⟨3490755596242808265041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9308681589980822040109 3490755596242808265041)
              ·
                refine ⟨2618066697182106198781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3490755596242808265041 2618066697182106198781)
                ·
                  refine ⟨981775011443289824543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2618066697182106198781 981775011443289824543)
                  ·
                    rfl

theorem cell21_4302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_4302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4302 prefixEnd_4302 := by exact prefixLift 4302
  have htrace : WordTrace (prefixWord ++ tailWord_4302) baseStart_4302 baseEnd_4302 := by
    simpa [prefixWord, tailWord_4302, baseEnd_4302] using wordTrace_append hprefix tailTrace_4302
  have hstable : (prefixWord ++ tailWord_4302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302).length < 2 ^ (prefixWord ++ tailWord_4302).sum := by decide
  have hdescent : baseEnd_4302 < baseStart_4302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361 : List Nat := [1, 2, 1, 1, 3, 4, 4, 2, 3]
def baseStart_4361 : Nat := 118140960795 + 4361 * 2 ^ 59
def prefixEnd_4361 : Nat := 4983230072969 + 3 ^ 40 * 4361 * 2
def baseEnd_4361 : Nat := 995239615272298341089

theorem tailTrace_4361 : CollatzResearch.WordTrace tailWord_4361 prefixEnd_4361 995239615272298341089 := by
  unfold tailWord_4361
  simp only [CollatzResearch.WordTrace]
  refine ⟨159058737208316644612937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106039158138877763075291 159058737208316644612937)
  ·
    refine ⟨119294052906237483459703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159058737208316644612937 119294052906237483459703)
    ·
      refine ⟨178941079359356225189555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119294052906237483459703 178941079359356225189555)
      ·
        refine ⟨268411619039034337784333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178941079359356225189555 268411619039034337784333)
        ·
          refine ⟨100654357139637876669125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268411619039034337784333 100654357139637876669125)
          ·
            refine ⟨18872691963682101875461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100654357139637876669125 18872691963682101875461)
            ·
              refine ⟨3538629743190394101649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18872691963682101875461 3538629743190394101649)
              ·
                refine ⟨2653972307392795576237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3538629743190394101649 2653972307392795576237)
                ·
                  refine ⟨995239615272298341089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2653972307392795576237 995239615272298341089)
                  ·
                    rfl

theorem cell21_4361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 3].length) (baseStart_4361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4361 prefixEnd_4361 := by exact prefixLift 4361
  have htrace : WordTrace (prefixWord ++ tailWord_4361) baseStart_4361 baseEnd_4361 := by
    simpa [prefixWord, tailWord_4361, baseEnd_4361] using wordTrace_append hprefix tailTrace_4361
  have hstable : (prefixWord ++ tailWord_4361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361).length < 2 ^ (prefixWord ++ tailWord_4361).sum := by decide
  have hdescent : baseEnd_4361 < baseStart_4361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4434 : List Nat := [3, 2, 2, 1, 1, 1, 2, 5, 4]
def baseStart_4434 : Nat := 118140960795 + 4434 * 2 ^ 59
def prefixEnd_4434 : Nat := 4983230072969 + 3 ^ 40 * 4434 * 2
def baseEnd_4434 : Nat := 1011899209840393624273

theorem tailTrace_4434 : CollatzResearch.WordTrace tailWord_4434 prefixEnd_4434 1011899209840393624273 := by
  unfold tailWord_4434
  simp only [CollatzResearch.WordTrace]
  refine ⟨40430316485962528005089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107814177295900074680237 40430316485962528005089)
  ·
    refine ⟨30322737364471896003817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40430316485962528005089 30322737364471896003817)
    ·
      refine ⟨22742053023353922002863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30322737364471896003817 22742053023353922002863)
      ·
        refine ⟨34113079535030883004295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22742053023353922002863 34113079535030883004295)
        ·
          refine ⟨51169619302546324506443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34113079535030883004295 51169619302546324506443)
          ·
            refine ⟨76754428953819486759665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51169619302546324506443 76754428953819486759665)
            ·
              refine ⟨57565821715364615069749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76754428953819486759665 57565821715364615069749)
              ·
                refine ⟨5396795785815432662789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57565821715364615069749 5396795785815432662789)
                ·
                  refine ⟨1011899209840393624273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5396795785815432662789 1011899209840393624273)
                  ·
                    rfl

theorem cell21_4434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_4434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4434 prefixEnd_4434 := by exact prefixLift 4434
  have htrace : WordTrace (prefixWord ++ tailWord_4434) baseStart_4434 baseEnd_4434 := by
    simpa [prefixWord, tailWord_4434, baseEnd_4434] using wordTrace_append hprefix tailTrace_4434
  have hstable : (prefixWord ++ tailWord_4434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4434).length < 2 ^ (prefixWord ++ tailWord_4434).sum := by decide
  have hdescent : baseEnd_4434 < baseStart_4434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4446 : List Nat := [4, 4, 2, 1, 2, 1, 1, 3, 3]
def baseStart_4446 : Nat := 118140960795 + 4446 * 2 ^ 59
def prefixEnd_4446 : Nat := 4983230072969 + 3 ^ 40 * 4446 * 2
def baseEnd_4446 : Nat := 1014637773331039424249

theorem tailTrace_4446 : CollatzResearch.WordTrace tailWord_4446 prefixEnd_4446 1014637773331039424249 := by
  unfold tailWord_4446
  simp only [CollatzResearch.WordTrace]
  refine ⟨20269867737547020182149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108105961266917440971461 20269867737547020182149)
  ·
    refine ⟨3800600200790066284153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20269867737547020182149 3800600200790066284153)
    ·
      refine ⟨2850450150592549713115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3800600200790066284153 2850450150592549713115)
      ·
        refine ⟨4275675225888824569673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2850450150592549713115 4275675225888824569673)
        ·
          refine ⟨3206756419416618427255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4275675225888824569673 3206756419416618427255)
          ·
            refine ⟨4810134629124927640883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3206756419416618427255 4810134629124927640883)
            ·
              refine ⟨7215201943687391461325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4810134629124927640883 7215201943687391461325)
              ·
                refine ⟨2705700728882771797997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7215201943687391461325 2705700728882771797997)
                ·
                  refine ⟨1014637773331039424249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2705700728882771797997 1014637773331039424249)
                  ·
                    rfl

theorem cell21_4446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_4446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4446 prefixEnd_4446 := by exact prefixLift 4446
  have htrace : WordTrace (prefixWord ++ tailWord_4446) baseStart_4446 baseEnd_4446 := by
    simpa [prefixWord, tailWord_4446, baseEnd_4446] using wordTrace_append hprefix tailTrace_4446
  have hstable : (prefixWord ++ tailWord_4446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4446).length < 2 ^ (prefixWord ++ tailWord_4446).sum := by decide
  have hdescent : baseEnd_4446 < baseStart_4446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4538 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 9]
def baseStart_4538 : Nat := 118140960795 + 4538 * 2 ^ 59
def prefixEnd_4538 : Nat := 4983230072969 + 3 ^ 40 * 4538 * 2
def baseEnd_4538 : Nat := 1035633426759323890727

theorem tailTrace_4538 : CollatzResearch.WordTrace tailWord_4538 prefixEnd_4538 1035633426759323890727 := by
  unfold tailWord_4538
  simp only [CollatzResearch.WordTrace]
  refine ⟨41378614391768968451567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110342971711383915870845 41378614391768968451567)
  ·
    refine ⟨62067921587653452677351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41378614391768968451567 62067921587653452677351)
    ·
      refine ⟨93101882381480179016027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62067921587653452677351 93101882381480179016027)
      ·
        refine ⟨139652823572220268524041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93101882381480179016027 139652823572220268524041)
        ·
          refine ⟨104739617679165201393031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139652823572220268524041 104739617679165201393031)
          ·
            refine ⟨157109426518747802089547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104739617679165201393031 157109426518747802089547)
            ·
              refine ⟨235664139778121703134321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157109426518747802089547 235664139778121703134321)
              ·
                refine ⟨176748104833591277350741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235664139778121703134321 176748104833591277350741)
                ·
                  refine ⟨1035633426759323890727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 176748104833591277350741 1035633426759323890727)
                  ·
                    rfl

theorem cell21_4538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_4538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4538 prefixEnd_4538 := by exact prefixLift 4538
  have htrace : WordTrace (prefixWord ++ tailWord_4538) baseStart_4538 baseEnd_4538 := by
    simpa [prefixWord, tailWord_4538, baseEnd_4538] using wordTrace_append hprefix tailTrace_4538
  have hstable : (prefixWord ++ tailWord_4538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4538).length < 2 ^ (prefixWord ++ tailWord_4538).sum := by decide
  have hdescent : baseEnd_4538 < baseStart_4538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541 : List Nat := [1, 4, 1, 2, 2, 4, 1, 6]
def baseStart_4541 : Nat := 118140960795 + 4541 * 2 ^ 59
def prefixEnd_4541 : Nat := 4983230072969 + 3 ^ 40 * 4541 * 2
def baseEnd_4541 : Nat := 345439355877328446907

theorem tailTrace_4541 : CollatzResearch.WordTrace tailWord_4541 prefixEnd_4541 345439355877328446907 := by
  unfold tailWord_4541
  simp only [CollatzResearch.WordTrace]
  refine ⟨165623876556207386165477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110415917704138257443651 165623876556207386165477)
  ·
    refine ⟨31054476854288884906027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165623876556207386165477 31054476854288884906027)
    ·
      refine ⟨46581715281433327359041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31054476854288884906027 46581715281433327359041)
      ·
        refine ⟨34936286461074995519281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46581715281433327359041 34936286461074995519281)
        ·
          refine ⟨26202214845806246639461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34936286461074995519281 26202214845806246639461)
          ·
            refine ⟨4912915283588671244899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26202214845806246639461 4912915283588671244899)
            ·
              refine ⟨7369372925383006867349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4912915283588671244899 7369372925383006867349)
              ·
                refine ⟨345439355877328446907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7369372925383006867349 345439355877328446907)
                ·
                  rfl

theorem cell21_4541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 6].length) (baseStart_4541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4541 prefixEnd_4541 := by exact prefixLift 4541
  have htrace : WordTrace (prefixWord ++ tailWord_4541) baseStart_4541 baseEnd_4541 := by
    simpa [prefixWord, tailWord_4541, baseEnd_4541] using wordTrace_append hprefix tailTrace_4541
  have hstable : (prefixWord ++ tailWord_4541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541).length < 2 ^ (prefixWord ++ tailWord_4541).sum := by decide
  have hdescent : baseEnd_4541 < baseStart_4541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4569 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 6]
def baseStart_4569 : Nat := 118140960795 + 4569 * 2 ^ 59
def prefixEnd_4569 : Nat := 4983230072969 + 3 ^ 40 * 4569 * 2
def baseEnd_4569 : Nat := 1042708049110158873997

theorem tailTrace_4569 : CollatzResearch.WordTrace tailWord_4569 prefixEnd_4569 1042708049110158873997 := by
  unfold tailWord_4569
  simp only [CollatzResearch.WordTrace]
  refine ⟨166645120454768168184761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111096746969845445456507 166645120454768168184761)
  ·
    refine ⟨124983840341076126138571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166645120454768168184761 124983840341076126138571)
    ·
      refine ⟨187475760511614189207857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124983840341076126138571 187475760511614189207857)
      ·
        refine ⟨140606820383710641905893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187475760511614189207857 140606820383710641905893)
        ·
          refine ⟨26363778821945745357355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140606820383710641905893 26363778821945745357355)
          ·
            refine ⟨39545668232918618036033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26363778821945745357355 39545668232918618036033)
            ·
              refine ⟨29659251174688963527025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39545668232918618036033 29659251174688963527025)
              ·
                refine ⟨22244438381016722645269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29659251174688963527025 22244438381016722645269)
                ·
                  refine ⟨1042708049110158873997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22244438381016722645269 1042708049110158873997)
                  ·
                    rfl

theorem cell21_4569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_4569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4569 prefixEnd_4569 := by exact prefixLift 4569
  have htrace : WordTrace (prefixWord ++ tailWord_4569) baseStart_4569 baseEnd_4569 := by
    simpa [prefixWord, tailWord_4569, baseEnd_4569] using wordTrace_append hprefix tailTrace_4569
  have hstable : (prefixWord ++ tailWord_4569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4569).length < 2 ^ (prefixWord ++ tailWord_4569).sum := by decide
  have hdescent : baseEnd_4569 < baseStart_4569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4578 : List Nat := [3, 3, 3, 2, 2, 1, 1, 2, 4]
def baseStart_4578 : Nat := 118140960795 + 4578 * 2 ^ 59
def prefixEnd_4578 : Nat := 4983230072969 + 3 ^ 40 * 4578 * 2
def baseEnd_4578 : Nat := 1044761971728143223979

theorem tailTrace_4578 : CollatzResearch.WordTrace tailWord_4578 prefixEnd_4578 1044761971728143223979 := by
  unfold tailWord_4578
  simp only [CollatzResearch.WordTrace]
  refine ⟨41743344355540676315597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111315584948108470174925 41743344355540676315597)
  ·
    refine ⟨15653754133327753618349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41743344355540676315597 15653754133327753618349)
    ·
      refine ⟨5870157799997907606881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15653754133327753618349 5870157799997907606881)
      ·
        refine ⟨4402618349998430705161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5870157799997907606881 4402618349998430705161)
        ·
          refine ⟨3301963762498823028871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4402618349998430705161 3301963762498823028871)
          ·
            refine ⟨4952945643748234543307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3301963762498823028871 4952945643748234543307)
            ·
              refine ⟨7429418465622351814961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4952945643748234543307 7429418465622351814961)
              ·
                refine ⟨5572063849216763861221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7429418465622351814961 5572063849216763861221)
                ·
                  refine ⟨1044761971728143223979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5572063849216763861221 1044761971728143223979)
                  ·
                    rfl

theorem cell21_4578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_4578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4578 prefixEnd_4578 := by exact prefixLift 4578
  have htrace : WordTrace (prefixWord ++ tailWord_4578) baseStart_4578 baseEnd_4578 := by
    simpa [prefixWord, tailWord_4578, baseEnd_4578] using wordTrace_append hprefix tailTrace_4578
  have hstable : (prefixWord ++ tailWord_4578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4578).length < 2 ^ (prefixWord ++ tailWord_4578).sum := by decide
  have hdescent : baseEnd_4578 < baseStart_4578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 6]
def baseStart_4586 : Nat := 118140960795 + 4586 * 2 ^ 59
def prefixEnd_4586 : Nat := 4983230072969 + 3 ^ 40 * 4586 * 2
def baseEnd_4586 : Nat := 1046587680721907090629

theorem tailTrace_4586 : CollatzResearch.WordTrace tailWord_4586 prefixEnd_4586 1046587680721907090629 := by
  unfold tailWord_4586
  simp only [CollatzResearch.WordTrace]
  refine ⟨41816290348295017888403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111510107595453381035741 41816290348295017888403)
  ·
    refine ⟨62724435522442526832605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41816290348295017888403 62724435522442526832605)
    ·
      refine ⟨23521663320915947562227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62724435522442526832605 23521663320915947562227)
      ·
        refine ⟨35282494981373921343341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23521663320915947562227 35282494981373921343341)
        ·
          refine ⟨13230935618015220503753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35282494981373921343341 13230935618015220503753)
          ·
            refine ⟨9923201713511415377815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13230935618015220503753 9923201713511415377815)
            ·
              refine ⟨14884802570267123066723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9923201713511415377815 14884802570267123066723)
              ·
                refine ⟨22327203855400684600085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14884802570267123066723 22327203855400684600085)
                ·
                  refine ⟨1046587680721907090629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22327203855400684600085 1046587680721907090629)
                  ·
                    rfl

theorem cell21_4586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_4586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4586 prefixEnd_4586 := by exact prefixLift 4586
  have htrace : WordTrace (prefixWord ++ tailWord_4586) baseStart_4586 baseEnd_4586 := by
    simpa [prefixWord, tailWord_4586, baseEnd_4586] using wordTrace_append hprefix tailTrace_4586
  have hstable : (prefixWord ++ tailWord_4586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586).length < 2 ^ (prefixWord ++ tailWord_4586).sum := by decide
  have hdescent : baseEnd_4586 < baseStart_4586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589 : List Nat := [1, 5, 1, 3, 1, 1, 2, 4, 3]
def baseStart_4589 : Nat := 118140960795 + 4589 * 2 ^ 59
def prefixEnd_4589 : Nat := 4983230072969 + 3 ^ 40 * 4589 * 2
def baseEnd_4589 : Nat := 1047272321594568540623

theorem tailTrace_4589 : CollatzResearch.WordTrace tailWord_4589 prefixEnd_4589 1047272321594568540623 := by
  unfold tailWord_4589
  simp only [CollatzResearch.WordTrace]
  refine ⟨167374580382311583912821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111583053588207722608547 167374580382311583912821)
  ·
    refine ⟨15691366910841710991827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167374580382311583912821 15691366910841710991827)
    ·
      refine ⟨23537050366262566487741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15691366910841710991827 23537050366262566487741)
      ·
        refine ⟨8826393887348462432903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23537050366262566487741 8826393887348462432903)
        ·
          refine ⟨13239590831022693649355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8826393887348462432903 13239590831022693649355)
          ·
            refine ⟨19859386246534040474033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13239590831022693649355 19859386246534040474033)
            ·
              refine ⟨14894539684900530355525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19859386246534040474033 14894539684900530355525)
              ·
                refine ⟨2792726190918849441661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14894539684900530355525 2792726190918849441661)
                ·
                  refine ⟨1047272321594568540623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2792726190918849441661 1047272321594568540623)
                  ·
                    rfl

theorem cell21_4589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_4589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4589 prefixEnd_4589 := by exact prefixLift 4589
  have htrace : WordTrace (prefixWord ++ tailWord_4589) baseStart_4589 baseEnd_4589 := by
    simpa [prefixWord, tailWord_4589, baseEnd_4589] using wordTrace_append hprefix tailTrace_4589
  have hstable : (prefixWord ++ tailWord_4589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589).length < 2 ^ (prefixWord ++ tailWord_4589).sum := by decide
  have hdescent : baseEnd_4589 < baseStart_4589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 6]
def baseStart_4645 : Nat := 118140960795 + 4645 * 2 ^ 59
def prefixEnd_4645 : Nat := 4983230072969 + 3 ^ 40 * 4645 * 2
def baseEnd_4645 : Nat := 1060052284550915607175

theorem tailTrace_4645 : CollatzResearch.WordTrace tailWord_4645 prefixEnd_4645 1060052284550915607175 := by
  unfold tailWord_4645
  simp only [CollatzResearch.WordTrace]
  refine ⟨169417068179433147951389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112944712119622098634259 169417068179433147951389)
  ·
    refine ⟨63531400567287430481771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169417068179433147951389 63531400567287430481771)
    ·
      refine ⟨95297100850931145722657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63531400567287430481771 95297100850931145722657)
      ·
        refine ⟨71472825638198359291993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95297100850931145722657 71472825638198359291993)
        ·
          refine ⟨53604619228648769468995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71472825638198359291993 53604619228648769468995)
          ·
            refine ⟨80406928842973154203493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53604619228648769468995 80406928842973154203493)
            ·
              refine ⟨15076299158057466413155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80406928842973154203493 15076299158057466413155)
              ·
                refine ⟨22614448737086199619733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15076299158057466413155 22614448737086199619733)
                ·
                  refine ⟨1060052284550915607175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22614448737086199619733 1060052284550915607175)
                  ·
                    rfl

theorem cell21_4645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_4645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4645 prefixEnd_4645 := by exact prefixLift 4645
  have htrace : WordTrace (prefixWord ++ tailWord_4645) baseStart_4645 baseEnd_4645 := by
    simpa [prefixWord, tailWord_4645, baseEnd_4645] using wordTrace_append hprefix tailTrace_4645
  have hstable : (prefixWord ++ tailWord_4645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645).length < 2 ^ (prefixWord ++ tailWord_4645).sum := by decide
  have hdescent : baseEnd_4645 < baseStart_4645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648 : List Nat := [2, 1, 5, 2, 1, 1, 3, 1, 5]
def baseStart_4648 : Nat := 118140960795 + 4648 * 2 ^ 59
def prefixEnd_4648 : Nat := 4983230072969 + 3 ^ 40 * 4648 * 2
def baseEnd_4648 : Nat := 1060736925423577057169

theorem tailTrace_4648 : CollatzResearch.WordTrace tailWord_4648 prefixEnd_4648 1060736925423577057169 := by
  unfold tailWord_4648
  simp only [CollatzResearch.WordTrace]
  refine ⟨84763243584282330155299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113017658112376440207065 84763243584282330155299)
  ·
    refine ⟨127144865376423495232949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84763243584282330155299 127144865376423495232949)
    ·
      refine ⟨11919831129039702678089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127144865376423495232949 11919831129039702678089)
      ·
        refine ⟨8939873346779777008567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11919831129039702678089 8939873346779777008567)
        ·
          refine ⟨13409810020169665512851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8939873346779777008567 13409810020169665512851)
          ·
            refine ⟨20114715030254498269277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13409810020169665512851 20114715030254498269277)
            ·
              refine ⟨7543018136345436850979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20114715030254498269277 7543018136345436850979)
              ·
                refine ⟨11314527204518155276469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7543018136345436850979 11314527204518155276469)
                ·
                  refine ⟨1060736925423577057169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11314527204518155276469 1060736925423577057169)
                  ·
                    rfl

theorem cell21_4648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_4648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4648 prefixEnd_4648 := by exact prefixLift 4648
  have htrace : WordTrace (prefixWord ++ tailWord_4648) baseStart_4648 baseEnd_4648 := by
    simpa [prefixWord, tailWord_4648, baseEnd_4648] using wordTrace_append hprefix tailTrace_4648
  have hstable : (prefixWord ++ tailWord_4648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648).length < 2 ^ (prefixWord ++ tailWord_4648).sum := by decide
  have hdescent : baseEnd_4648 < baseStart_4648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 6]
def baseStart_4797 : Nat := 118140960795 + 4797 * 2 ^ 59
def prefixEnd_4797 : Nat := 4983230072969 + 3 ^ 40 * 4797 * 2
def baseEnd_4797 : Nat := 1094740755432429073531

theorem tailTrace_4797 : CollatzResearch.WordTrace tailWord_4797 prefixEnd_4797 1094740755432429073531 := by
  unfold tailWord_4797
  simp only [CollatzResearch.WordTrace]
  refine ⟨174960963628763107484645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116640642419175404989763 174960963628763107484645)
  ·
    refine ⟨32805180680393082653371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174960963628763107484645 32805180680393082653371)
    ·
      refine ⟨49207771020589623980057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32805180680393082653371 49207771020589623980057)
      ·
        refine ⟨36905828265442217985043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49207771020589623980057 36905828265442217985043)
        ·
          refine ⟨55358742398163326977565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36905828265442217985043 55358742398163326977565)
          ·
            refine ⟨20759528399311247616587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55358742398163326977565 20759528399311247616587)
            ·
              refine ⟨31139292598966871424881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20759528399311247616587 31139292598966871424881)
              ·
                refine ⟨23354469449225153568661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31139292598966871424881 23354469449225153568661)
                ·
                  refine ⟨1094740755432429073531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23354469449225153568661 1094740755432429073531)
                  ·
                    rfl

theorem cell21_4797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_4797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4797 prefixEnd_4797 := by exact prefixLift 4797
  have htrace : WordTrace (prefixWord ++ tailWord_4797) baseStart_4797 baseEnd_4797 := by
    simpa [prefixWord, tailWord_4797, baseEnd_4797] using wordTrace_append hprefix tailTrace_4797
  have hstable : (prefixWord ++ tailWord_4797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797).length < 2 ^ (prefixWord ++ tailWord_4797).sum := by decide
  have hdescent : baseEnd_4797 < baseStart_4797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800 : List Nat := [2, 1, 1, 2, 4, 2, 3, 3, 3]
def baseStart_4800 : Nat := 118140960795 + 4800 * 2 ^ 59
def prefixEnd_4800 : Nat := 4983230072969 + 3 ^ 40 * 4800 * 2
def baseEnd_4800 : Nat := 1095425396305090523525

theorem tailTrace_4800 : CollatzResearch.WordTrace tailWord_4800 prefixEnd_4800 1095425396305090523525 := by
  unfold tailWord_4800
  simp only [CollatzResearch.WordTrace]
  refine ⟨87535191308947309921927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116713588411929746562569 87535191308947309921927)
  ·
    refine ⟨131302786963420964882891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87535191308947309921927 131302786963420964882891)
    ·
      refine ⟨196954180445131447324337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131302786963420964882891 196954180445131447324337)
      ·
        refine ⟨147715635333848585493253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196954180445131447324337 147715635333848585493253)
        ·
          refine ⟨27696681625096609779985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147715635333848585493253 27696681625096609779985)
          ·
            refine ⟨20772511218822457334989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27696681625096609779985 20772511218822457334989)
            ·
              refine ⟨7789691707058421500621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20772511218822457334989 7789691707058421500621)
              ·
                refine ⟨2921134390146908062733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7789691707058421500621 2921134390146908062733)
                ·
                  refine ⟨1095425396305090523525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2921134390146908062733 1095425396305090523525)
                  ·
                    rfl

theorem cell21_4800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 3].length) (baseStart_4800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4800 prefixEnd_4800 := by exact prefixLift 4800
  have htrace : WordTrace (prefixWord ++ tailWord_4800) baseStart_4800 baseEnd_4800 := by
    simpa [prefixWord, tailWord_4800, baseEnd_4800] using wordTrace_append hprefix tailTrace_4800
  have hstable : (prefixWord ++ tailWord_4800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800).length < 2 ^ (prefixWord ++ tailWord_4800).sum := by decide
  have hdescent : baseEnd_4800 < baseStart_4800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4831 : List Nat := [1, 1, 2, 3, 2, 5, 2, 1, 4]
def baseStart_4831 : Nat := 118140960795 + 4831 * 2 ^ 59
def prefixEnd_4831 : Nat := 4983230072969 + 3 ^ 40 * 4831 * 2
def baseEnd_4831 : Nat := 1102500018655925506795

theorem tailTrace_4831 : CollatzResearch.WordTrace tailWord_4831 prefixEnd_4831 1102500018655925506795 := by
  unfold tailWord_4831
  simp only [CollatzResearch.WordTrace]
  refine ⟨176201045505586914222347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117467363670391276148231 176201045505586914222347)
  ·
    refine ⟨264301568258380371333521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176201045505586914222347 264301568258380371333521)
    ·
      refine ⟨198226176193785278500141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264301568258380371333521 198226176193785278500141)
      ·
        refine ⟨74334816072669479437553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198226176193785278500141 74334816072669479437553)
        ·
          refine ⟨55751112054502109578165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74334816072669479437553 55751112054502109578165)
          ·
            refine ⟨5226666755109572772953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55751112054502109578165 5226666755109572772953)
            ·
              refine ⟨3920000066332179579715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5226666755109572772953 3920000066332179579715)
              ·
                refine ⟨5880000099498269369573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3920000066332179579715 5880000099498269369573)
                ·
                  refine ⟨1102500018655925506795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5880000099498269369573 1102500018655925506795)
                  ·
                    rfl

theorem cell21_4831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 4].length) (baseStart_4831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4831 prefixEnd_4831 := by exact prefixLift 4831
  have htrace : WordTrace (prefixWord ++ tailWord_4831) baseStart_4831 baseEnd_4831 := by
    simpa [prefixWord, tailWord_4831, baseEnd_4831] using wordTrace_append hprefix tailTrace_4831
  have hstable : (prefixWord ++ tailWord_4831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4831).length < 2 ^ (prefixWord ++ tailWord_4831).sum := by decide
  have hdescent : baseEnd_4831 < baseStart_4831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 7]
def baseStart_4842 : Nat := 118140960795 + 4842 * 2 ^ 59
def prefixEnd_4842 : Nat := 4983230072969 + 3 ^ 40 * 4842 * 2
def baseEnd_4842 : Nat := 1105010368522350823439

theorem tailTrace_4842 : CollatzResearch.WordTrace tailWord_4842 prefixEnd_4842 1105010368522350823439 := by
  unfold tailWord_4842
  simp only [CollatzResearch.WordTrace]
  refine ⟨44150562116433948218195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117734832310490528581853 44150562116433948218195)
  ·
    refine ⟨66225843174650922327293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44150562116433948218195 66225843174650922327293)
    ·
      refine ⟨24834691190494095872735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66225843174650922327293 24834691190494095872735)
      ·
        refine ⟨37252036785741143809103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24834691190494095872735 37252036785741143809103)
        ·
          refine ⟨55878055178611715713655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37252036785741143809103 55878055178611715713655)
          ·
            refine ⟨83817082767917573570483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55878055178611715713655 83817082767917573570483)
            ·
              refine ⟨125725624151876360355725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83817082767917573570483 125725624151876360355725)
              ·
                refine ⟨47147109056953635133397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125725624151876360355725 47147109056953635133397)
                ·
                  refine ⟨1105010368522350823439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 47147109056953635133397 1105010368522350823439)
                  ·
                    rfl

theorem cell21_4842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_4842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4842 prefixEnd_4842 := by exact prefixLift 4842
  have htrace : WordTrace (prefixWord ++ tailWord_4842) baseStart_4842 baseEnd_4842 := by
    simpa [prefixWord, tailWord_4842, baseEnd_4842] using wordTrace_append hprefix tailTrace_4842
  have hstable : (prefixWord ++ tailWord_4842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842).length < 2 ^ (prefixWord ++ tailWord_4842).sum := by decide
  have hdescent : baseEnd_4842 < baseStart_4842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873 : List Nat := [1, 2, 1, 1, 3, 2, 3, 4, 4]
def baseStart_4873 : Nat := 118140960795 + 4873 * 2 ^ 59
def prefixEnd_4873 : Nat := 4983230072969 + 3 ^ 40 * 4873 * 2
def baseEnd_4873 : Nat := 1112084990873185806709

theorem tailTrace_4873 : CollatzResearch.WordTrace tailWord_4873 prefixEnd_4873 1112084990873185806709 := by
  unfold tailWord_4873
  simp only [CollatzResearch.WordTrace]
  refine ⟨177732911353428087251273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118488607568952058167515 177732911353428087251273)
  ·
    refine ⟨133299683515071065438455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177732911353428087251273 133299683515071065438455)
    ·
      refine ⟨199949525272606598157683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133299683515071065438455 199949525272606598157683)
      ·
        refine ⟨299924287908909897236525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199949525272606598157683 299924287908909897236525)
        ·
          refine ⟨112471607965841211463697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 299924287908909897236525 112471607965841211463697)
          ·
            refine ⟨84353705974380908597773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112471607965841211463697 84353705974380908597773)
            ·
              refine ⟨31632639740392840724165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84353705974380908597773 31632639740392840724165)
              ·
                refine ⟨5931119951323657635781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31632639740392840724165 5931119951323657635781)
                ·
                  refine ⟨1112084990873185806709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5931119951323657635781 1112084990873185806709)
                  ·
                    rfl

theorem cell21_4873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_4873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_4873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_4873 prefixEnd_4873 := by exact prefixLift 4873
  have htrace : WordTrace (prefixWord ++ tailWord_4873) baseStart_4873 baseEnd_4873 := by
    simpa [prefixWord, tailWord_4873, baseEnd_4873] using wordTrace_append hprefix tailTrace_4873
  have hstable : (prefixWord ++ tailWord_4873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873).length < 2 ^ (prefixWord ++ tailWord_4873).sum := by decide
  have hdescent : baseEnd_4873 < baseStart_4873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5014 : List Nat := [5, 3, 1, 1, 1, 1, 2, 7]
def baseStart_5014 : Nat := 118140960795 + 5014 * 2 ^ 59
def prefixEnd_5014 : Nat := 4983230072969 + 3 ^ 40 * 5014 * 2
def baseEnd_5014 : Nat := 381421037296091318807

theorem tailTrace_5014 : CollatzResearch.WordTrace tailWord_5014 prefixEnd_5014 381421037296091318807 := by
  unfold tailWord_5014
  simp only [CollatzResearch.WordTrace]
  refine ⟨11429725240163073008381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121917069228406112089397 11429725240163073008381)
  ·
    refine ⟨4286146965061152378143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11429725240163073008381 4286146965061152378143)
    ·
      refine ⟨6429220447591728567215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4286146965061152378143 6429220447591728567215)
      ·
        refine ⟨9643830671387592850823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6429220447591728567215 9643830671387592850823)
        ·
          refine ⟨14465746007081389276235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9643830671387592850823 14465746007081389276235)
          ·
            refine ⟨21698619010622083914353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14465746007081389276235 21698619010622083914353)
            ·
              refine ⟨16273964257966562935765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21698619010622083914353 16273964257966562935765)
              ·
                refine ⟨381421037296091318807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16273964257966562935765 381421037296091318807)
                ·
                  rfl

theorem cell21_5014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_5014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_5014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_5014 prefixEnd_5014 := by exact prefixLift 5014
  have htrace : WordTrace (prefixWord ++ tailWord_5014) baseStart_5014 baseEnd_5014 := by
    simpa [prefixWord, tailWord_5014, baseEnd_5014] using wordTrace_append hprefix tailTrace_5014
  have hstable : (prefixWord ++ tailWord_5014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5014).length < 2 ^ (prefixWord ++ tailWord_5014).sum := by decide
  have hdescent : baseEnd_5014 < baseStart_5014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5056 : List Nat := [2, 1, 1, 2, 3, 5, 1, 6]
def baseStart_5056 : Nat := 118140960795 + 5056 * 2 ^ 59
def prefixEnd_5056 : Nat := 4983230072969 + 3 ^ 40 * 5056 * 2
def baseEnd_5056 : Nat := 384616028035178085445

theorem tailTrace_5056 : CollatzResearch.WordTrace tailWord_5056 prefixEnd_5056 384616028035178085445 := by
  unfold tailWord_5056
  simp only [CollatzResearch.WordTrace]
  refine ⟨92203734845225170581511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122938313126966894108681 92203734845225170581511)
  ·
    refine ⟨138305602267837755872267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92203734845225170581511 138305602267837755872267)
    ·
      refine ⟨207458403401756633808401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138305602267837755872267 207458403401756633808401)
      ·
        refine ⟨155593802551317475356301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207458403401756633808401 155593802551317475356301)
        ·
          refine ⟨58347675956744053258613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155593802551317475356301 58347675956744053258613)
          ·
            refine ⟨5470094620944754992995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58347675956744053258613 5470094620944754992995)
            ·
              refine ⟨8205141931417132489493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5470094620944754992995 8205141931417132489493)
              ·
                refine ⟨384616028035178085445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8205141931417132489493 384616028035178085445)
                ·
                  rfl

theorem cell21_5056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 6].length) (baseStart_5056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_5056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_5056 prefixEnd_5056 := by exact prefixLift 5056
  have htrace : WordTrace (prefixWord ++ tailWord_5056) baseStart_5056 baseEnd_5056 := by
    simpa [prefixWord, tailWord_5056, baseEnd_5056] using wordTrace_append hprefix tailTrace_5056
  have hstable : (prefixWord ++ tailWord_5056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5056).length < 2 ^ (prefixWord ++ tailWord_5056).sum := by decide
  have hdescent : baseEnd_5056 < baseStart_5056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_5070 : Nat := 118140960795 + 5070 * 2 ^ 59
def prefixEnd_5070 : Nat := 4983230072969 + 3 ^ 40 * 5070 * 2
def baseEnd_5070 : Nat := 1157043074844621022973

theorem tailTrace_5070 : CollatzResearch.WordTrace tailWord_5070 prefixEnd_5070 1157043074844621022973 := by
  unfold tailWord_5070
  simp only [CollatzResearch.WordTrace]
  refine ⟨23114761454966341521583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123278727759820488115109 23114761454966341521583)
  ·
    refine ⟨34672142182449512282375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23114761454966341521583 34672142182449512282375)
    ·
      refine ⟨52008213273674268423563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34672142182449512282375 52008213273674268423563)
      ·
        refine ⟨78012319910511402635345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52008213273674268423563 78012319910511402635345)
        ·
          refine ⟨58509239932883551976509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78012319910511402635345 58509239932883551976509)
          ·
            refine ⟨21940964974831331991191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58509239932883551976509 21940964974831331991191)
            ·
              refine ⟨32911447462246997986787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21940964974831331991191 32911447462246997986787)
              ·
                refine ⟨49367171193370496980181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32911447462246997986787 49367171193370496980181)
                ·
                  refine ⟨1157043074844621022973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 49367171193370496980181 1157043074844621022973)
                  ·
                    rfl

theorem cell21_5070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_5070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_5070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_5070 prefixEnd_5070 := by exact prefixLift 5070
  have htrace : WordTrace (prefixWord ++ tailWord_5070) baseStart_5070 baseEnd_5070 := by
    simpa [prefixWord, tailWord_5070, baseEnd_5070] using wordTrace_append hprefix tailTrace_5070
  have hstable : (prefixWord ++ tailWord_5070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070).length < 2 ^ (prefixWord ++ tailWord_5070).sum := by decide
  have hdescent : baseEnd_5070 < baseStart_5070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5132 : List Nat := [2, 2, 1, 2, 3, 2, 4, 5]
def baseStart_5132 : Nat := 118140960795 + 5132 * 2 ^ 59
def prefixEnd_5132 : Nat := 4983230072969 + 3 ^ 40 * 5132 * 2
def baseEnd_5132 : Nat := 390397439848763663171

theorem tailTrace_5132 : CollatzResearch.WordTrace tailWord_5132 prefixEnd_5132 390397439848763663171 := by
  unfold tailWord_5132
  simp only [CollatzResearch.WordTrace]
  refine ⟨93589708707557660464825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124786278276743547286433 93589708707557660464825)
  ·
    refine ⟨70192281530668245348619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93589708707557660464825 70192281530668245348619)
    ·
      refine ⟨105288422296002368022929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70192281530668245348619 105288422296002368022929)
      ·
        refine ⟨78966316722001776017197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105288422296002368022929 78966316722001776017197)
        ·
          refine ⟨29612368770750666006449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78966316722001776017197 29612368770750666006449)
          ·
            refine ⟨22209276578062999504837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29612368770750666006449 22209276578062999504837)
            ·
              refine ⟨4164239358386812407157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22209276578062999504837 4164239358386812407157)
              ·
                refine ⟨390397439848763663171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4164239358386812407157 390397439848763663171)
                ·
                  rfl

theorem cell21_5132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 5].length) (baseStart_5132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_5132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_5132 prefixEnd_5132 := by exact prefixLift 5132
  have htrace : WordTrace (prefixWord ++ tailWord_5132) baseStart_5132 baseEnd_5132 := by
    simpa [prefixWord, tailWord_5132, baseEnd_5132] using wordTrace_append hprefix tailTrace_5132
  have hstable : (prefixWord ++ tailWord_5132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5132).length < 2 ^ (prefixWord ++ tailWord_5132).sum := by decide
  have hdescent : baseEnd_5132 < baseStart_5132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5149 : List Nat := [1, 4, 2, 2, 4, 1, 7]
def baseStart_5149 : Nat := 118140960795 + 5149 * 2 ^ 59
def prefixEnd_5149 : Nat := 4983230072969 + 3 ^ 40 * 5149 * 2
def baseEnd_5149 : Nat := 130563550128671022905

theorem tailTrace_5149 : CollatzResearch.WordTrace tailWord_5149 prefixEnd_5149 130563550128671022905 := by
  unfold tailWord_5149
  simp only [CollatzResearch.WordTrace]
  refine ⟨187799458353527224298501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125199638902351482865667 187799458353527224298501)
  ·
    refine ⟨35212398441286354555969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187799458353527224298501 35212398441286354555969)
    ·
      refine ⟨26409298830964765916977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35212398441286354555969 26409298830964765916977)
      ·
        refine ⟨19806974123223574437733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26409298830964765916977 19806974123223574437733)
        ·
          refine ⟨3713807648104420207075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19806974123223574437733 3713807648104420207075)
          ·
            refine ⟨5570711472156630310613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713807648104420207075 5570711472156630310613)
            ·
              refine ⟨130563550128671022905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 5570711472156630310613 130563550128671022905)
              ·
                rfl

theorem cell21_5149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 7].length) (baseStart_5149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_5149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_5149 prefixEnd_5149 := by exact prefixLift 5149
  have htrace : WordTrace (prefixWord ++ tailWord_5149) baseStart_5149 baseEnd_5149 := by
    simpa [prefixWord, tailWord_5149, baseEnd_5149] using wordTrace_append hprefix tailTrace_5149
  have hstable : (prefixWord ++ tailWord_5149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5149).length < 2 ^ (prefixWord ++ tailWord_5149).sum := by decide
  have hdescent : baseEnd_5149 < baseStart_5149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191 : List Nat := [1, 1, 4, 1, 3, 2, 2, 7]
def baseStart_5191 : Nat := 118140960795 + 5191 * 2 ^ 59
def prefixEnd_5191 : Nat := 4983230072969 + 3 ^ 40 * 5191 * 2
def baseEnd_5191 : Nat := 394885641125099835353

theorem tailTrace_5191 : CollatzResearch.WordTrace tailWord_5191 prefixEnd_5191 394885641125099835353 := by
  unfold tailWord_5191
  simp only [CollatzResearch.WordTrace]
  refine ⟨189331324201368397327427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126220882800912264884951 189331324201368397327427)
  ·
    refine ⟨283996986302052595991141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189331324201368397327427 283996986302052595991141)
    ·
      refine ⟨53249434931634861748339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283996986302052595991141 53249434931634861748339)
      ·
        refine ⟨79874152397452292622509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53249434931634861748339 79874152397452292622509)
        ·
          refine ⟨29952807149044609733441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79874152397452292622509 29952807149044609733441)
          ·
            refine ⟨22464605361783457300081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29952807149044609733441 22464605361783457300081)
            ·
              refine ⟨16848454021337592975061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22464605361783457300081 16848454021337592975061)
              ·
                refine ⟨394885641125099835353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16848454021337592975061 394885641125099835353)
                ·
                  rfl

theorem cell21_5191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 7].length) (baseStart_5191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_5191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_5191 prefixEnd_5191 := by exact prefixLift 5191
  have htrace : WordTrace (prefixWord ++ tailWord_5191) baseStart_5191 baseEnd_5191 := by
    simpa [prefixWord, tailWord_5191, baseEnd_5191] using wordTrace_append hprefix tailTrace_5191
  have hstable : (prefixWord ++ tailWord_5191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191).length < 2 ^ (prefixWord ++ tailWord_5191).sum := by decide
  have hdescent : baseEnd_5191 < baseStart_5191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5214 : List Nat := [4, 4, 1, 1, 1, 2, 1, 4, 3]
def baseStart_5214 : Nat := 118140960795 + 5214 * 2 ^ 59
def prefixEnd_5214 : Nat := 4983230072969 + 3 ^ 40 * 5214 * 2
def baseEnd_5214 : Nat := 1189905836732370622679

theorem tailTrace_5214 : CollatzResearch.WordTrace tailWord_5214 prefixEnd_5214 1189905836732370622679 := by
  unfold tailWord_5214
  simp only [CollatzResearch.WordTrace]
  refine ⟨23771275389755415676837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126780135412028883609797 23771275389755415676837)
  ·
    refine ⟨4457114135579140439407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23771275389755415676837 4457114135579140439407)
    ·
      refine ⟨6685671203368710659111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4457114135579140439407 6685671203368710659111)
      ·
        refine ⟨10028506805053065988667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6685671203368710659111 10028506805053065988667)
        ·
          refine ⟨15042760207579598983001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10028506805053065988667 15042760207579598983001)
          ·
            refine ⟨11282070155684699237251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15042760207579598983001 11282070155684699237251)
            ·
              refine ⟨16923105233527048855877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11282070155684699237251 16923105233527048855877)
              ·
                refine ⟨3173082231286321660477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16923105233527048855877 3173082231286321660477)
                ·
                  refine ⟨1189905836732370622679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3173082231286321660477 1189905836732370622679)
                  ·
                    rfl

theorem cell21_5214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_5214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_5214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_5214 prefixEnd_5214 := by exact prefixLift 5214
  have htrace : WordTrace (prefixWord ++ tailWord_5214) baseStart_5214 baseEnd_5214 := by
    simpa [prefixWord, tailWord_5214, baseEnd_5214] using wordTrace_append hprefix tailTrace_5214
  have hstable : (prefixWord ++ tailWord_5214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5214).length < 2 ^ (prefixWord ++ tailWord_5214).sum := by decide
  have hdescent : baseEnd_5214 < baseStart_5214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287 : List Nat := [1, 1, 6, 2, 1, 2, 3, 1, 4]
def baseStart_5287 : Nat := 118140960795 + 5287 * 2 ^ 59
def prefixEnd_5287 : Nat := 4983230072969 + 3 ^ 40 * 5287 * 2
def baseEnd_5287 : Nat := 1206565431300465905863

theorem tailTrace_5287 : CollatzResearch.WordTrace tailWord_5287 prefixEnd_5287 1206565431300465905863 := by
  unfold tailWord_5287
  simp only [CollatzResearch.WordTrace]
  refine ⟨192832731853576792822115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128555154569051195214743 192832731853576792822115)
  ·
    refine ⟨289249097780365189233173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192832731853576792822115 289249097780365189233173)
    ·
      refine ⟨13558551458454618245305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 289249097780365189233173 13558551458454618245305)
      ·
        refine ⟨10168913593840963683979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13558551458454618245305 10168913593840963683979)
        ·
          refine ⟨15253370390761445525969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10168913593840963683979 15253370390761445525969)
          ·
            refine ⟨11440027793071084144477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15253370390761445525969 11440027793071084144477)
            ·
              refine ⟨4290010422401656554179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11440027793071084144477 4290010422401656554179)
              ·
                refine ⟨6435015633602484831269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4290010422401656554179 6435015633602484831269)
                ·
                  refine ⟨1206565431300465905863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6435015633602484831269 1206565431300465905863)
                  ·
                    rfl

theorem cell21_5287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 4].length) (baseStart_5287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_5287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_5287 prefixEnd_5287 := by exact prefixLift 5287
  have htrace : WordTrace (prefixWord ++ tailWord_5287) baseStart_5287 baseEnd_5287 := by
    simpa [prefixWord, tailWord_5287, baseEnd_5287] using wordTrace_append hprefix tailTrace_5287
  have hstable : (prefixWord ++ tailWord_5287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287).length < 2 ^ (prefixWord ++ tailWord_5287).sum := by decide
  have hdescent : baseEnd_5287 < baseStart_5287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5298 : List Nat := [3, 2, 1, 1, 1, 4, 2, 2, 5]
def baseStart_5298 : Nat := 118140960795 + 5298 * 2 ^ 59
def prefixEnd_5298 : Nat := 4983230072969 + 3 ^ 40 * 5298 * 2
def baseEnd_5298 : Nat := 1209075781166891222507

theorem tailTrace_5298 : CollatzResearch.WordTrace tailWord_5298 prefixEnd_5298 1209075781166891222507 := by
  unfold tailWord_5298
  simp only [CollatzResearch.WordTrace]
  refine ⟨48308483703431417868137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128822623209150447648365 48308483703431417868137)
  ·
    refine ⟨36231362777573563401103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48308483703431417868137 36231362777573563401103)
    ·
      refine ⟨54347044166360345101655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36231362777573563401103 54347044166360345101655)
      ·
        refine ⟨81520566249540517652483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54347044166360345101655 81520566249540517652483)
        ·
          refine ⟨122280849374310776478725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81520566249540517652483 122280849374310776478725)
          ·
            refine ⟨22927659257683270589761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122280849374310776478725 22927659257683270589761)
            ·
              refine ⟨17195744443262452942321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22927659257683270589761 17195744443262452942321)
              ·
                refine ⟨12896808332446839706741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17195744443262452942321 12896808332446839706741)
                ·
                  refine ⟨1209075781166891222507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12896808332446839706741 1209075781166891222507)
                  ·
                    rfl

theorem cell21_5298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_5298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_5298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_5298 prefixEnd_5298 := by exact prefixLift 5298
  have htrace : WordTrace (prefixWord ++ tailWord_5298) baseStart_5298 baseEnd_5298 := by
    simpa [prefixWord, tailWord_5298, baseEnd_5298] using wordTrace_append hprefix tailTrace_5298
  have hstable : (prefixWord ++ tailWord_5298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5298).length < 2 ^ (prefixWord ++ tailWord_5298).sum := by decide
  have hdescent : baseEnd_5298 < baseStart_5298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394 : List Nat := [3, 2, 4, 2, 1, 2, 1, 6]
def baseStart_5394 : Nat := 118140960795 + 5394 * 2 ^ 59
def prefixEnd_5394 : Nat := 4983230072969 + 3 ^ 40 * 5394 * 2
def baseEnd_5394 : Nat := 410328096364019207437

theorem tailTrace_5394 : CollatzResearch.WordTrace tailWord_5394 prefixEnd_5394 410328096364019207437 := by
  unfold tailWord_5394
  simp only [CollatzResearch.WordTrace]
  refine ⟨49183835616483516741809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131156894977289377978157 49183835616483516741809)
  ·
    refine ⟨36887876712362637556357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49183835616483516741809 36887876712362637556357)
    ·
      refine ⟨6916476883567994541817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36887876712362637556357 6916476883567994541817)
      ·
        refine ⟨5187357662675995906363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6916476883567994541817 5187357662675995906363)
        ·
          refine ⟨7781036494013993859545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5187357662675995906363 7781036494013993859545)
          ·
            refine ⟨5835777370510495394659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7781036494013993859545 5835777370510495394659)
            ·
              refine ⟨8753666055765743091989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5835777370510495394659 8753666055765743091989)
              ·
                refine ⟨410328096364019207437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8753666055765743091989 410328096364019207437)
                ·
                  rfl

theorem cell21_5394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_5394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_5394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_5394 prefixEnd_5394 := by exact prefixLift 5394
  have htrace : WordTrace (prefixWord ++ tailWord_5394) baseStart_5394 baseEnd_5394 := by
    simpa [prefixWord, tailWord_5394, baseEnd_5394] using wordTrace_append hprefix tailTrace_5394
  have hstable : (prefixWord ++ tailWord_5394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394).length < 2 ^ (prefixWord ++ tailWord_5394).sum := by decide
  have hdescent : baseEnd_5394 < baseStart_5394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484 : List Nat := [2, 2, 1, 1, 5, 3, 1, 3, 3]
def baseStart_5484 : Nat := 118140960795 + 5484 * 2 ^ 59
def prefixEnd_5484 : Nat := 4983230072969 + 3 ^ 40 * 5484 * 2
def baseEnd_5484 : Nat := 1251523515271901122127

theorem tailTrace_5484 : CollatzResearch.WordTrace tailWord_5484 prefixEnd_5484 1251523515271901122127 := by
  unfold tailWord_5484
  simp only [CollatzResearch.WordTrace]
  refine ⟨100008956069939718871753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133345274759919625162337 100008956069939718871753)
  ·
    refine ⟨75006717052454789153815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100008956069939718871753 75006717052454789153815)
    ·
      refine ⟨112510075578682183730723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75006717052454789153815 112510075578682183730723)
      ·
        refine ⟨168765113368023275596085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112510075578682183730723 168765113368023275596085)
        ·
          refine ⟨15821729378252182087133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168765113368023275596085 15821729378252182087133)
          ·
            refine ⟨5933148516844568282675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15821729378252182087133 5933148516844568282675)
            ·
              refine ⟨8899722775266852424013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5933148516844568282675 8899722775266852424013)
              ·
                refine ⟨3337396040725069659005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8899722775266852424013 3337396040725069659005)
                ·
                  refine ⟨1251523515271901122127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3337396040725069659005 1251523515271901122127)
                  ·
                    rfl

theorem cell21_5484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_5484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_5484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_5484 prefixEnd_5484 := by exact prefixLift 5484
  have htrace : WordTrace (prefixWord ++ tailWord_5484) baseStart_5484 baseEnd_5484 := by
    simpa [prefixWord, tailWord_5484, baseEnd_5484] using wordTrace_append hprefix tailTrace_5484
  have hstable : (prefixWord ++ tailWord_5484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484).length < 2 ^ (prefixWord ++ tailWord_5484).sum := by decide
  have hdescent : baseEnd_5484 < baseStart_5484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543 : List Nat := [1, 1, 6, 1, 1, 1, 2, 5, 3]
def baseStart_5543 : Nat := 118140960795 + 5543 * 2 ^ 59
def prefixEnd_5543 : Nat := 4983230072969 + 3 ^ 40 * 5543 * 2
def baseEnd_5543 : Nat := 1264988119100909638673

theorem tailTrace_5543 : CollatzResearch.WordTrace tailWord_5543 prefixEnd_5543 1264988119100909638673 := by
  unfold tailWord_5543
  simp only [CollatzResearch.WordTrace]
  refine ⟨202169818926132514141283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134779879284088342760855 202169818926132514141283)
  ·
    refine ⟨303254728389198771211925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202169818926132514141283 303254728389198771211925)
    ·
      refine ⟨14215065393243692400559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 303254728389198771211925 14215065393243692400559)
      ·
        refine ⟨21322598089865538600839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14215065393243692400559 21322598089865538600839)
        ·
          refine ⟨31983897134798307901259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21322598089865538600839 31983897134798307901259)
          ·
            refine ⟨47975845702197461851889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31983897134798307901259 47975845702197461851889)
            ·
              refine ⟨35981884276648096388917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47975845702197461851889 35981884276648096388917)
              ·
                refine ⟨3373301650935759036461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35981884276648096388917 3373301650935759036461)
                ·
                  refine ⟨1264988119100909638673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3373301650935759036461 1264988119100909638673)
                  ·
                    rfl

theorem cell21_5543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 3].length) (baseStart_5543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_5543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_5543 prefixEnd_5543 := by exact prefixLift 5543
  have htrace : WordTrace (prefixWord ++ tailWord_5543) baseStart_5543 baseEnd_5543 := by
    simpa [prefixWord, tailWord_5543, baseEnd_5543] using wordTrace_append hprefix tailTrace_5543
  have hstable : (prefixWord ++ tailWord_5543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543).length < 2 ^ (prefixWord ++ tailWord_5543).sum := by decide
  have hdescent : baseEnd_5543 < baseStart_5543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557 : List Nat := [1, 3, 3, 2, 2, 1, 1, 4, 4]
def baseStart_5557 : Nat := 118140960795 + 5557 * 2 ^ 59
def prefixEnd_5557 : Nat := 4983230072969 + 3 ^ 40 * 5557 * 2
def baseEnd_5557 : Nat := 1268183109839996405311

theorem tailTrace_5557 : CollatzResearch.WordTrace tailWord_5557 prefixEnd_5557 1268183109839996405311 := by
  unfold tailWord_5557
  simp only [CollatzResearch.WordTrace]
  refine ⟨202680440875412905150925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135120293916941936767283 202680440875412905150925)
  ·
    refine ⟨76005165328279839431597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202680440875412905150925 76005165328279839431597)
    ·
      refine ⟨28501936998104939786849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76005165328279839431597 28501936998104939786849)
      ·
        refine ⟨21376452748578704840137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28501936998104939786849 21376452748578704840137)
        ·
          refine ⟨16032339561434028630103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21376452748578704840137 16032339561434028630103)
          ·
            refine ⟨24048509342151042945155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16032339561434028630103 24048509342151042945155)
            ·
              refine ⟨36072764013226564417733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24048509342151042945155 36072764013226564417733)
              ·
                refine ⟨6763643252479980828325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36072764013226564417733 6763643252479980828325)
                ·
                  refine ⟨1268183109839996405311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6763643252479980828325 1268183109839996405311)
                  ·
                    rfl

theorem cell21_5557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_5557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_5557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_5557 prefixEnd_5557 := by exact prefixLift 5557
  have htrace : WordTrace (prefixWord ++ tailWord_5557) baseStart_5557 baseEnd_5557 := by
    simpa [prefixWord, tailWord_5557, baseEnd_5557] using wordTrace_append hprefix tailTrace_5557
  have hstable : (prefixWord ++ tailWord_5557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557).length < 2 ^ (prefixWord ++ tailWord_5557).sum := by decide
  have hdescent : baseEnd_5557 < baseStart_5557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 6]
def baseStart_5616 : Nat := 118140960795 + 5616 * 2 ^ 59
def prefixEnd_5616 : Nat := 4983230072969 + 3 ^ 40 * 5616 * 2
def baseEnd_5616 : Nat := 1281647713669004921857

theorem tailTrace_5616 : CollatzResearch.WordTrace tailWord_5616 prefixEnd_5616 1281647713669004921857 := by
  unfold tailWord_5616
  simp only [CollatzResearch.WordTrace]
  refine ⟨102416173830832990774351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136554898441110654365801 102416173830832990774351)
  ·
    refine ⟨153624260746249486161527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102416173830832990774351 153624260746249486161527)
    ·
      refine ⟨230436391119374229242291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153624260746249486161527 230436391119374229242291)
      ·
        refine ⟨345654586679061343863437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230436391119374229242291 345654586679061343863437)
        ·
          refine ⟨129620470004648003948789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 345654586679061343863437 129620470004648003948789)
          ·
            refine ⟨12151919062935750370199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129620470004648003948789 12151919062935750370199)
            ·
              refine ⟨18227878594403625555299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12151919062935750370199 18227878594403625555299)
              ·
                refine ⟨27341817891605438332949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18227878594403625555299 27341817891605438332949)
                ·
                  refine ⟨1281647713669004921857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27341817891605438332949 1281647713669004921857)
                  ·
                    rfl

theorem cell21_5616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_5616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_5616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_5616 prefixEnd_5616 := by exact prefixLift 5616
  have htrace : WordTrace (prefixWord ++ tailWord_5616) baseStart_5616 baseEnd_5616 := by
    simpa [prefixWord, tailWord_5616, baseEnd_5616] using wordTrace_append hprefix tailTrace_5616
  have hstable : (prefixWord ++ tailWord_5616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616).length < 2 ^ (prefixWord ++ tailWord_5616).sum := by decide
  have hdescent : baseEnd_5616 < baseStart_5616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5706 : List Nat := [3, 1, 2, 1, 1, 3, 1, 9]
def baseStart_5706 : Nat := 118140960795 + 5706 * 2 ^ 59
def prefixEnd_5706 : Nat := 4983230072969 + 3 ^ 40 * 5706 * 2
def baseEnd_5706 : Nat := 434062313282949473891

theorem tailTrace_5706 : CollatzResearch.WordTrace tailWord_5706 prefixEnd_5706 434062313282949473891 := by
  unfold tailWord_5706
  simp only [CollatzResearch.WordTrace]
  refine ⟨52028729333902838081243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138743278223740901549981 52028729333902838081243)
  ·
    refine ⟨78043094000854257121865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52028729333902838081243 78043094000854257121865)
    ·
      refine ⟨58532320500640692841399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78043094000854257121865 58532320500640692841399)
      ·
        refine ⟨87798480750961039262099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58532320500640692841399 87798480750961039262099)
        ·
          refine ⟨131697721126441558893149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87798480750961039262099 131697721126441558893149)
          ·
            refine ⟨49386645422415584584931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131697721126441558893149 49386645422415584584931)
            ·
              refine ⟨74079968133623376877397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49386645422415584584931 74079968133623376877397)
              ·
                refine ⟨434062313282949473891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 74079968133623376877397 434062313282949473891)
                ·
                  rfl

theorem cell21_5706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_5706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_5706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_5706 prefixEnd_5706 := by exact prefixLift 5706
  have htrace : WordTrace (prefixWord ++ tailWord_5706) baseStart_5706 baseEnd_5706 := by
    simpa [prefixWord, tailWord_5706, baseEnd_5706] using wordTrace_append hprefix tailTrace_5706
  have hstable : (prefixWord ++ tailWord_5706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5706).length < 2 ^ (prefixWord ++ tailWord_5706).sum := by decide
  have hdescent : baseEnd_5706 < baseStart_5706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 8]
def baseStart_5751 : Nat := 118140960795 + 5751 * 2 ^ 59
def prefixEnd_5751 : Nat := 4983230072969 + 3 ^ 40 * 5751 * 2
def baseEnd_5751 : Nat := 1312456552938770171581

theorem tailTrace_5751 : CollatzResearch.WordTrace tailWord_5751 prefixEnd_5751 1312456552938770171581 := by
  unfold tailWord_5751
  simp only [CollatzResearch.WordTrace]
  refine ⟨209756202172584037713107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139837468115056025142071 209756202172584037713107)
  ·
    refine ⟨314634303258876056569661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209756202172584037713107 314634303258876056569661)
    ·
      refine ⟨117987863722078521213623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314634303258876056569661 117987863722078521213623)
      ·
        refine ⟨176981795583117781820435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117987863722078521213623 176981795583117781820435)
        ·
          refine ⟨265472693374676672730653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176981795583117781820435 265472693374676672730653)
          ·
            refine ⟨99552260015503752273995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265472693374676672730653 99552260015503752273995)
            ·
              refine ⟨149328390023255628410993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99552260015503752273995 149328390023255628410993)
              ·
                refine ⟨111996292517441721308245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149328390023255628410993 111996292517441721308245)
                ·
                  refine ⟨1312456552938770171581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 111996292517441721308245 1312456552938770171581)
                  ·
                    rfl

theorem cell21_5751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 8].length) (baseStart_5751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_5751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_5751 prefixEnd_5751 := by exact prefixLift 5751
  have htrace : WordTrace (prefixWord ++ tailWord_5751) baseStart_5751 baseEnd_5751 := by
    simpa [prefixWord, tailWord_5751, baseEnd_5751] using wordTrace_append hprefix tailTrace_5751
  have hstable : (prefixWord ++ tailWord_5751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751).length < 2 ^ (prefixWord ++ tailWord_5751).sum := by decide
  have hdescent : baseEnd_5751 < baseStart_5751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5847 : List Nat := [1, 1, 3, 2, 1, 3, 5, 2, 3]
def baseStart_5847 : Nat := 118140960795 + 5847 * 2 ^ 59
def prefixEnd_5847 : Nat := 4983230072969 + 3 ^ 40 * 5847 * 2
def baseEnd_5847 : Nat := 1334365060863936571385

theorem tailTrace_5847 : CollatzResearch.WordTrace tailWord_5847 prefixEnd_5847 1334365060863936571385 := by
  unfold tailWord_5847
  simp only [CollatzResearch.WordTrace]
  refine ⟨213257609824792433207795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142171739883194955471863 213257609824792433207795)
  ·
    refine ⟨319886414737188649811693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213257609824792433207795 319886414737188649811693)
    ·
      refine ⟨119957405526445743679385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319886414737188649811693 119957405526445743679385)
      ·
        refine ⟨89968054144834307759539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119957405526445743679385 89968054144834307759539)
        ·
          refine ⟨134952081217251461639309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89968054144834307759539 134952081217251461639309)
          ·
            refine ⟨50607030456469298114741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134952081217251461639309 50607030456469298114741)
            ·
              refine ⟨4744409105293996698257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50607030456469298114741 4744409105293996698257)
              ·
                refine ⟨3558306828970497523693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4744409105293996698257 3558306828970497523693)
                ·
                  refine ⟨1334365060863936571385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3558306828970497523693 1334365060863936571385)
                  ·
                    rfl

theorem cell21_5847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 3].length) (baseStart_5847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_5847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_5847 prefixEnd_5847 := by exact prefixLift 5847
  have htrace : WordTrace (prefixWord ++ tailWord_5847) baseStart_5847 baseEnd_5847 := by
    simpa [prefixWord, tailWord_5847, baseEnd_5847] using wordTrace_append hprefix tailTrace_5847
  have hstable : (prefixWord ++ tailWord_5847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5847).length < 2 ^ (prefixWord ++ tailWord_5847).sum := by decide
  have hdescent : baseEnd_5847 < baseStart_5847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920 : List Nat := [2, 1, 1, 5, 1, 1, 1, 5, 4]
def baseStart_5920 : Nat := 118140960795 + 5920 * 2 ^ 59
def prefixEnd_5920 : Nat := 4983230072969 + 3 ^ 40 * 5920 * 2
def baseEnd_5920 : Nat := 1351024655432031854569

theorem tailTrace_5920 : CollatzResearch.WordTrace tailWord_5920 prefixEnd_5920 1351024655432031854569 := by
  unfold tailWord_5920
  simp only [CollatzResearch.WordTrace]
  refine ⟨107960069280162950307607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143946759040217267076809 107960069280162950307607)
  ·
    refine ⟨161940103920244425461411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107960069280162950307607 161940103920244425461411)
    ·
      refine ⟨242910155880366638192117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161940103920244425461411 242910155880366638192117)
      ·
        refine ⟨22772827113784372330511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242910155880366638192117 22772827113784372330511)
        ·
          refine ⟨34159240670676558495767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22772827113784372330511 34159240670676558495767)
          ·
            refine ⟨51238861006014837743651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34159240670676558495767 51238861006014837743651)
            ·
              refine ⟨76858291509022256615477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51238861006014837743651 76858291509022256615477)
              ·
                refine ⟨7205464828970836557701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76858291509022256615477 7205464828970836557701)
                ·
                  refine ⟨1351024655432031854569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7205464828970836557701 1351024655432031854569)
                  ·
                    rfl

theorem cell21_5920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_5920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_5920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_5920 prefixEnd_5920 := by exact prefixLift 5920
  have htrace : WordTrace (prefixWord ++ tailWord_5920) baseStart_5920 baseEnd_5920 := by
    simpa [prefixWord, tailWord_5920, baseEnd_5920] using wordTrace_append hprefix tailTrace_5920
  have hstable : (prefixWord ++ tailWord_5920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920).length < 2 ^ (prefixWord ++ tailWord_5920).sum := by decide
  have hdescent : baseEnd_5920 < baseStart_5920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5940 : List Nat := [2, 5, 1, 1, 2, 2, 2, 3, 3]
def baseStart_5940 : Nat := 118140960795 + 5940 * 2 ^ 59
def prefixEnd_5940 : Nat := 4983230072969 + 3 ^ 40 * 5940 * 2
def baseEnd_5940 : Nat := 1355588927916441521195

theorem tailTrace_5940 : CollatzResearch.WordTrace tailWord_5940 prefixEnd_5940 1355588927916441521195 := by
  unfold tailWord_5940
  simp only [CollatzResearch.WordTrace]
  refine ⟨108324799243934658171637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144433065658579544228849 108324799243934658171637)
  ·
    refine ⟨10155449929118874203591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108324799243934658171637 10155449929118874203591)
    ·
      refine ⟨15233174893678311305387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10155449929118874203591 15233174893678311305387)
      ·
        refine ⟨22849762340517466958081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15233174893678311305387 22849762340517466958081)
        ·
          refine ⟨17137321755388100218561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22849762340517466958081 17137321755388100218561)
          ·
            refine ⟨12852991316541075163921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17137321755388100218561 12852991316541075163921)
            ·
              refine ⟨9639743487405806372941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12852991316541075163921 9639743487405806372941)
              ·
                refine ⟨3614903807777177389853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9639743487405806372941 3614903807777177389853)
                ·
                  refine ⟨1355588927916441521195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3614903807777177389853 1355588927916441521195)
                  ·
                    rfl

theorem cell21_5940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_5940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_5940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_5940 prefixEnd_5940 := by exact prefixLift 5940
  have htrace : WordTrace (prefixWord ++ tailWord_5940) baseStart_5940 baseEnd_5940 := by
    simpa [prefixWord, tailWord_5940, baseEnd_5940] using wordTrace_append hprefix tailTrace_5940
  have hstable : (prefixWord ++ tailWord_5940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5940).length < 2 ^ (prefixWord ++ tailWord_5940).sum := by decide
  have hdescent : baseEnd_5940 < baseStart_5940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6030 : List Nat := [4, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_6030 : Nat := 118140960795 + 6030 * 2 ^ 59
def prefixEnd_6030 : Nat := 4983230072969 + 3 ^ 40 * 6030 * 2
def baseEnd_6030 : Nat := 1376128154096285021011

theorem tailTrace_6030 : CollatzResearch.WordTrace tailWord_6030 prefixEnd_6030 1376128154096285021011 := by
  unfold tailWord_6030
  simp only [CollatzResearch.WordTrace]
  refine ⟨27491521020226835889943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146621445441209791413029 27491521020226835889943)
  ·
    refine ⟨41237281530340253834915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27491521020226835889943 41237281530340253834915)
    ·
      refine ⟨61855922295510380752373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41237281530340253834915 61855922295510380752373)
      ·
        refine ⟨5798992715204098195535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61855922295510380752373 5798992715204098195535)
        ·
          refine ⟨8698489072806147293303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5798992715204098195535 8698489072806147293303)
          ·
            refine ⟨13047733609209220939955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8698489072806147293303 13047733609209220939955)
            ·
              refine ⟨19571600413813831409933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13047733609209220939955 19571600413813831409933)
              ·
                refine ⟨7339350155180186778725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19571600413813831409933 7339350155180186778725)
                ·
                  refine ⟨1376128154096285021011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7339350155180186778725 1376128154096285021011)
                  ·
                    rfl

theorem cell21_6030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_6030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6030 prefixEnd_6030 := by exact prefixLift 6030
  have htrace : WordTrace (prefixWord ++ tailWord_6030) baseStart_6030 baseEnd_6030 := by
    simpa [prefixWord, tailWord_6030, baseEnd_6030] using wordTrace_append hprefix tailTrace_6030
  have hstable : (prefixWord ++ tailWord_6030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6030).length < 2 ^ (prefixWord ++ tailWord_6030).sum := by decide
  have hdescent : baseEnd_6030 < baseStart_6030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072 : List Nat := [2, 1, 2, 1, 2, 3, 4, 2, 4]
def baseStart_6072 : Nat := 118140960795 + 6072 * 2 ^ 59
def prefixEnd_6072 : Nat := 4983230072969 + 3 ^ 40 * 6072 * 2
def baseEnd_6072 : Nat := 1385713126313545320925

theorem tailTrace_6072 : CollatzResearch.WordTrace tailWord_6072 prefixEnd_6072 1385713126313545320925 := by
  unfold tailWord_6072
  simp only [CollatzResearch.WordTrace]
  refine ⟨110732017004827930074235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147642689339770573432313 110732017004827930074235)
  ·
    refine ⟨166098025507241895111353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110732017004827930074235 166098025507241895111353)
    ·
      refine ⟨124573519130431421333515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166098025507241895111353 124573519130431421333515)
      ·
        refine ⟨186860278695647132000273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124573519130431421333515 186860278695647132000273)
        ·
          refine ⟨140145209021735349000205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186860278695647132000273 140145209021735349000205)
          ·
            refine ⟨52554453383150755875077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140145209021735349000205 52554453383150755875077)
            ·
              refine ⟨9853960009340766726577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52554453383150755875077 9853960009340766726577)
              ·
                refine ⟨7390470007005575044933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9853960009340766726577 7390470007005575044933)
                ·
                  refine ⟨1385713126313545320925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7390470007005575044933 1385713126313545320925)
                  ·
                    rfl

theorem cell21_6072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_6072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6072 prefixEnd_6072 := by exact prefixLift 6072
  have htrace : WordTrace (prefixWord ++ tailWord_6072) baseStart_6072 baseEnd_6072 := by
    simpa [prefixWord, tailWord_6072, baseEnd_6072] using wordTrace_append hprefix tailTrace_6072
  have hstable : (prefixWord ++ tailWord_6072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072).length < 2 ^ (prefixWord ++ tailWord_6072).sum := by decide
  have hdescent : baseEnd_6072 < baseStart_6072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193 : List Nat := [1, 2, 2, 3, 1, 3, 3, 1, 5]
def baseStart_6193 : Nat := 118140960795 + 6193 * 2 ^ 59
def prefixEnd_6193 : Nat := 4983230072969 + 3 ^ 40 * 6193 * 2
def baseEnd_6193 : Nat := 1413326974844223804011

theorem tailTrace_6193 : CollatzResearch.WordTrace tailWord_6193 prefixEnd_6193 1413326974844223804011 := by
  unfold tailWord_6193
  simp only [CollatzResearch.WordTrace]
  refine ⟨225877266571293525303233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150584844380862350202155 225877266571293525303233)
  ·
    refine ⟨169407949928470143977425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225877266571293525303233 169407949928470143977425)
    ·
      refine ⟨127055962446352607983069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169407949928470143977425 127055962446352607983069)
      ·
        refine ⟨47645985917382227993651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127055962446352607983069 47645985917382227993651)
        ·
          refine ⟨71468978876073341990477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47645985917382227993651 71468978876073341990477)
          ·
            refine ⟨26800867078527503246429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71468978876073341990477 26800867078527503246429)
            ·
              refine ⟨10050325154447813717411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26800867078527503246429 10050325154447813717411)
              ·
                refine ⟨15075487731671720576117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10050325154447813717411 15075487731671720576117)
                ·
                  refine ⟨1413326974844223804011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15075487731671720576117 1413326974844223804011)
                  ·
                    rfl

theorem cell21_6193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_6193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6193 prefixEnd_6193 := by exact prefixLift 6193
  have htrace : WordTrace (prefixWord ++ tailWord_6193) baseStart_6193 baseEnd_6193 := by
    simpa [prefixWord, tailWord_6193, baseEnd_6193] using wordTrace_append hprefix tailTrace_6193
  have hstable : (prefixWord ++ tailWord_6193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193).length < 2 ^ (prefixWord ++ tailWord_6193).sum := by decide
  have hdescent : baseEnd_6193 < baseStart_6193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196 : List Nat := [2, 5, 1, 2, 2, 1, 2, 6]
def baseStart_6196 : Nat := 118140960795 + 6196 * 2 ^ 59
def prefixEnd_6196 : Nat := 4983230072969 + 3 ^ 40 * 6196 * 2
def baseEnd_6196 : Nat := 471337205238961751335

theorem tailTrace_6196 : CollatzResearch.WordTrace tailWord_6196 prefixEnd_6196 471337205238961751335 := by
  unfold tailWord_6196
  simp only [CollatzResearch.WordTrace]
  refine ⟨112993342780212518831221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150657790373616691774961 112993342780212518831221)
  ·
    refine ⟨10593125885644923640427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112993342780212518831221 10593125885644923640427)
    ·
      refine ⟨15889688828467385460641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10593125885644923640427 15889688828467385460641)
      ·
        refine ⟨11917266621350539095481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15889688828467385460641 11917266621350539095481)
        ·
          refine ⟨8937949966012904321611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11917266621350539095481 8937949966012904321611)
          ·
            refine ⟨13406924949019356482417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8937949966012904321611 13406924949019356482417)
            ·
              refine ⟨10055193711764517361813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13406924949019356482417 10055193711764517361813)
              ·
                refine ⟨471337205238961751335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10055193711764517361813 471337205238961751335)
                ·
                  rfl

theorem cell21_6196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 6].length) (baseStart_6196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6196 prefixEnd_6196 := by exact prefixLift 6196
  have htrace : WordTrace (prefixWord ++ tailWord_6196) baseStart_6196 baseEnd_6196 := by
    simpa [prefixWord, tailWord_6196, baseEnd_6196] using wordTrace_append hprefix tailTrace_6196
  have hstable : (prefixWord ++ tailWord_6196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196).length < 2 ^ (prefixWord ++ tailWord_6196).sum := by decide
  have hdescent : baseEnd_6196 < baseStart_6196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269 : List Nat := [1, 4, 1, 1, 3, 3, 1, 2, 5]
def baseStart_6269 : Nat := 118140960795 + 6269 * 2 ^ 59
def prefixEnd_6269 : Nat := 4983230072969 + 3 ^ 40 * 6269 * 2
def baseEnd_6269 : Nat := 1430671210284980537189

theorem tailTrace_6269 : CollatzResearch.WordTrace tailWord_6269 prefixEnd_6269 1430671210284980537189 := by
  unfold tailWord_6269
  simp only [CollatzResearch.WordTrace]
  refine ⟨228649214295958505069861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152432809530639003379907 228649214295958505069861)
  ·
    refine ⟨42871727680492219700599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228649214295958505069861 42871727680492219700599)
    ·
      refine ⟨64307591520738329550899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42871727680492219700599 64307591520738329550899)
      ·
        refine ⟨96461387281107494326349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64307591520738329550899 96461387281107494326349)
        ·
          refine ⟨36173020230415310372381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96461387281107494326349 36173020230415310372381)
          ·
            refine ⟨13564882586405741389643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36173020230415310372381 13564882586405741389643)
            ·
              refine ⟨20347323879608612084465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13564882586405741389643 20347323879608612084465)
              ·
                refine ⟨15260492909706459063349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20347323879608612084465 15260492909706459063349)
                ·
                  refine ⟨1430671210284980537189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15260492909706459063349 1430671210284980537189)
                  ·
                    rfl

theorem cell21_6269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_6269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6269 prefixEnd_6269 := by exact prefixLift 6269
  have htrace : WordTrace (prefixWord ++ tailWord_6269) baseStart_6269 baseEnd_6269 := by
    simpa [prefixWord, tailWord_6269, baseEnd_6269] using wordTrace_append hprefix tailTrace_6269
  have hstable : (prefixWord ++ tailWord_6269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269).length < 2 ^ (prefixWord ++ tailWord_6269).sum := by decide
  have hdescent : baseEnd_6269 < baseStart_6269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6328 : List Nat := [2, 1, 2, 1, 2, 1, 3, 4, 5]
def baseStart_6328 : Nat := 118140960795 + 6328 * 2 ^ 59
def prefixEnd_6328 : Nat := 4983230072969 + 3 ^ 40 * 6328 * 2
def baseEnd_6328 : Nat := 1444135814113989053735

theorem tailTrace_6328 : CollatzResearch.WordTrace tailWord_6328 prefixEnd_6328 1444135814113989053735 := by
  unfold tailWord_6328
  simp only [CollatzResearch.WordTrace]
  refine ⟨115400560541105790733819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153867414054807720978425 115400560541105790733819)
  ·
    refine ⟨173100840811658686100729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115400560541105790733819 173100840811658686100729)
    ·
      refine ⟨129825630608744014575547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173100840811658686100729 129825630608744014575547)
      ·
        refine ⟨194738445913116021863321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129825630608744014575547 194738445913116021863321)
        ·
          refine ⟨146053834434837016397491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194738445913116021863321 146053834434837016397491)
          ·
            refine ⟨219080751652255524596237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146053834434837016397491 219080751652255524596237)
            ·
              refine ⟨82155281869595821723589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219080751652255524596237 82155281869595821723589)
              ·
                refine ⟨15404115350549216573173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82155281869595821723589 15404115350549216573173)
                ·
                  refine ⟨1444135814113989053735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15404115350549216573173 1444135814113989053735)
                  ·
                    rfl

theorem cell21_6328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_6328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6328 prefixEnd_6328 := by exact prefixLift 6328
  have htrace : WordTrace (prefixWord ++ tailWord_6328) baseStart_6328 baseEnd_6328 := by
    simpa [prefixWord, tailWord_6328, baseEnd_6328] using wordTrace_append hprefix tailTrace_6328
  have hstable : (prefixWord ++ tailWord_6328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6328).length < 2 ^ (prefixWord ++ tailWord_6328).sum := by decide
  have hdescent : baseEnd_6328 < baseStart_6328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6337 : List Nat := [1, 2, 6, 1, 3, 1, 1, 3, 3]
def baseStart_6337 : Nat := 118140960795 + 6337 * 2 ^ 59
def prefixEnd_6337 : Nat := 4983230072969 + 3 ^ 40 * 6337 * 2
def baseEnd_6337 : Nat := 1446189736731973403717

theorem tailTrace_6337 : CollatzResearch.WordTrace tailWord_6337 prefixEnd_6337 1446189736731973403717 := by
  unfold tailWord_6337
  simp only [CollatzResearch.WordTrace]
  refine ⟨231129378049606118545265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154086252033070745696843 231129378049606118545265)
  ·
    refine ⟨173347033537204588908949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231129378049606118545265 173347033537204588908949)
    ·
      refine ⟨8125642197056465105107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 173347033537204588908949 8125642197056465105107)
      ·
        refine ⟨12188463295584697657661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8125642197056465105107 12188463295584697657661)
        ·
          refine ⟨4570673735844261621623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12188463295584697657661 4570673735844261621623)
          ·
            refine ⟨6856010603766392432435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4570673735844261621623 6856010603766392432435)
            ·
              refine ⟨10284015905649588648653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6856010603766392432435 10284015905649588648653)
              ·
                refine ⟨3856505964618595743245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10284015905649588648653 3856505964618595743245)
                ·
                  refine ⟨1446189736731973403717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3856505964618595743245 1446189736731973403717)
                  ·
                    rfl

theorem cell21_6337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 3].length) (baseStart_6337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6337 prefixEnd_6337 := by exact prefixLift 6337
  have htrace : WordTrace (prefixWord ++ tailWord_6337) baseStart_6337 baseEnd_6337 := by
    simpa [prefixWord, tailWord_6337, baseEnd_6337] using wordTrace_append hprefix tailTrace_6337
  have hstable : (prefixWord ++ tailWord_6337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6337).length < 2 ^ (prefixWord ++ tailWord_6337).sum := by decide
  have hdescent : baseEnd_6337 < baseStart_6337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345 : List Nat := [1, 2, 1, 1, 2, 1, 1, 9, 3]
def baseStart_6345 : Nat := 118140960795 + 6345 * 2 ^ 59
def prefixEnd_6345 : Nat := 4983230072969 + 3 ^ 40 * 6345 * 2
def baseEnd_6345 : Nat := 1448015445725737270367

theorem tailTrace_6345 : CollatzResearch.WordTrace tailWord_6345 prefixEnd_6345 1448015445725737270367 := by
  unfold tailWord_6345
  simp only [CollatzResearch.WordTrace]
  refine ⟨231421162020623484836489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154280774680415656557659 231421162020623484836489)
  ·
    refine ⟨173565871515467613627367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231421162020623484836489 173565871515467613627367)
    ·
      refine ⟨260348807273201420441051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173565871515467613627367 260348807273201420441051)
      ·
        refine ⟨390523210909802130661577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260348807273201420441051 390523210909802130661577)
        ·
          refine ⟨292892408182351597996183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390523210909802130661577 292892408182351597996183)
          ·
            refine ⟨439338612273527396994275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292892408182351597996183 439338612273527396994275)
            ·
              refine ⟨659007918410291095491413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439338612273527396994275 659007918410291095491413)
              ·
                refine ⟨3861374521935299387645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 659007918410291095491413 3861374521935299387645)
                ·
                  refine ⟨1448015445725737270367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3861374521935299387645 1448015445725737270367)
                  ·
                    rfl

theorem cell21_6345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 3].length) (baseStart_6345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6345 prefixEnd_6345 := by exact prefixLift 6345
  have htrace : WordTrace (prefixWord ++ tailWord_6345) baseStart_6345 baseEnd_6345 := by
    simpa [prefixWord, tailWord_6345, baseEnd_6345] using wordTrace_append hprefix tailTrace_6345
  have hstable : (prefixWord ++ tailWord_6345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345).length < 2 ^ (prefixWord ++ tailWord_6345).sum := by decide
  have hdescent : baseEnd_6345 < baseStart_6345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348 : List Nat := [2, 2, 1, 6, 2, 1, 7]
def baseStart_6348 : Nat := 118140960795 + 6348 * 2 ^ 59
def prefixEnd_6348 : Nat := 4983230072969 + 3 ^ 40 * 6348 * 2
def baseEnd_6348 : Nat := 160966676288710968929

theorem tailTrace_6348 : CollatzResearch.WordTrace tailWord_6348 prefixEnd_6348 160966676288710968929 := by
  unfold tailWord_6348
  simp only [CollatzResearch.WordTrace]
  refine ⟨115765290504877498597849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154353720673169998130465 115765290504877498597849)
  ·
    refine ⟨86823967878658123948387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115765290504877498597849 86823967878658123948387)
    ·
      refine ⟨130235951817987185922581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86823967878658123948387 130235951817987185922581)
      ·
        refine ⟨6104810241468149340121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 130235951817987185922581 6104810241468149340121)
        ·
          refine ⟨4578607681101112005091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6104810241468149340121 4578607681101112005091)
          ·
            refine ⟨6867911521651668007637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4578607681101112005091 6867911521651668007637)
            ·
              refine ⟨160966676288710968929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6867911521651668007637 160966676288710968929)
              ·
                rfl

theorem cell21_6348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 7].length) (baseStart_6348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6348 prefixEnd_6348 := by exact prefixLift 6348
  have htrace : WordTrace (prefixWord ++ tailWord_6348) baseStart_6348 baseEnd_6348 := by
    simpa [prefixWord, tailWord_6348, baseEnd_6348] using wordTrace_append hprefix tailTrace_6348
  have hstable : (prefixWord ++ tailWord_6348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348).length < 2 ^ (prefixWord ++ tailWord_6348).sum := by decide
  have hdescent : baseEnd_6348 < baseStart_6348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6359 : List Nat := [1, 1, 3, 2, 1, 2, 1, 6, 4]
def baseStart_6359 : Nat := 118140960795 + 6359 * 2 ^ 59
def prefixEnd_6359 : Nat := 4983230072969 + 3 ^ 40 * 6359 * 2
def baseEnd_6359 : Nat := 1451210436464824037005

theorem tailTrace_6359 : CollatzResearch.WordTrace tailWord_6359 prefixEnd_6359 1451210436464824037005 := by
  unfold tailWord_6359
  simp only [CollatzResearch.WordTrace]
  refine ⟨231931783969903875846131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154621189313269250564087 231931783969903875846131)
  ·
    refine ⟨347897675954855813769197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231931783969903875846131 347897675954855813769197)
    ·
      refine ⟨130461628483070930163449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347897675954855813769197 130461628483070930163449)
      ·
        refine ⟨97846221362303197622587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130461628483070930163449 97846221362303197622587)
        ·
          refine ⟨146769332043454796433881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97846221362303197622587 146769332043454796433881)
          ·
            refine ⟨110076999032591097325411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146769332043454796433881 110076999032591097325411)
            ·
              refine ⟨165115498548886645988117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110076999032591097325411 165115498548886645988117)
              ·
                refine ⟨7739788994479061530693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165115498548886645988117 7739788994479061530693)
                ·
                  refine ⟨1451210436464824037005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7739788994479061530693 1451210436464824037005)
                  ·
                    rfl

theorem cell21_6359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 4].length) (baseStart_6359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6359 prefixEnd_6359 := by exact prefixLift 6359
  have htrace : WordTrace (prefixWord ++ tailWord_6359) baseStart_6359 baseEnd_6359 := by
    simpa [prefixWord, tailWord_6359, baseEnd_6359] using wordTrace_append hprefix tailTrace_6359
  have hstable : (prefixWord ++ tailWord_6359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6359).length < 2 ^ (prefixWord ++ tailWord_6359).sum := by decide
  have hdescent : baseEnd_6359 < baseStart_6359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6376 : List Nat := [2, 1, 4, 1, 2, 3, 1, 3, 4]
def baseStart_6376 : Nat := 118140960795 + 6376 * 2 ^ 59
def prefixEnd_6376 : Nat := 4983230072969 + 3 ^ 40 * 6376 * 2
def baseEnd_6376 : Nat := 1455090068076572253637

theorem tailTrace_6376 : CollatzResearch.WordTrace tailWord_6376 prefixEnd_6376 1455090068076572253637 := by
  unfold tailWord_6376
  simp only [CollatzResearch.WordTrace]
  refine ⟨116275912454157889607491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155034549938877186143321 116275912454157889607491)
  ·
    refine ⟨174413868681236834411237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116275912454157889607491 174413868681236834411237)
    ·
      refine ⟨32702600377731906452107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174413868681236834411237 32702600377731906452107)
      ·
        refine ⟨49053900566597859678161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32702600377731906452107 49053900566597859678161)
        ·
          refine ⟨36790425424948394758621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49053900566597859678161 36790425424948394758621)
          ·
            refine ⟨13796409534355648034483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36790425424948394758621 13796409534355648034483)
            ·
              refine ⟨20694614301533472051725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13796409534355648034483 20694614301533472051725)
              ·
                refine ⟨7760480363075052019397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20694614301533472051725 7760480363075052019397)
                ·
                  refine ⟨1455090068076572253637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7760480363075052019397 1455090068076572253637)
                  ·
                    rfl

theorem cell21_6376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_6376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6376 prefixEnd_6376 := by exact prefixLift 6376
  have htrace : WordTrace (prefixWord ++ tailWord_6376) baseStart_6376 baseEnd_6376 := by
    simpa [prefixWord, tailWord_6376, baseEnd_6376] using wordTrace_append hprefix tailTrace_6376
  have hstable : (prefixWord ++ tailWord_6376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6376).length < 2 ^ (prefixWord ++ tailWord_6376).sum := by decide
  have hdescent : baseEnd_6376 < baseStart_6376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390 : List Nat := [5, 1, 1, 1, 1, 1, 4, 7]
def baseStart_6390 : Nat := 118140960795 + 6390 * 2 ^ 59
def prefixEnd_6390 : Nat := 4983230072969 + 3 ^ 40 * 6390 * 2
def baseEnd_6390 : Nat := 486095019605219673425

theorem tailTrace_6390 : CollatzResearch.WordTrace tailWord_6390 prefixEnd_6390 486095019605219673425 := by
  unfold tailWord_6390
  simp only [CollatzResearch.WordTrace]
  refine ⟨14566402928599760639039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155374964571730780149749 14566402928599760639039)
  ·
    refine ⟨21849604392899640958559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14566402928599760639039 21849604392899640958559)
    ·
      refine ⟨32774406589349461437839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21849604392899640958559 32774406589349461437839)
      ·
        refine ⟨49161609884024192156759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32774406589349461437839 49161609884024192156759)
        ·
          refine ⟨73742414826036288235139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49161609884024192156759 73742414826036288235139)
          ·
            refine ⟨110613622239054432352709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73742414826036288235139 110613622239054432352709)
            ·
              refine ⟨20740054169822706066133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110613622239054432352709 20740054169822706066133)
              ·
                refine ⟨486095019605219673425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20740054169822706066133 486095019605219673425)
                ·
                  rfl

theorem cell21_6390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_6390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6390 prefixEnd_6390 := by exact prefixLift 6390
  have htrace : WordTrace (prefixWord ++ tailWord_6390) baseStart_6390 baseEnd_6390 := by
    simpa [prefixWord, tailWord_6390, baseEnd_6390] using wordTrace_append hprefix tailTrace_6390
  have hstable : (prefixWord ++ tailWord_6390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390).length < 2 ^ (prefixWord ++ tailWord_6390).sum := by decide
  have hdescent : baseEnd_6390 < baseStart_6390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6407 : List Nat := [1, 1, 4, 5, 2, 8]
def baseStart_6407 : Nat := 118140960795 + 6407 * 2 ^ 59
def prefixEnd_6407 : Nat := 4983230072969 + 3 ^ 40 * 6407 * 2
def baseEnd_6407 : Nat := 54154247793607675441

theorem tailTrace_6407 : CollatzResearch.WordTrace tailWord_6407 prefixEnd_6407 54154247793607675441 := by
  unfold tailWord_6407
  simp only [CollatzResearch.WordTrace]
  refine ⟨233682487796008073593475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155788325197338715728983 233682487796008073593475)
  ·
    refine ⟨350523731694012110390213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233682487796008073593475 350523731694012110390213)
    ·
      refine ⟨65723199692627270698165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 350523731694012110390213 65723199692627270698165)
      ·
        refine ⟨6161549971183806627953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65723199692627270698165 6161549971183806627953)
        ·
          refine ⟨4621162478387854970965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6161549971183806627953 4621162478387854970965)
          ·
            refine ⟨54154247793607675441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 4621162478387854970965 54154247793607675441)
            ·
              rfl

theorem cell21_6407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 8].length) (baseStart_6407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6407 prefixEnd_6407 := by exact prefixLift 6407
  have htrace : WordTrace (prefixWord ++ tailWord_6407) baseStart_6407 baseEnd_6407 := by
    simpa [prefixWord, tailWord_6407, baseEnd_6407] using wordTrace_append hprefix tailTrace_6407
  have hstable : (prefixWord ++ tailWord_6407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6407).length < 2 ^ (prefixWord ++ tailWord_6407).sum := by decide
  have hdescent : baseEnd_6407 < baseStart_6407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435 : List Nat := [1, 1, 1, 4, 2, 2, 1, 5, 4]
def baseStart_6435 : Nat := 118140960795 + 6435 * 2 ^ 59
def prefixEnd_6435 : Nat := 4983230072969 + 3 ^ 40 * 6435 * 2
def baseEnd_6435 : Nat := 1468554671905580770183

theorem tailTrace_6435 : CollatzResearch.WordTrace tailWord_6435 prefixEnd_6435 1468554671905580770183 := by
  unfold tailWord_6435
  simp only [CollatzResearch.WordTrace]
  refine ⟨234703731694568855612759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156469154463045903741839 234703731694568855612759)
  ·
    refine ⟨352055597541853283419139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234703731694568855612759 352055597541853283419139)
    ·
      refine ⟨528083396312779925128709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352055597541853283419139 528083396312779925128709)
      ·
        refine ⟨99015636808646235961633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 528083396312779925128709 99015636808646235961633)
        ·
          refine ⟨74261727606484676971225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99015636808646235961633 74261727606484676971225)
          ·
            refine ⟨55696295704863507728419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74261727606484676971225 55696295704863507728419)
            ·
              refine ⟨83544443557295261592629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55696295704863507728419 83544443557295261592629)
              ·
                refine ⟨7832291583496430774309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83544443557295261592629 7832291583496430774309)
                ·
                  refine ⟨1468554671905580770183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7832291583496430774309 1468554671905580770183)
                  ·
                    rfl

theorem cell21_6435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 4].length) (baseStart_6435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6435 prefixEnd_6435 := by exact prefixLift 6435
  have htrace : WordTrace (prefixWord ++ tailWord_6435) baseStart_6435 baseEnd_6435 := by
    simpa [prefixWord, tailWord_6435, baseEnd_6435] using wordTrace_append hprefix tailTrace_6435
  have hstable : (prefixWord ++ tailWord_6435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435).length < 2 ^ (prefixWord ++ tailWord_6435).sum := by decide
  have hdescent : baseEnd_6435 < baseStart_6435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6480 : List Nat := [2, 1, 1, 1, 1, 6, 1, 3, 5]
def baseStart_6480 : Nat := 118140960795 + 6480 * 2 ^ 59
def prefixEnd_6480 : Nat := 4983230072969 + 3 ^ 40 * 6480 * 2
def baseEnd_6480 : Nat := 1478824284995502520091

theorem tailTrace_6480 : CollatzResearch.WordTrace tailWord_6480 prefixEnd_6480 1478824284995502520091 := by
  unfold tailWord_6480
  simp only [CollatzResearch.WordTrace]
  refine ⟨118172508265770770500447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157563344354361027333929 118172508265770770500447)
  ·
    refine ⟨177258762398656155750671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118172508265770770500447 177258762398656155750671)
    ·
      refine ⟨265888143597984233626007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177258762398656155750671 265888143597984233626007)
      ·
        refine ⟨398832215396976350439011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265888143597984233626007 398832215396976350439011)
        ·
          refine ⟨598248323095464525658517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398832215396976350439011 598248323095464525658517)
          ·
            refine ⟨28042890145099899640243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 598248323095464525658517 28042890145099899640243)
            ·
              refine ⟨42064335217649849460365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28042890145099899640243 42064335217649849460365)
              ·
                refine ⟨15774125706618693547637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42064335217649849460365 15774125706618693547637)
                ·
                  refine ⟨1478824284995502520091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15774125706618693547637 1478824284995502520091)
                  ·
                    rfl

theorem cell21_6480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_6480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6480 prefixEnd_6480 := by exact prefixLift 6480
  have htrace : WordTrace (prefixWord ++ tailWord_6480) baseStart_6480 baseEnd_6480 := by
    simpa [prefixWord, tailWord_6480, baseEnd_6480] using wordTrace_append hprefix tailTrace_6480
  have hstable : (prefixWord ++ tailWord_6480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6480).length < 2 ^ (prefixWord ++ tailWord_6480).sum := by decide
  have hdescent : baseEnd_6480 < baseStart_6480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514 : List Nat := [3, 2, 1, 2, 1, 3, 3, 3, 3]
def baseStart_6514 : Nat := 118140960795 + 6514 * 2 ^ 59
def prefixEnd_6514 : Nat := 4983230072969 + 3 ^ 40 * 6514 * 2
def baseEnd_6514 : Nat := 1486583548218998953355

theorem tailTrace_6514 : CollatzResearch.WordTrace tailWord_6514 prefixEnd_6514 1486583548218998953355 := by
  unfold tailWord_6514
  simp only [CollatzResearch.WordTrace]
  refine ⟨59396274602091336934649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158390065605576898492397 59396274602091336934649)
  ·
    refine ⟨44547205951568502700987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59396274602091336934649 44547205951568502700987)
    ·
      refine ⟨66820808927352754051481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44547205951568502700987 66820808927352754051481)
      ·
        refine ⟨50115606695514565538611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66820808927352754051481 50115606695514565538611)
        ·
          refine ⟨75173410043271848307917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50115606695514565538611 75173410043271848307917)
          ·
            refine ⟨28190028766226943115469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75173410043271848307917 28190028766226943115469)
            ·
              refine ⟨10571260787335103668301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28190028766226943115469 10571260787335103668301)
              ·
                refine ⟨3964222795250663875613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10571260787335103668301 3964222795250663875613)
                ·
                  refine ⟨1486583548218998953355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3964222795250663875613 1486583548218998953355)
                  ·
                    rfl

theorem cell21_6514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_6514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6514 prefixEnd_6514 := by exact prefixLift 6514
  have htrace : WordTrace (prefixWord ++ tailWord_6514) baseStart_6514 baseEnd_6514 := by
    simpa [prefixWord, tailWord_6514, baseEnd_6514] using wordTrace_append hprefix tailTrace_6514
  have hstable : (prefixWord ++ tailWord_6514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514).length < 2 ^ (prefixWord ++ tailWord_6514).sum := by decide
  have hdescent : baseEnd_6514 < baseStart_6514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525 : List Nat := [1, 4, 1, 1, 2, 3, 9]
def baseStart_6525 : Nat := 118140960795 + 6525 * 2 ^ 59
def prefixEnd_6525 : Nat := 4983230072969 + 3 ^ 40 * 6525 * 2
def baseEnd_6525 : Nat := 165454877565047141111

theorem tailTrace_6525 : CollatzResearch.WordTrace tailWord_6525 prefixEnd_6525 165454877565047141111 := by
  unfold tailWord_6525
  simp only [CollatzResearch.WordTrace]
  refine ⟨237986301368514226389029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158657534245676150926019 237986301368514226389029)
  ·
    refine ⟨44622431506596417447943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237986301368514226389029 44622431506596417447943)
    ·
      refine ⟨66933647259894626171915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44622431506596417447943 66933647259894626171915)
      ·
        refine ⟨100400470889841939257873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66933647259894626171915 100400470889841939257873)
        ·
          refine ⟨75300353167381454443405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100400470889841939257873 75300353167381454443405)
          ·
            refine ⟨28237632437768045416277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75300353167381454443405 28237632437768045416277)
            ·
              refine ⟨165454877565047141111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 28237632437768045416277 165454877565047141111)
              ·
                rfl

theorem cell21_6525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 9].length) (baseStart_6525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6525 prefixEnd_6525 := by exact prefixLift 6525
  have htrace : WordTrace (prefixWord ++ tailWord_6525) baseStart_6525 baseEnd_6525 := by
    simpa [prefixWord, tailWord_6525, baseEnd_6525] using wordTrace_append hprefix tailTrace_6525
  have hstable : (prefixWord ++ tailWord_6525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525).length < 2 ^ (prefixWord ++ tailWord_6525).sum := by decide
  have hdescent : baseEnd_6525 < baseStart_6525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531 : List Nat := [1, 1, 1, 3, 6, 1, 3, 2, 3]
def baseStart_6531 : Nat := 118140960795 + 6531 * 2 ^ 59
def prefixEnd_6531 : Nat := 4983230072969 + 3 ^ 40 * 6531 * 2
def baseEnd_6531 : Nat := 1490463179830747169987

theorem tailTrace_6531 : CollatzResearch.WordTrace tailWord_6531 prefixEnd_6531 1490463179830747169987 := by
  unfold tailWord_6531
  simp only [CollatzResearch.WordTrace]
  refine ⟨238205139346777251107447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158803426231184834071631 238205139346777251107447)
  ·
    refine ⟨357307709020165876661171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238205139346777251107447 357307709020165876661171)
    ·
      refine ⟨535961563530248814991757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357307709020165876661171 535961563530248814991757)
      ·
        refine ⟨200985586323843305621909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 535961563530248814991757 200985586323843305621909)
        ·
          refine ⟨9421199358930154951027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 200985586323843305621909 9421199358930154951027)
          ·
            refine ⟨14131799038395232426541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9421199358930154951027 14131799038395232426541)
            ·
              refine ⟨5299424639398212159953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14131799038395232426541 5299424639398212159953)
              ·
                refine ⟨3974568479548659119965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5299424639398212159953 3974568479548659119965)
                ·
                  refine ⟨1490463179830747169987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3974568479548659119965 1490463179830747169987)
                  ·
                    rfl

theorem cell21_6531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 3].length) (baseStart_6531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6531 prefixEnd_6531 := by exact prefixLift 6531
  have htrace : WordTrace (prefixWord ++ tailWord_6531) baseStart_6531 baseEnd_6531 := by
    simpa [prefixWord, tailWord_6531, baseEnd_6531] using wordTrace_append hprefix tailTrace_6531
  have hstable : (prefixWord ++ tailWord_6531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531).length < 2 ^ (prefixWord ++ tailWord_6531).sum := by decide
  have hdescent : baseEnd_6531 < baseStart_6531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6542 : List Nat := [4, 1, 1, 4, 1, 1, 1, 8]
def baseStart_6542 : Nat := 118140960795 + 6542 * 2 ^ 59
def prefixEnd_6542 : Nat := 4983230072969 + 3 ^ 40 * 6542 * 2
def baseEnd_6542 : Nat := 497657843232390828877

theorem tailTrace_6542 : CollatzResearch.WordTrace tailWord_6542 prefixEnd_6542 497657843232390828877 := by
  unfold tailWord_6542
  simp only [CollatzResearch.WordTrace]
  refine ⟨29825792788365766219735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159070894871284086505253 29825792788365766219735)
  ·
    refine ⟨44738689182548649329603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29825792788365766219735 44738689182548649329603)
    ·
      refine ⟨67108033773822973994405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44738689182548649329603 67108033773822973994405)
      ·
        refine ⟨12582756332591807623951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67108033773822973994405 12582756332591807623951)
        ·
          refine ⟨18874134498887711435927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12582756332591807623951 18874134498887711435927)
          ·
            refine ⟨28311201748331567153891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18874134498887711435927 28311201748331567153891)
            ·
              refine ⟨42466802622497350730837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28311201748331567153891 42466802622497350730837)
              ·
                refine ⟨497657843232390828877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 42466802622497350730837 497657843232390828877)
                ·
                  rfl

theorem cell21_6542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_6542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6542 prefixEnd_6542 := by exact prefixLift 6542
  have htrace : WordTrace (prefixWord ++ tailWord_6542) baseStart_6542 baseEnd_6542 := by
    simpa [prefixWord, tailWord_6542, baseEnd_6542] using wordTrace_append hprefix tailTrace_6542
  have hstable : (prefixWord ++ tailWord_6542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6542).length < 2 ^ (prefixWord ++ tailWord_6542).sum := by decide
  have hdescent : baseEnd_6542 < baseStart_6542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593 : List Nat := [1, 2, 7, 1, 1, 2, 1, 6]
def baseStart_6593 : Nat := 118140960795 + 6593 * 2 ^ 59
def prefixEnd_6593 : Nat := 4983230072969 + 3 ^ 40 * 6593 * 2
def baseEnd_6593 : Nat := 501537474844139045509

theorem tailTrace_6593 : CollatzResearch.WordTrace tailWord_6593 prefixEnd_6593 501537474844139045509 := by
  unfold tailWord_6593
  simp only [CollatzResearch.WordTrace]
  refine ⟨240466465122161839864433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160310976748107893242955 240466465122161839864433)
  ·
    refine ⟨180349848841621379898325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240466465122161839864433 180349848841621379898325)
    ·
      refine ⟨4226949582225501091367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 180349848841621379898325 4226949582225501091367)
      ·
        refine ⟨6340424373338251637051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4226949582225501091367 6340424373338251637051)
        ·
          refine ⟨9510636560007377455577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6340424373338251637051 9510636560007377455577)
          ·
            refine ⟨7132977420005533091683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9510636560007377455577 7132977420005533091683)
            ·
              refine ⟨10699466130008299637525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7132977420005533091683 10699466130008299637525)
              ·
                refine ⟨501537474844139045509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10699466130008299637525 501537474844139045509)
                ·
                  rfl

theorem cell21_6593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 6].length) (baseStart_6593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6593 prefixEnd_6593 := by exact prefixLift 6593
  have htrace : WordTrace (prefixWord ++ tailWord_6593) baseStart_6593 baseEnd_6593 := by
    simpa [prefixWord, tailWord_6593, baseEnd_6593] using wordTrace_append hprefix tailTrace_6593
  have hstable : (prefixWord ++ tailWord_6593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593).length < 2 ^ (prefixWord ++ tailWord_6593).sum := by decide
  have hdescent : baseEnd_6593 < baseStart_6593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601 : List Nat := [1, 2, 1, 1, 2, 1, 7, 6]
def baseStart_6601 : Nat := 118140960795 + 6601 * 2 ^ 59
def prefixEnd_6601 : Nat := 4983230072969 + 3 ^ 40 * 6601 * 2
def baseEnd_6601 : Nat := 502146044508727001059

theorem tailTrace_6601 : CollatzResearch.WordTrace tailWord_6601 prefixEnd_6601 502146044508727001059 := by
  unfold tailWord_6601
  simp only [CollatzResearch.WordTrace]
  refine ⟨240758249093179206155657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160505499395452804103771 240758249093179206155657)
  ·
    refine ⟨180568686819884404616743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240758249093179206155657 180568686819884404616743)
    ·
      refine ⟨270853030229826606925115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180568686819884404616743 270853030229826606925115)
      ·
        refine ⟨406279545344739910387673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270853030229826606925115 406279545344739910387673)
        ·
          refine ⟨304709659008554932790755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406279545344739910387673 304709659008554932790755)
          ·
            refine ⟨457064488512832399186133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304709659008554932790755 457064488512832399186133)
            ·
              refine ⟨10712448949519509355925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 457064488512832399186133 10712448949519509355925)
              ·
                refine ⟨502146044508727001059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10712448949519509355925 502146044508727001059)
                ·
                  rfl

theorem cell21_6601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 6].length) (baseStart_6601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6601 prefixEnd_6601 := by exact prefixLift 6601
  have htrace : WordTrace (prefixWord ++ tailWord_6601) baseStart_6601 baseEnd_6601 := by
    simpa [prefixWord, tailWord_6601, baseEnd_6601] using wordTrace_append hprefix tailTrace_6601
  have hstable : (prefixWord ++ tailWord_6601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601).length < 2 ^ (prefixWord ++ tailWord_6601).sum := by decide
  have hdescent : baseEnd_6601 < baseStart_6601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618 : List Nat := [3, 1, 1, 2, 3, 1, 5, 5]
def baseStart_6618 : Nat := 118140960795 + 6618 * 2 ^ 59
def prefixEnd_6618 : Nat := 4983230072969 + 3 ^ 40 * 6618 * 2
def baseEnd_6618 : Nat := 503439255045976406603

theorem tailTrace_6618 : CollatzResearch.WordTrace tailWord_6618 prefixEnd_6618 503439255045976406603 := by
  unfold tailWord_6618
  simp only [CollatzResearch.WordTrace]
  refine ⟨60344572507897777381127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160918860021060739683005 60344572507897777381127)
  ·
    refine ⟨90516858761846666071691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60344572507897777381127 90516858761846666071691)
    ·
      refine ⟨135775288142769999107537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90516858761846666071691 135775288142769999107537)
      ·
        refine ⟨101831466107077499330653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135775288142769999107537 101831466107077499330653)
        ·
          refine ⟨38186799790154062248995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101831466107077499330653 38186799790154062248995)
          ·
            refine ⟨57280199685231093373493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38186799790154062248995 57280199685231093373493)
            ·
              refine ⟨5370018720490415003765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57280199685231093373493 5370018720490415003765)
              ·
                refine ⟨503439255045976406603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5370018720490415003765 503439255045976406603)
                ·
                  rfl

theorem cell21_6618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_6618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6618 prefixEnd_6618 := by exact prefixLift 6618
  have htrace : WordTrace (prefixWord ++ tailWord_6618) baseStart_6618 baseEnd_6618 := by
    simpa [prefixWord, tailWord_6618, baseEnd_6618] using wordTrace_append hprefix tailTrace_6618
  have hstable : (prefixWord ++ tailWord_6618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618).length < 2 ^ (prefixWord ++ tailWord_6618).sum := by decide
  have hdescent : baseEnd_6618 < baseStart_6618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6649 : List Nat := [1, 2, 1, 3, 1, 2, 4, 4, 3]
def baseStart_6649 : Nat := 118140960795 + 6649 * 2 ^ 59
def prefixEnd_6649 : Nat := 4983230072969 + 3 ^ 40 * 6649 * 2
def baseEnd_6649 : Nat := 1517392387488764203079

theorem tailTrace_6649 : CollatzResearch.WordTrace tailWord_6649 prefixEnd_6649 1517392387488764203079 := by
  unfold tailWord_6649
  simp only [CollatzResearch.WordTrace]
  refine ⟨242508952919283403903001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161672635279522269268667 242508952919283403903001)
  ·
    refine ⟨181881714689462552927251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242508952919283403903001 181881714689462552927251)
    ·
      refine ⟨272822572034193829390877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181881714689462552927251 272822572034193829390877)
      ·
        refine ⟨102308464512822686021579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272822572034193829390877 102308464512822686021579)
        ·
          refine ⟨153462696769234029032369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102308464512822686021579 153462696769234029032369)
          ·
            refine ⟨115097022576925521774277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153462696769234029032369 115097022576925521774277)
            ·
              refine ⟨21580691733173535332677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115097022576925521774277 21580691733173535332677)
              ·
                refine ⟨4046379699970037874877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21580691733173535332677 4046379699970037874877)
                ·
                  refine ⟨1517392387488764203079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4046379699970037874877 1517392387488764203079)
                  ·
                    rfl

theorem cell21_6649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 3].length) (baseStart_6649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6649 prefixEnd_6649 := by exact prefixLift 6649
  have htrace : WordTrace (prefixWord ++ tailWord_6649) baseStart_6649 baseEnd_6649 := by
    simpa [prefixWord, tailWord_6649, baseEnd_6649] using wordTrace_append hprefix tailTrace_6649
  have hstable : (prefixWord ++ tailWord_6649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6649).length < 2 ^ (prefixWord ++ tailWord_6649).sum := by decide
  have hdescent : baseEnd_6649 < baseStart_6649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669 : List Nat := [1, 7, 1, 1, 1, 3, 2, 5]
def baseStart_6669 : Nat := 118140960795 + 6669 * 2 ^ 59
def prefixEnd_6669 : Nat := 4983230072969 + 3 ^ 40 * 6669 * 2
def baseEnd_6669 : Nat := 507318886657724623235

theorem tailTrace_6669 : CollatzResearch.WordTrace tailWord_6669 prefixEnd_6669 507318886657724623235 := by
  unfold tailWord_6669
  simp only [CollatzResearch.WordTrace]
  refine ⟨243238412846826819631061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162158941897884546420707 243238412846826819631061)
  ·
    refine ⟨5700900301097503585103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 243238412846826819631061 5700900301097503585103)
    ·
      refine ⟨8551350451646255377655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5700900301097503585103 8551350451646255377655)
      ·
        refine ⟨12827025677469383066483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8551350451646255377655 12827025677469383066483)
        ·
          refine ⟨19240538516204074599725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12827025677469383066483 19240538516204074599725)
          ·
            refine ⟨7215201943576527974897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19240538516204074599725 7215201943576527974897)
            ·
              refine ⟨5411401457682395981173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7215201943576527974897 5411401457682395981173)
              ·
                refine ⟨507318886657724623235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5411401457682395981173 507318886657724623235)
                ·
                  rfl

theorem cell21_6669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 5].length) (baseStart_6669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6669 prefixEnd_6669 := by exact prefixLift 6669
  have htrace : WordTrace (prefixWord ++ tailWord_6669) baseStart_6669 baseEnd_6669 := by
    simpa [prefixWord, tailWord_6669, baseEnd_6669] using wordTrace_append hprefix tailTrace_6669
  have hstable : (prefixWord ++ tailWord_6669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669).length < 2 ^ (prefixWord ++ tailWord_6669).sum := by decide
  have hdescent : baseEnd_6669 < baseStart_6669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677 : List Nat := [1, 3, 2, 1, 3, 1, 3, 7]
def baseStart_6677 : Nat := 118140960795 + 6677 * 2 ^ 59
def prefixEnd_6677 : Nat := 4983230072969 + 3 ^ 40 * 6677 * 2
def baseEnd_6677 : Nat := 507927456322312578785

theorem tailTrace_6677 : CollatzResearch.WordTrace tailWord_6677 prefixEnd_6677 507927456322312578785 := by
  unfold tailWord_6677
  simp only [CollatzResearch.WordTrace]
  refine ⟨243530196817844185922285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162353464545229457281523 243530196817844185922285)
  ·
    refine ⟨91323823806691569720857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243530196817844185922285 91323823806691569720857)
    ·
      refine ⟨68492867855018677290643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91323823806691569720857 68492867855018677290643)
      ·
        refine ⟨102739301782528015935965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68492867855018677290643 102739301782528015935965)
        ·
          refine ⟨38527238168448005975987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102739301782528015935965 38527238168448005975987)
          ·
            refine ⟨57790857252672008963981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38527238168448005975987 57790857252672008963981)
            ·
              refine ⟨21671571469752003361493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57790857252672008963981 21671571469752003361493)
              ·
                refine ⟨507927456322312578785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21671571469752003361493 507927456322312578785)
                ·
                  rfl

theorem cell21_6677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 7].length) (baseStart_6677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6677 prefixEnd_6677 := by exact prefixLift 6677
  have htrace : WordTrace (prefixWord ++ tailWord_6677) baseStart_6677 baseEnd_6677 := by
    simpa [prefixWord, tailWord_6677, baseEnd_6677] using wordTrace_append hprefix tailTrace_6677
  have hstable : (prefixWord ++ tailWord_6677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677).length < 2 ^ (prefixWord ++ tailWord_6677).sum := by decide
  have hdescent : baseEnd_6677 < baseStart_6677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6784 : List Nat := [2, 1, 1, 2, 1, 6, 1, 2, 5]
def baseStart_6784 : Nat := 118140960795 + 6784 * 2 ^ 59
def prefixEnd_6784 : Nat := 4983230072969 + 3 ^ 40 * 6784 * 2
def baseEnd_6784 : Nat := 1548201226758529452803

theorem tailTrace_6784 : CollatzResearch.WordTrace tailWord_6784 prefixEnd_6784 1548201226758529452803 := by
  unfold tailWord_6784
  simp only [CollatzResearch.WordTrace]
  refine ⟨123716403715100730033703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164955204953467640044937 123716403715100730033703)
  ·
    refine ⟨185574605572651095050555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123716403715100730033703 185574605572651095050555)
    ·
      refine ⟨278361908358976642575833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185574605572651095050555 278361908358976642575833)
      ·
        refine ⟨208771431269232481931875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278361908358976642575833 208771431269232481931875)
        ·
          refine ⟨313157146903848722897813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208771431269232481931875 313157146903848722897813)
          ·
            refine ⟨14679241261117908885835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 313157146903848722897813 14679241261117908885835)
            ·
              refine ⟨22018861891676863328753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14679241261117908885835 22018861891676863328753)
              ·
                refine ⟨16514146418757647496565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22018861891676863328753 16514146418757647496565)
                ·
                  refine ⟨1548201226758529452803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16514146418757647496565 1548201226758529452803)
                  ·
                    rfl

theorem cell21_6784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_6784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6784 prefixEnd_6784 := by exact prefixLift 6784
  have htrace : WordTrace (prefixWord ++ tailWord_6784) baseStart_6784 baseEnd_6784 := by
    simpa [prefixWord, tailWord_6784, baseEnd_6784] using wordTrace_append hprefix tailTrace_6784
  have hstable : (prefixWord ++ tailWord_6784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6784).length < 2 ^ (prefixWord ++ tailWord_6784).sum := by decide
  have hdescent : baseEnd_6784 < baseStart_6784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6874 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 6]
def baseStart_6874 : Nat := 118140960795 + 6874 * 2 ^ 59
def prefixEnd_6874 : Nat := 4983230072969 + 3 ^ 40 * 6874 * 2
def baseEnd_6874 : Nat := 1568740452938372952619

theorem tailTrace_6874 : CollatzResearch.WordTrace tailWord_6874 prefixEnd_6874 1568740452938372952619 := by
  unfold tailWord_6874
  simp only [CollatzResearch.WordTrace]
  refine ⟨62678844276036707710919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167143584736097887229117 62678844276036707710919)
  ·
    refine ⟨94018266414055061566379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62678844276036707710919 94018266414055061566379)
    ·
      refine ⟨141027399621082592349569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94018266414055061566379 141027399621082592349569)
      ·
        refine ⟨105770549715811944262177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141027399621082592349569 105770549715811944262177)
        ·
          refine ⟨79327912286858958196633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105770549715811944262177 79327912286858958196633)
          ·
            refine ⟨59495934215144218647475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79327912286858958196633 59495934215144218647475)
            ·
              refine ⟨89243901322716327971213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59495934215144218647475 89243901322716327971213)
              ·
                refine ⟨33466462996018622989205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89243901322716327971213 33466462996018622989205)
                ·
                  refine ⟨1568740452938372952619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33466462996018622989205 1568740452938372952619)
                  ·
                    rfl

theorem cell21_6874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_6874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6874 prefixEnd_6874 := by exact prefixLift 6874
  have htrace : WordTrace (prefixWord ++ tailWord_6874) baseStart_6874 baseEnd_6874 := by
    simpa [prefixWord, tailWord_6874, baseEnd_6874] using wordTrace_append hprefix tailTrace_6874
  have hstable : (prefixWord ++ tailWord_6874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6874).length < 2 ^ (prefixWord ++ tailWord_6874).sum := by decide
  have hdescent : baseEnd_6874 < baseStart_6874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6970 : List Nat := [3, 1, 1, 1, 6, 1, 2, 3, 3]
def baseStart_6970 : Nat := 118140960795 + 6970 * 2 ^ 59
def prefixEnd_6970 : Nat := 4983230072969 + 3 ^ 40 * 6970 * 2
def baseEnd_6970 : Nat := 1590648960863539352423

theorem tailTrace_6970 : CollatzResearch.WordTrace tailWord_6970 prefixEnd_6970 1590648960863539352423 := by
  unfold tailWord_6970
  simp only [CollatzResearch.WordTrace]
  refine ⟨63554196189088806584591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169477856504236817558909 63554196189088806584591)
  ·
    refine ⟨95331294283633209876887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63554196189088806584591 95331294283633209876887)
    ·
      refine ⟨142996941425449814815331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95331294283633209876887 142996941425449814815331)
      ·
        refine ⟨214495412138174722222997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142996941425449814815331 214495412138174722222997)
        ·
          refine ⟨10054472443976940104203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 214495412138174722222997 10054472443976940104203)
          ·
            refine ⟨15081708665965410156305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10054472443976940104203 15081708665965410156305)
            ·
              refine ⟨11311281499474057617229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15081708665965410156305 11311281499474057617229)
              ·
                refine ⟨4241730562302771606461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11311281499474057617229 4241730562302771606461)
                ·
                  refine ⟨1590648960863539352423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4241730562302771606461 1590648960863539352423)
                  ·
                    rfl

theorem cell21_6970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_6970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_6970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_6970 prefixEnd_6970 := by exact prefixLift 6970
  have htrace : WordTrace (prefixWord ++ tailWord_6970) baseStart_6970 baseEnd_6970 := by
    simpa [prefixWord, tailWord_6970, baseEnd_6970] using wordTrace_append hprefix tailTrace_6970
  have hstable : (prefixWord ++ tailWord_6970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6970).length < 2 ^ (prefixWord ++ tailWord_6970).sum := by decide
  have hdescent : baseEnd_6970 < baseStart_6970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012 : List Nat := [2, 3, 1, 1, 4, 1, 2, 2, 5]
def baseStart_7012 : Nat := 118140960795 + 7012 * 2 ^ 59
def prefixEnd_7012 : Nat := 4983230072969 + 3 ^ 40 * 7012 * 2
def baseEnd_7012 : Nat := 1600233933080799652337

theorem tailTrace_7012 : CollatzResearch.WordTrace tailWord_7012 prefixEnd_7012 1600233933080799652337 := by
  unfold tailWord_7012
  simp only [CollatzResearch.WordTrace]
  refine ⟨127874325302098199683645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170499100402797599578193 127874325302098199683645)
  ·
    refine ⟨47952871988286824881367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127874325302098199683645 47952871988286824881367)
    ·
      refine ⟨71929307982430237322051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47952871988286824881367 71929307982430237322051)
      ·
        refine ⟨107893961973645355983077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71929307982430237322051 107893961973645355983077)
        ·
          refine ⟨20230117870058504246827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107893961973645355983077 20230117870058504246827)
          ·
            refine ⟨30345176805087756370241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20230117870058504246827 30345176805087756370241)
            ·
              refine ⟨22758882603815817277681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30345176805087756370241 22758882603815817277681)
              ·
                refine ⟨17069161952861862958261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22758882603815817277681 17069161952861862958261)
                ·
                  refine ⟨1600233933080799652337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17069161952861862958261 1600233933080799652337)
                  ·
                    rfl

theorem cell21_7012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_7012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_7012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_7012 prefixEnd_7012 := by exact prefixLift 7012
  have htrace : WordTrace (prefixWord ++ tailWord_7012) baseStart_7012 baseEnd_7012 := by
    simpa [prefixWord, tailWord_7012, baseEnd_7012] using wordTrace_append hprefix tailTrace_7012
  have hstable : (prefixWord ++ tailWord_7012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012).length < 2 ^ (prefixWord ++ tailWord_7012).sum := by decide
  have hdescent : baseEnd_7012 < baseStart_7012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 6]
def baseStart_7026 : Nat := 118140960795 + 7026 * 2 ^ 59
def prefixEnd_7026 : Nat := 4983230072969 + 3 ^ 40 * 7026 * 2
def baseEnd_7026 : Nat := 1603428923819886418975

theorem tailTrace_7026 : CollatzResearch.WordTrace tailWord_7026 prefixEnd_7026 1603428923819886418975 := by
  unfold tailWord_7026
  simp only [CollatzResearch.WordTrace]
  refine ⟨64064818138369197594233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170839515035651193584621 64064818138369197594233)
  ·
    refine ⟨48048613603776898195675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64064818138369197594233 48048613603776898195675)
    ·
      refine ⟨72072920405665347293513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48048613603776898195675 72072920405665347293513)
      ·
        refine ⟨54054690304249010470135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72072920405665347293513 54054690304249010470135)
        ·
          refine ⟨81082035456373515705203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54054690304249010470135 81082035456373515705203)
          ·
            refine ⟨121623053184560273557805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81082035456373515705203 121623053184560273557805)
            ·
              refine ⟨45608644944210102584177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121623053184560273557805 45608644944210102584177)
              ·
                refine ⟨34206483708157576938133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45608644944210102584177 34206483708157576938133)
                ·
                  refine ⟨1603428923819886418975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34206483708157576938133 1603428923819886418975)
                  ·
                    rfl

theorem cell21_7026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_7026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_7026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_7026 prefixEnd_7026 := by exact prefixLift 7026
  have htrace : WordTrace (prefixWord ++ tailWord_7026) baseStart_7026 baseEnd_7026 := by
    simpa [prefixWord, tailWord_7026, baseEnd_7026] using wordTrace_append hprefix tailTrace_7026
  have hstable : (prefixWord ++ tailWord_7026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026).length < 2 ^ (prefixWord ++ tailWord_7026).sum := by decide
  have hdescent : baseEnd_7026 < baseStart_7026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108 : List Nat := [2, 3, 3, 3, 2, 1, 1, 6]
def baseStart_7108 : Nat := 118140960795 + 7108 * 2 ^ 59
def prefixEnd_7108 : Nat := 4983230072969 + 3 ^ 40 * 7108 * 2
def baseEnd_7108 : Nat := 540714147001988684047

theorem tailTrace_7108 : CollatzResearch.WordTrace tailWord_7108 prefixEnd_7108 540714147001988684047 := by
  unfold tailWord_7108
  simp only [CollatzResearch.WordTrace]
  refine ⟨129625029128202397430989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172833372170936529907985 129625029128202397430989)
  ·
    refine ⟨48609385923075899036621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129625029128202397430989 48609385923075899036621)
    ·
      refine ⟨18228519721153462138733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48609385923075899036621 18228519721153462138733)
      ·
        refine ⟨6835694895432548302025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18228519721153462138733 6835694895432548302025)
        ·
          refine ⟨5126771171574411226519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6835694895432548302025 5126771171574411226519)
          ·
            refine ⟨7690156757361616839779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5126771171574411226519 7690156757361616839779)
            ·
              refine ⟨11535235136042425259669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7690156757361616839779 11535235136042425259669)
              ·
                refine ⟨540714147001988684047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11535235136042425259669 540714147001988684047)
                ·
                  rfl

theorem cell21_7108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 6].length) (baseStart_7108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_7108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_7108 prefixEnd_7108 := by exact prefixLift 7108
  have htrace : WordTrace (prefixWord ++ tailWord_7108) baseStart_7108 baseEnd_7108 := by
    simpa [prefixWord, tailWord_7108, baseEnd_7108] using wordTrace_append hprefix tailTrace_7108
  have hstable : (prefixWord ++ tailWord_7108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108).length < 2 ^ (prefixWord ++ tailWord_7108).sum := by decide
  have hdescent : baseEnd_7108 < baseStart_7108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7156 : List Nat := [2, 6, 2, 1, 1, 1, 2, 1, 5]
def baseStart_7156 : Nat := 118140960795 + 7156 * 2 ^ 59
def prefixEnd_7156 : Nat := 4983230072969 + 3 ^ 40 * 7156 * 2
def baseEnd_7156 : Nat := 1633096694968549252043

theorem tailTrace_7156 : CollatzResearch.WordTrace tailWord_7156 prefixEnd_7156 1633096694968549252043 := by
  unfold tailWord_7156
  simp only [CollatzResearch.WordTrace]
  refine ⟨130500381041254496304661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174000508055005995072881 130500381041254496304661)
  ·
    refine ⟨6117205361308804514281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 130500381041254496304661 6117205361308804514281)
    ·
      refine ⟨4587904020981603385711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6117205361308804514281 4587904020981603385711)
      ·
        refine ⟨6881856031472405078567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4587904020981603385711 6881856031472405078567)
        ·
          refine ⟨10322784047208607617851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6881856031472405078567 10322784047208607617851)
          ·
            refine ⟨15484176070812911426777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10322784047208607617851 15484176070812911426777)
            ·
              refine ⟨11613132053109683570083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15484176070812911426777 11613132053109683570083)
              ·
                refine ⟨17419698079664525355125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11613132053109683570083 17419698079664525355125)
                ·
                  refine ⟨1633096694968549252043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17419698079664525355125 1633096694968549252043)
                  ·
                    rfl

theorem cell21_7156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_7156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_7156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_7156 prefixEnd_7156 := by exact prefixLift 7156
  have htrace : WordTrace (prefixWord ++ tailWord_7156) baseStart_7156 baseEnd_7156 := by
    simpa [prefixWord, tailWord_7156, baseEnd_7156] using wordTrace_append hprefix tailTrace_7156
  have hstable : (prefixWord ++ tailWord_7156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7156).length < 2 ^ (prefixWord ++ tailWord_7156).sum := by decide
  have hdescent : baseEnd_7156 < baseStart_7156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7164 : List Nat := [2, 2, 2, 1, 2, 4, 2, 1, 5]
def baseStart_7164 : Nat := 118140960795 + 7164 * 2 ^ 59
def prefixEnd_7164 : Nat := 4983230072969 + 3 ^ 40 * 7164 * 2
def baseEnd_7164 : Nat := 1634922403962313118693

theorem tailTrace_7164 : CollatzResearch.WordTrace tailWord_7164 prefixEnd_7164 1634922403962313118693 := by
  unfold tailWord_7164
  simp only [CollatzResearch.WordTrace]
  refine ⟨130646273026763179450273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174195030702350905933697 130646273026763179450273)
  ·
    refine ⟨97984704770072384587705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130646273026763179450273 97984704770072384587705)
    ·
      refine ⟨73488528577554288440779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97984704770072384587705 73488528577554288440779)
      ·
        refine ⟨110232792866331432661169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73488528577554288440779 110232792866331432661169)
        ·
          refine ⟨82674594649748574495877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110232792866331432661169 82674594649748574495877)
          ·
            refine ⟨15501486496827857717977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82674594649748574495877 15501486496827857717977)
            ·
              refine ⟨11626114872620893288483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15501486496827857717977 11626114872620893288483)
              ·
                refine ⟨17439172308931339932725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11626114872620893288483 17439172308931339932725)
                ·
                  refine ⟨1634922403962313118693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17439172308931339932725 1634922403962313118693)
                  ·
                    rfl

theorem cell21_7164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_7164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_7164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_7164 prefixEnd_7164 := by exact prefixLift 7164
  have htrace : WordTrace (prefixWord ++ tailWord_7164) baseStart_7164 baseEnd_7164 := by
    simpa [prefixWord, tailWord_7164, baseEnd_7164] using wordTrace_append hprefix tailTrace_7164
  have hstable : (prefixWord ++ tailWord_7164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7164).length < 2 ^ (prefixWord ++ tailWord_7164).sum := by decide
  have hdescent : baseEnd_7164 < baseStart_7164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7170 : List Nat := [3, 4, 1, 3, 1, 1, 3, 1, 4]
def baseStart_7170 : Nat := 118140960795 + 7170 * 2 ^ 59
def prefixEnd_7170 : Nat := 4983230072969 + 3 ^ 40 * 7170 * 2
def baseEnd_7170 : Nat := 1636291685707636018681

theorem tailTrace_7170 : CollatzResearch.WordTrace tailWord_7170 prefixEnd_7170 1636291685707636018681 := by
  unfold tailWord_7170
  simp only [CollatzResearch.WordTrace]
  refine ⟨65377846007947345904741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174340922687859589079309 65377846007947345904741)
  ·
    refine ⟨12258346126490127357139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65377846007947345904741 12258346126490127357139)
    ·
      refine ⟨18387519189735191035709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12258346126490127357139 18387519189735191035709)
      ·
        refine ⟨6895319696150696638391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18387519189735191035709 6895319696150696638391)
        ·
          refine ⟨10342979544226044957587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6895319696150696638391 10342979544226044957587)
          ·
            refine ⟨15514469316339067436381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10342979544226044957587 15514469316339067436381)
            ·
              refine ⟨5817925993627150288643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15514469316339067436381 5817925993627150288643)
              ·
                refine ⟨8726888990440725432965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5817925993627150288643 8726888990440725432965)
                ·
                  refine ⟨1636291685707636018681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8726888990440725432965 1636291685707636018681)
                  ·
                    rfl

theorem cell21_7170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_7170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_7170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_7170 prefixEnd_7170 := by exact prefixLift 7170
  have htrace : WordTrace (prefixWord ++ tailWord_7170) baseStart_7170 baseEnd_7170 := by
    simpa [prefixWord, tailWord_7170, baseEnd_7170] using wordTrace_append hprefix tailTrace_7170
  have hstable : (prefixWord ++ tailWord_7170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7170).length < 2 ^ (prefixWord ++ tailWord_7170).sum := by decide
  have hdescent : baseEnd_7170 < baseStart_7170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271 : List Nat := [1, 1, 5, 1, 1, 4, 2, 2, 4]
def baseStart_7271 : Nat := 118140960795 + 7271 * 2 ^ 59
def prefixEnd_7271 : Nat := 4983230072969 + 3 ^ 40 * 7271 * 2
def baseEnd_7271 : Nat := 1659341261753904835141

theorem tailTrace_7271 : CollatzResearch.WordTrace tailWord_7271 prefixEnd_7271 1659341261753904835141 := by
  unfold tailWord_7271
  simp only [CollatzResearch.WordTrace]
  refine ⟨265195156665883633045667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176796771110589088697111 265195156665883633045667)
  ·
    refine ⟨397792734998825449568501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265195156665883633045667 397792734998825449568501)
    ·
      refine ⟨37293068906139885897047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 397792734998825449568501 37293068906139885897047)
      ·
        refine ⟨55939603359209828845571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37293068906139885897047 55939603359209828845571)
        ·
          refine ⟨83909405038814743268357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55939603359209828845571 83909405038814743268357)
          ·
            refine ⟨15733013444777764362817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83909405038814743268357 15733013444777764362817)
            ·
              refine ⟨11799760083583323272113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15733013444777764362817 11799760083583323272113)
              ·
                refine ⟨8849820062687492454085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11799760083583323272113 8849820062687492454085)
                ·
                  refine ⟨1659341261753904835141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8849820062687492454085 1659341261753904835141)
                  ·
                    rfl

theorem cell21_7271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 4].length) (baseStart_7271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_7271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_7271 prefixEnd_7271 := by exact prefixLift 7271
  have htrace : WordTrace (prefixWord ++ tailWord_7271) baseStart_7271 baseEnd_7271 := by
    simpa [prefixWord, tailWord_7271, baseEnd_7271] using wordTrace_append hprefix tailTrace_7271
  have hstable : (prefixWord ++ tailWord_7271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271).length < 2 ^ (prefixWord ++ tailWord_7271).sum := by decide
  have hdescent : baseEnd_7271 < baseStart_7271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274 : List Nat := [3, 1, 3, 2, 2, 1, 4, 2, 3]
def baseStart_7274 : Nat := 118140960795 + 7274 * 2 ^ 59
def prefixEnd_7274 : Nat := 4983230072969 + 3 ^ 40 * 7274 * 2
def baseEnd_7274 : Nat := 1660025902626566285135

theorem tailTrace_7274 : CollatzResearch.WordTrace tailWord_7274 prefixEnd_7274 1660025902626566285135 := by
  unfold tailWord_7274
  simp only [CollatzResearch.WordTrace]
  refine ⟨66326143913753786351219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176869717103343430269917 66326143913753786351219)
  ·
    refine ⟨99489215870630679526829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66326143913753786351219 99489215870630679526829)
    ·
      refine ⟨37308455951486504822561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99489215870630679526829 37308455951486504822561)
      ·
        refine ⟨27981341963614878616921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37308455951486504822561 27981341963614878616921)
        ·
          refine ⟨20986006472711158962691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27981341963614878616921 20986006472711158962691)
          ·
            refine ⟨31479009709066738444037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20986006472711158962691 31479009709066738444037)
            ·
              refine ⟨5902314320450013458257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31479009709066738444037 5902314320450013458257)
              ·
                refine ⟨4426735740337510093693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5902314320450013458257 4426735740337510093693)
                ·
                  refine ⟨1660025902626566285135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4426735740337510093693 1660025902626566285135)
                  ·
                    rfl

theorem cell21_7274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_7274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_7274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_7274 prefixEnd_7274 := by exact prefixLift 7274
  have htrace : WordTrace (prefixWord ++ tailWord_7274) baseStart_7274 baseEnd_7274 := by
    simpa [prefixWord, tailWord_7274, baseEnd_7274] using wordTrace_append hprefix tailTrace_7274
  have hstable : (prefixWord ++ tailWord_7274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274).length < 2 ^ (prefixWord ++ tailWord_7274).sum := by decide
  have hdescent : baseEnd_7274 < baseStart_7274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7299 : List Nat := [1, 1, 1, 3, 3, 2, 3, 2, 5]
def baseStart_7299 : Nat := 118140960795 + 7299 * 2 ^ 59
def prefixEnd_7299 : Nat := 4983230072969 + 3 ^ 40 * 7299 * 2
def baseEnd_7299 : Nat := 1665731243232078368417

theorem tailTrace_7299 : CollatzResearch.WordTrace tailWord_7299 prefixEnd_7299 1665731243232078368417 := by
  unfold tailWord_7299
  simp only [CollatzResearch.WordTrace]
  refine ⟨266216400564444415064951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177477600376296276709967 266216400564444415064951)
  ·
    refine ⟨399324600846666622597427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266216400564444415064951 399324600846666622597427)
    ·
      refine ⟨598986901269999933896141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399324600846666622597427 598986901269999933896141)
      ·
        refine ⟨224620087976249975211053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 598986901269999933896141 224620087976249975211053)
        ·
          refine ⟨84232532991093740704145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224620087976249975211053 84232532991093740704145)
          ·
            refine ⟨63174399743320305528109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84232532991093740704145 63174399743320305528109)
            ·
              refine ⟨23690399903745114573041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63174399743320305528109 23690399903745114573041)
              ·
                refine ⟨17767799927808835929781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23690399903745114573041 17767799927808835929781)
                ·
                  refine ⟨1665731243232078368417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17767799927808835929781 1665731243232078368417)
                  ·
                    rfl

theorem cell21_7299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 5].length) (baseStart_7299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_7299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_7299 prefixEnd_7299 := by exact prefixLift 7299
  have htrace : WordTrace (prefixWord ++ tailWord_7299) baseStart_7299 baseEnd_7299 := by
    simpa [prefixWord, tailWord_7299, baseEnd_7299] using wordTrace_append hprefix tailTrace_7299
  have hstable : (prefixWord ++ tailWord_7299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7299).length < 2 ^ (prefixWord ++ tailWord_7299).sum := by decide
  have hdescent : baseEnd_7299 < baseStart_7299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392 : List Nat := [2, 1, 1, 3, 1, 6, 1, 1, 5]
def baseStart_7392 : Nat := 118140960795 + 7392 * 2 ^ 59
def prefixEnd_7392 : Nat := 4983230072969 + 3 ^ 40 * 7392 * 2
def baseEnd_7392 : Nat := 1686955110284583318227

theorem tailTrace_7392 : CollatzResearch.WordTrace tailWord_7392 prefixEnd_7392 1686955110284583318227 := by
  unfold tailWord_7392
  simp only [CollatzResearch.WordTrace]
  refine ⟨134804194613760649100215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179738926151680865466953 134804194613760649100215)
  ·
    refine ⟨202206291920640973650323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134804194613760649100215 202206291920640973650323)
    ·
      refine ⟨303309437880961460475485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202206291920640973650323 303309437880961460475485)
      ·
        refine ⟨113741039205360547678307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303309437880961460475485 113741039205360547678307)
        ·
          refine ⟨170611558808040821517461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113741039205360547678307 170611558808040821517461)
          ·
            refine ⟨7997416819126913508631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 170611558808040821517461 7997416819126913508631)
            ·
              refine ⟨11996125228690370262947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7997416819126913508631 11996125228690370262947)
              ·
                refine ⟨17994187843035555394421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11996125228690370262947 17994187843035555394421)
                ·
                  refine ⟨1686955110284583318227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17994187843035555394421 1686955110284583318227)
                  ·
                    rfl

theorem cell21_7392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 5].length) (baseStart_7392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_7392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_7392 prefixEnd_7392 := by exact prefixLift 7392
  have htrace : WordTrace (prefixWord ++ tailWord_7392) baseStart_7392 baseEnd_7392 := by
    simpa [prefixWord, tailWord_7392, baseEnd_7392] using wordTrace_append hprefix tailTrace_7392
  have hstable : (prefixWord ++ tailWord_7392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392).length < 2 ^ (prefixWord ++ tailWord_7392).sum := by decide
  have hdescent : baseEnd_7392 < baseStart_7392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7561 : List Nat := [1, 2, 1, 1, 8, 1, 1, 1, 5]
def baseStart_7561 : Nat := 118140960795 + 7561 * 2 ^ 59
def prefixEnd_7561 : Nat := 4983230072969 + 3 ^ 40 * 7561 * 2
def baseEnd_7561 : Nat := 1725523212777845001215

theorem tailTrace_7561 : CollatzResearch.WordTrace tailWord_7561 prefixEnd_7561 1725523212777845001215 := by
  unfold tailWord_7561
  simp only [CollatzResearch.WordTrace]
  refine ⟨275772325615263161102537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183848217076842107401691 275772325615263161102537)
  ·
    refine ⟨206829244211447370826903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275772325615263161102537 206829244211447370826903)
    ·
      refine ⟨310243866317171056240355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206829244211447370826903 310243866317171056240355)
      ·
        refine ⟨465365799475756584360533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310243866317171056240355 465365799475756584360533)
        ·
          refine ⟨5453505462606522472975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 465365799475756584360533 5453505462606522472975)
          ·
            refine ⟨8180258193909783709463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5453505462606522472975 8180258193909783709463)
            ·
              refine ⟨12270387290864675564195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8180258193909783709463 12270387290864675564195)
              ·
                refine ⟨18405580936297013346293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12270387290864675564195 18405580936297013346293)
                ·
                  refine ⟨1725523212777845001215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18405580936297013346293 1725523212777845001215)
                  ·
                    rfl

theorem cell21_7561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 5].length) (baseStart_7561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_7561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_7561 prefixEnd_7561 := by exact prefixLift 7561
  have htrace : WordTrace (prefixWord ++ tailWord_7561) baseStart_7561 baseEnd_7561 := by
    simpa [prefixWord, tailWord_7561, baseEnd_7561] using wordTrace_append hprefix tailTrace_7561
  have hstable : (prefixWord ++ tailWord_7561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7561).length < 2 ^ (prefixWord ++ tailWord_7561).sum := by decide
  have hdescent : baseEnd_7561 < baseStart_7561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7713 : List Nat := [1, 2, 3, 2, 2, 4, 1, 3, 3]
def baseStart_7713 : Nat := 118140960795 + 7713 * 2 ^ 59
def prefixEnd_7713 : Nat := 4983230072969 + 3 ^ 40 * 7713 * 2
def baseEnd_7713 : Nat := 1760211683659358467571

theorem tailTrace_7713 : CollatzResearch.WordTrace tailWord_7713 prefixEnd_7713 1760211683659358467571 := by
  unfold tailWord_7713
  simp only [CollatzResearch.WordTrace]
  refine ⟨281316221064593120635793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187544147376395413757195 281316221064593120635793)
  ·
    refine ⟨210987165798444840476845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281316221064593120635793 210987165798444840476845)
    ·
      refine ⟨79120187174416815178817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210987165798444840476845 79120187174416815178817)
      ·
        refine ⟨59340140380812611384113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79120187174416815178817 59340140380812611384113)
        ·
          refine ⟨44505105285609458538085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59340140380812611384113 44505105285609458538085)
          ·
            refine ⟨8344707241051773475891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44505105285609458538085 8344707241051773475891)
            ·
              refine ⟨12517060861577660213837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8344707241051773475891 12517060861577660213837)
              ·
                refine ⟨4693897823091622580189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12517060861577660213837 4693897823091622580189)
                ·
                  refine ⟨1760211683659358467571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4693897823091622580189 1760211683659358467571)
                  ·
                    rfl

theorem cell21_7713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 3].length) (baseStart_7713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_7713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_7713 prefixEnd_7713 := by exact prefixLift 7713
  have htrace : WordTrace (prefixWord ++ tailWord_7713) baseStart_7713 baseEnd_7713 := by
    simpa [prefixWord, tailWord_7713, baseEnd_7713] using wordTrace_append hprefix tailTrace_7713
  have hstable : (prefixWord ++ tailWord_7713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7713).length < 2 ^ (prefixWord ++ tailWord_7713).sum := by decide
  have hdescent : baseEnd_7713 < baseStart_7713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741 : List Nat := [1, 4, 1, 3, 3, 1, 2, 6]
def baseStart_7741 : Nat := 118140960795 + 7741 * 2 ^ 59
def prefixEnd_7741 : Nat := 4983230072969 + 3 ^ 40 * 7741 * 2
def baseEnd_7741 : Nat := 588867221712510666949

theorem tailTrace_7741 : CollatzResearch.WordTrace tailWord_7741 prefixEnd_7741 588867221712510666949 := by
  unfold tailWord_7741
  simp only [CollatzResearch.WordTrace]
  refine ⟨282337464963153902655077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188224976642102601770051 282337464963153902655077)
  ·
    refine ⟨52938274680591356747827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282337464963153902655077 52938274680591356747827)
    ·
      refine ⟨79407412020887035121741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52938274680591356747827 79407412020887035121741)
      ·
        refine ⟨29777779507832638170653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79407412020887035121741 29777779507832638170653)
        ·
          refine ⟨11166667315437239313995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29777779507832638170653 11166667315437239313995)
          ·
            refine ⟨16750000973155858970993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11166667315437239313995 16750000973155858970993)
            ·
              refine ⟨12562500729866894228245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16750000973155858970993 12562500729866894228245)
              ·
                refine ⟨588867221712510666949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12562500729866894228245 588867221712510666949)
                ·
                  rfl

theorem cell21_7741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 6].length) (baseStart_7741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_7741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_7741 prefixEnd_7741 := by exact prefixLift 7741
  have htrace : WordTrace (prefixWord ++ tailWord_7741) baseStart_7741 baseEnd_7741 := by
    simpa [prefixWord, tailWord_7741, baseEnd_7741] using wordTrace_append hprefix tailTrace_7741
  have hstable : (prefixWord ++ tailWord_7741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741).length < 2 ^ (prefixWord ++ tailWord_7741).sum := by decide
  have hdescent : baseEnd_7741 < baseStart_7741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786 : List Nat := [3, 1, 3, 2, 1, 2, 1, 4, 4]
def baseStart_7786 : Nat := 118140960795 + 7786 * 2 ^ 59
def prefixEnd_7786 : Nat := 4983230072969 + 3 ^ 40 * 7786 * 2
def baseEnd_7786 : Nat := 1776871278227453750755

theorem tailTrace_7786 : CollatzResearch.WordTrace tailWord_7786 prefixEnd_7786 1776871278227453750755 := by
  unfold tailWord_7786
  simp only [CollatzResearch.WordTrace]
  refine ⟨70994687450031647010803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189319166533417725362141 70994687450031647010803)
  ·
    refine ⟨106492031175047470516205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70994687450031647010803 106492031175047470516205)
    ·
      refine ⟨39934511690642801443577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106492031175047470516205 39934511690642801443577)
      ·
        refine ⟨29950883767982101082683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39934511690642801443577 29950883767982101082683)
        ·
          refine ⟨44926325651973151624025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29950883767982101082683 44926325651973151624025)
          ·
            refine ⟨33694744238979863718019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44926325651973151624025 33694744238979863718019)
            ·
              refine ⟨50542116358469795577029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33694744238979863718019 50542116358469795577029)
              ·
                refine ⟨9476646817213086670693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50542116358469795577029 9476646817213086670693)
                ·
                  refine ⟨1776871278227453750755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9476646817213086670693 1776871278227453750755)
                  ·
                    rfl

theorem cell21_7786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_7786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_7786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_7786 prefixEnd_7786 := by exact prefixLift 7786
  have htrace : WordTrace (prefixWord ++ tailWord_7786) baseStart_7786 baseEnd_7786 := by
    simpa [prefixWord, tailWord_7786, baseEnd_7786] using wordTrace_append hprefix tailTrace_7786
  have hstable : (prefixWord ++ tailWord_7786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786).length < 2 ^ (prefixWord ++ tailWord_7786).sum := by decide
  have hdescent : baseEnd_7786 < baseStart_7786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7789 : List Nat := [1, 5, 1, 1, 4, 1, 1, 4, 3]
def baseStart_7789 : Nat := 118140960795 + 7789 * 2 ^ 59
def prefixEnd_7789 : Nat := 4983230072969 + 3 ^ 40 * 7789 * 2
def baseEnd_7789 : Nat := 1777555919100115200749

theorem tailTrace_7789 : CollatzResearch.WordTrace tailWord_7789 prefixEnd_7789 1777555919100115200749 := by
  unfold tailWord_7789
  simp only [CollatzResearch.WordTrace]
  refine ⟨284088168789258100402421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189392112526172066934947 284088168789258100402421)
  ·
    refine ⟨26633265823992946912727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 284088168789258100402421 26633265823992946912727)
    ·
      refine ⟨39949898735989420369091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26633265823992946912727 39949898735989420369091)
      ·
        refine ⟨59924848103984130553637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39949898735989420369091 59924848103984130553637)
        ·
          refine ⟨11235909019497024478807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59924848103984130553637 11235909019497024478807)
          ·
            refine ⟨16853863529245536718211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11235909019497024478807 16853863529245536718211)
            ·
              refine ⟨25280795293868305077317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16853863529245536718211 25280795293868305077317)
              ·
                refine ⟨4740149117600307201997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25280795293868305077317 4740149117600307201997)
                ·
                  refine ⟨1777555919100115200749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4740149117600307201997 1777555919100115200749)
                  ·
                    rfl

theorem cell21_7789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_7789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_7789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_7789 prefixEnd_7789 := by exact prefixLift 7789
  have htrace : WordTrace (prefixWord ++ tailWord_7789) baseStart_7789 baseEnd_7789 := by
    simpa [prefixWord, tailWord_7789, baseEnd_7789] using wordTrace_append hprefix tailTrace_7789
  have hstable : (prefixWord ++ tailWord_7789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7789).length < 2 ^ (prefixWord ++ tailWord_7789).sum := by decide
  have hdescent : baseEnd_7789 < baseStart_7789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859 : List Nat := [1, 1, 1, 2, 3, 3, 2, 8]
def baseStart_7859 : Nat := 118140960795 + 7859 * 2 ^ 59
def prefixEnd_7859 : Nat := 4983230072969 + 3 ^ 40 * 7859 * 2
def baseEnd_7859 : Nat := 597843624265183011313

theorem tailTrace_7859 : CollatzResearch.WordTrace tailWord_7859 prefixEnd_7859 597843624265183011313 := by
  unfold tailWord_7859
  simp only [CollatzResearch.WordTrace]
  refine ⟨286641278535660055450631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191094185690440036967087 286641278535660055450631)
  ·
    refine ⟨429961917803490083175947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286641278535660055450631 429961917803490083175947)
    ·
      refine ⟨644942876705235124763921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429961917803490083175947 644942876705235124763921)
      ·
        refine ⟨483707157528926343572941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 644942876705235124763921 483707157528926343572941)
        ·
          refine ⟨181390184073347378839853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 483707157528926343572941 181390184073347378839853)
          ·
            refine ⟨68021319027505267064945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181390184073347378839853 68021319027505267064945)
            ·
              refine ⟨51015989270628950298709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68021319027505267064945 51015989270628950298709)
              ·
                refine ⟨597843624265183011313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 51015989270628950298709 597843624265183011313)
                ·
                  rfl

theorem cell21_7859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 8].length) (baseStart_7859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_7859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_7859 prefixEnd_7859 := by exact prefixLift 7859
  have htrace : WordTrace (prefixWord ++ tailWord_7859) baseStart_7859 baseEnd_7859 := by
    simpa [prefixWord, tailWord_7859, baseEnd_7859] using wordTrace_append hprefix tailTrace_7859
  have hstable : (prefixWord ++ tailWord_7859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859).length < 2 ^ (prefixWord ++ tailWord_7859).sum := by decide
  have hdescent : baseEnd_7859 < baseStart_7859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7876 : List Nat := [2, 3, 3, 1, 1, 1, 3, 7]
def baseStart_7876 : Nat := 118140960795 + 7876 * 2 ^ 59
def prefixEnd_7876 : Nat := 4983230072969 + 3 ^ 40 * 7876 * 2
def baseEnd_7876 : Nat := 599136834802432416857

theorem tailTrace_7876 : CollatzResearch.WordTrace tailWord_7876 prefixEnd_7876 599136834802432416857 := by
  unfold tailWord_7876
  simp only [CollatzResearch.WordTrace]
  refine ⟨143630659737035979409741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191507546316047972546321 143630659737035979409741)
  ·
    refine ⟨53861497401388492278653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143630659737035979409741 53861497401388492278653)
    ·
      refine ⟨20198061525520684604495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53861497401388492278653 20198061525520684604495)
      ·
        refine ⟨30297092288281026906743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20198061525520684604495 30297092288281026906743)
        ·
          refine ⟨45445638432421540360115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30297092288281026906743 45445638432421540360115)
          ·
            refine ⟨68168457648632310540173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45445638432421540360115 68168457648632310540173)
            ·
              refine ⟨25563171618237116452565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68168457648632310540173 25563171618237116452565)
              ·
                refine ⟨599136834802432416857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25563171618237116452565 599136834802432416857)
                ·
                  rfl

theorem cell21_7876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 7].length) (baseStart_7876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_7876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_7876 prefixEnd_7876 := by exact prefixLift 7876
  have htrace : WordTrace (prefixWord ++ tailWord_7876) baseStart_7876 baseEnd_7876 := by
    simpa [prefixWord, tailWord_7876, baseEnd_7876] using wordTrace_append hprefix tailTrace_7876
  have hstable : (prefixWord ++ tailWord_7876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7876).length < 2 ^ (prefixWord ++ tailWord_7876).sum := by decide
  have hdescent : baseEnd_7876 < baseStart_7876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7882 : List Nat := [3, 1, 2, 1, 6, 1, 1, 3, 3]
def baseStart_7882 : Nat := 118140960795 + 7882 * 2 ^ 59
def prefixEnd_7882 : Nat := 4983230072969 + 3 ^ 40 * 7882 * 2
def baseEnd_7882 : Nat := 1798779786152620150559

theorem tailTrace_7882 : CollatzResearch.WordTrace tailWord_7882 prefixEnd_7882 1798779786152620150559 := by
  unfold tailWord_7882
  simp only [CollatzResearch.WordTrace]
  refine ⟨71870039363083745884475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191653438301556655691933 71870039363083745884475)
  ·
    refine ⟨107805059044625618826713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71870039363083745884475 107805059044625618826713)
    ·
      refine ⟨80853794283469214120035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107805059044625618826713 80853794283469214120035)
      ·
        refine ⟨121280691425203821180053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80853794283469214120035 121280691425203821180053)
        ·
          refine ⟨5685032410556429117815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121280691425203821180053 5685032410556429117815)
          ·
            refine ⟨8527548615834643676723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5685032410556429117815 8527548615834643676723)
            ·
              refine ⟨12791322923751965515085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8527548615834643676723 12791322923751965515085)
              ·
                refine ⟨4796746096406987068157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12791322923751965515085 4796746096406987068157)
                ·
                  refine ⟨1798779786152620150559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4796746096406987068157 1798779786152620150559)
                  ·
                    rfl

theorem cell21_7882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_7882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_7882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_7882 prefixEnd_7882 := by exact prefixLift 7882
  have htrace : WordTrace (prefixWord ++ tailWord_7882) baseStart_7882 baseEnd_7882 := by
    simpa [prefixWord, tailWord_7882, baseEnd_7882] using wordTrace_append hprefix tailTrace_7882
  have hstable : (prefixWord ++ tailWord_7882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7882).length < 2 ^ (prefixWord ++ tailWord_7882).sum := by decide
  have hdescent : baseEnd_7882 < baseStart_7882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7935 : List Nat := [1, 1, 2, 2, 1, 3, 4, 7]
def baseStart_7935 : Nat := 118140960795 + 7935 * 2 ^ 59
def prefixEnd_7935 : Nat := 4983230072969 + 3 ^ 40 * 7935 * 2
def baseEnd_7935 : Nat := 603625036078768589039

theorem tailTrace_7935 : CollatzResearch.WordTrace tailWord_7935 prefixEnd_7935 603625036078768589039 := by
  unfold tailWord_7935
  simp only [CollatzResearch.WordTrace]
  refine ⟨289413226260325035217259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192942150840216690144839 289413226260325035217259)
  ·
    refine ⟨434119839390487552825889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289413226260325035217259 434119839390487552825889)
    ·
      refine ⟨325589879542865664619417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434119839390487552825889 325589879542865664619417)
      ·
        refine ⟨244192409657149248464563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325589879542865664619417 244192409657149248464563)
        ·
          refine ⟨366288614485723872696845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244192409657149248464563 366288614485723872696845)
          ·
            refine ⟨137358230432146452261317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366288614485723872696845 137358230432146452261317)
            ·
              refine ⟨25754668206027459798997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137358230432146452261317 25754668206027459798997)
              ·
                refine ⟨603625036078768589039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25754668206027459798997 603625036078768589039)
                ·
                  rfl

theorem cell21_7935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 7].length) (baseStart_7935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_7935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_7935 prefixEnd_7935 := by exact prefixLift 7935
  have htrace : WordTrace (prefixWord ++ tailWord_7935) baseStart_7935 baseEnd_7935 := by
    simpa [prefixWord, tailWord_7935, baseEnd_7935] using wordTrace_append hprefix tailTrace_7935
  have hstable : (prefixWord ++ tailWord_7935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7935).length < 2 ^ (prefixWord ++ tailWord_7935).sum := by decide
  have hdescent : baseEnd_7935 < baseStart_7935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073 : List Nat := [1, 2, 1, 1, 5, 1, 2, 4, 4]
def baseStart_8073 : Nat := 118140960795 + 8073 * 2 ^ 59
def prefixEnd_8073 : Nat := 4983230072969 + 3 ^ 40 * 8073 * 2
def baseEnd_8073 : Nat := 1842368588378732466835

theorem tailTrace_8073 : CollatzResearch.WordTrace tailWord_8073 prefixEnd_8073 1842368588378732466835 := by
  unfold tailWord_8073
  simp only [CollatzResearch.WordTrace]
  refine ⟨294446499760374603740873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196297666506916402493915 294446499760374603740873)
  ·
    refine ⟨220834874820280952805655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294446499760374603740873 220834874820280952805655)
    ·
      refine ⟨331252312230421429208483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220834874820280952805655 331252312230421429208483)
      ·
        refine ⟨496878468345632143812725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331252312230421429208483 496878468345632143812725)
        ·
          refine ⟨46582356407403013482443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 496878468345632143812725 46582356407403013482443)
          ·
            refine ⟨69873534611104520223665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46582356407403013482443 69873534611104520223665)
            ·
              refine ⟨52405150958328390167749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69873534611104520223665 52405150958328390167749)
              ·
                refine ⟨9825965804686573156453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52405150958328390167749 9825965804686573156453)
                ·
                  refine ⟨1842368588378732466835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9825965804686573156453 1842368588378732466835)
                  ·
                    rfl

theorem cell21_8073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_8073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_8073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_8073 prefixEnd_8073 := by exact prefixLift 8073
  have htrace : WordTrace (prefixWord ++ tailWord_8073) baseStart_8073 baseEnd_8073 := by
    simpa [prefixWord, tailWord_8073, baseEnd_8073] using wordTrace_append hprefix tailTrace_8073
  have hstable : (prefixWord ++ tailWord_8073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073).length < 2 ^ (prefixWord ++ tailWord_8073).sum := by decide
  have hdescent : baseEnd_8073 < baseStart_8073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8087 : List Nat := [1, 1, 3, 3, 1, 3, 1, 8]
def baseStart_8087 : Nat := 118140960795 + 8087 * 2 ^ 59
def prefixEnd_8087 : Nat := 4983230072969 + 3 ^ 40 * 8087 * 2
def baseEnd_8087 : Nat := 615187859705939744491

theorem tailTrace_8087 : CollatzResearch.WordTrace tailWord_8087 prefixEnd_8087 615187859705939744491 := by
  unfold tailWord_8087
  simp only [CollatzResearch.WordTrace]
  refine ⟨294957121709654994750515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196638081139769996500343 294957121709654994750515)
  ·
    refine ⟨442435682564482492125773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294957121709654994750515 442435682564482492125773)
    ·
      refine ⟨165913380961680934547165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442435682564482492125773 165913380961680934547165)
      ·
        refine ⟨62217517860630350455187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165913380961680934547165 62217517860630350455187)
        ·
          refine ⟨93326276790945525682781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62217517860630350455187 93326276790945525682781)
          ·
            refine ⟨34997353796604572131043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93326276790945525682781 34997353796604572131043)
            ·
              refine ⟨52496030694906858196565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34997353796604572131043 52496030694906858196565)
              ·
                refine ⟨615187859705939744491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 52496030694906858196565 615187859705939744491)
                ·
                  rfl

theorem cell21_8087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 8].length) (baseStart_8087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_8087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_8087 prefixEnd_8087 := by exact prefixLift 8087
  have htrace : WordTrace (prefixWord ++ tailWord_8087) baseStart_8087 baseEnd_8087 := by
    simpa [prefixWord, tailWord_8087, baseEnd_8087] using wordTrace_append hprefix tailTrace_8087
  have hstable : (prefixWord ++ tailWord_8087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8087).length < 2 ^ (prefixWord ++ tailWord_8087).sum := by decide
  have hdescent : baseEnd_8087 < baseStart_8087 := by decide
  rcases family_descends (prefixWord ++ tailWord_8087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8090 : List Nat := [3, 1, 1, 4, 2, 2, 1, 3, 4]
def baseStart_8090 : Nat := 118140960795 + 8090 * 2 ^ 59
def prefixEnd_8090 : Nat := 4983230072969 + 3 ^ 40 * 8090 * 2
def baseEnd_8090 : Nat := 1846248219990480683467

theorem tailTrace_8090 : CollatzResearch.WordTrace tailWord_8090 prefixEnd_8090 1846248219990480683467 := by
  unfold tailWord_8090
  simp only [CollatzResearch.WordTrace]
  refine ⟨73766635174696626777431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196711027132524338073149 73766635174696626777431)
  ·
    refine ⟨110649952762044940166147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73766635174696626777431 110649952762044940166147)
    ·
      refine ⟨165974929143067410249221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110649952762044940166147 165974929143067410249221)
      ·
        refine ⟨31120299214325139421729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165974929143067410249221 31120299214325139421729)
        ·
          refine ⟨23340224410743854566297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31120299214325139421729 23340224410743854566297)
          ·
            refine ⟨17505168308057890924723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23340224410743854566297 17505168308057890924723)
            ·
              refine ⟨26257752462086836387085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17505168308057890924723 26257752462086836387085)
              ·
                refine ⟨9846657173282563645157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26257752462086836387085 9846657173282563645157)
                ·
                  refine ⟨1846248219990480683467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9846657173282563645157 1846248219990480683467)
                  ·
                    rfl

theorem cell21_8090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_8090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_8090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_8090 prefixEnd_8090 := by exact prefixLift 8090
  have htrace : WordTrace (prefixWord ++ tailWord_8090) baseStart_8090 baseEnd_8090 := by
    simpa [prefixWord, tailWord_8090, baseEnd_8090] using wordTrace_append hprefix tailTrace_8090
  have hstable : (prefixWord ++ tailWord_8090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8090).length < 2 ^ (prefixWord ++ tailWord_8090).sum := by decide
  have hdescent : baseEnd_8090 < baseStart_8090 := by decide
  rcases family_descends (prefixWord ++ tailWord_8090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304 : List Nat := [2, 1, 1, 1, 5, 2, 4, 2, 3]
def baseStart_8304 : Nat := 118140960795 + 8304 * 2 ^ 59
def prefixEnd_8304 : Nat := 4983230072969 + 3 ^ 40 * 8304 * 2
def baseEnd_8304 : Nat := 1895085935573664116363

theorem tailTrace_8304 : CollatzResearch.WordTrace tailWord_8304 prefixEnd_8304 1895085935573664116363 := by
  unfold tailWord_8304
  simp only [CollatzResearch.WordTrace]
  refine ⟨151435880961750527699983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201914507949000703599977 151435880961750527699983)
  ·
    refine ⟨227153821442625791549975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151435880961750527699983 227153821442625791549975)
    ·
      refine ⟨340730732163938687324963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227153821442625791549975 340730732163938687324963)
      ·
        refine ⟨511096098245908030987445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340730732163938687324963 511096098245908030987445)
        ·
          refine ⟨47915259210553877905073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 511096098245908030987445 47915259210553877905073)
          ·
            refine ⟨35936444407915408428805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47915259210553877905073 35936444407915408428805)
            ·
              refine ⟨6738083326484139080401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35936444407915408428805 6738083326484139080401)
              ·
                refine ⟨5053562494863104310301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6738083326484139080401 5053562494863104310301)
                ·
                  refine ⟨1895085935573664116363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5053562494863104310301 1895085935573664116363)
                  ·
                    rfl

theorem cell21_8304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 3].length) (baseStart_8304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_8304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_8304 prefixEnd_8304 := by exact prefixLift 8304
  have htrace : WordTrace (prefixWord ++ tailWord_8304) baseStart_8304 baseEnd_8304 := by
    simpa [prefixWord, tailWord_8304, baseEnd_8304] using wordTrace_append hprefix tailTrace_8304
  have hstable : (prefixWord ++ tailWord_8304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304).length < 2 ^ (prefixWord ++ tailWord_8304).sum := by decide
  have hdescent : baseEnd_8304 < baseStart_8304 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8484 : List Nat := [2, 3, 1, 3, 1, 4, 1, 6]
def baseStart_8484 : Nat := 118140960795 + 8484 * 2 ^ 59
def prefixEnd_8484 : Nat := 4983230072969 + 3 ^ 40 * 8484 * 2
def baseEnd_8484 : Nat := 645388129311117038665

theorem tailTrace_8484 : CollatzResearch.WordTrace tailWord_8484 prefixEnd_8484 645388129311117038665 := by
  unfold tailWord_8484
  simp only [CollatzResearch.WordTrace]
  refine ⟨154718450635695898476253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 206291267514261197968337 154718450635695898476253)
  ·
    refine ⟨58019418988385961928595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154718450635695898476253 58019418988385961928595)
    ·
      refine ⟨87029128482578942892893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58019418988385961928595 87029128482578942892893)
      ·
        refine ⟨32635923180967103584835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87029128482578942892893 32635923180967103584835)
        ·
          refine ⟨48953884771450655377253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32635923180967103584835 48953884771450655377253)
          ·
            refine ⟨9178853394646997883235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48953884771450655377253 9178853394646997883235)
            ·
              refine ⟨13768280091970496824853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9178853394646997883235 13768280091970496824853)
              ·
                refine ⟨645388129311117038665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13768280091970496824853 645388129311117038665)
                ·
                  rfl

theorem cell21_8484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 6].length) (baseStart_8484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_8484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_8484 prefixEnd_8484 := by exact prefixLift 8484
  have htrace : WordTrace (prefixWord ++ tailWord_8484) baseStart_8484 baseEnd_8484 := by
    simpa [prefixWord, tailWord_8484, baseEnd_8484] using wordTrace_append hprefix tailTrace_8484
  have hstable : (prefixWord ++ tailWord_8484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8484).length < 2 ^ (prefixWord ++ tailWord_8484).sum := by decide
  have hdescent : baseEnd_8484 < baseStart_8484 := by decide
  rcases family_descends (prefixWord ++ tailWord_8484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8529 : List Nat := [1, 2, 2, 1, 4, 2, 3, 2, 4]
def baseStart_8529 : Nat := 118140960795 + 8529 * 2 ^ 59
def prefixEnd_8529 : Nat := 4983230072969 + 3 ^ 40 * 8529 * 2
def baseEnd_8529 : Nat := 1946434001023272865903

theorem tailTrace_8529 : CollatzResearch.WordTrace tailWord_8529 prefixEnd_8529 1946434001023272865903 := by
  unfold tailWord_8529
  simp only [CollatzResearch.WordTrace]
  refine ⟨311078186108364482340641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 207385457405576321560427 311078186108364482340641)
  ·
    refine ⟨233308639581273361755481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 311078186108364482340641 233308639581273361755481)
    ·
      refine ⟨174981479685955021316611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233308639581273361755481 174981479685955021316611)
      ·
        refine ⟨262472219528932531974917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174981479685955021316611 262472219528932531974917)
        ·
          refine ⟨49213541161674849745297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 262472219528932531974917 49213541161674849745297)
          ·
            refine ⟨36910155871256137308973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49213541161674849745297 36910155871256137308973)
            ·
              refine ⟨13841308451721051490865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36910155871256137308973 13841308451721051490865)
              ·
                refine ⟨10380981338790788618149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13841308451721051490865 10380981338790788618149)
                ·
                  refine ⟨1946434001023272865903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10380981338790788618149 1946434001023272865903)
                  ·
                    rfl

theorem cell21_8529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_8529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_8529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_8529 prefixEnd_8529 := by exact prefixLift 8529
  have htrace : WordTrace (prefixWord ++ tailWord_8529) baseStart_8529 baseEnd_8529 := by
    simpa [prefixWord, tailWord_8529, baseEnd_8529] using wordTrace_append hprefix tailTrace_8529
  have hstable : (prefixWord ++ tailWord_8529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8529).length < 2 ^ (prefixWord ++ tailWord_8529).sum := by decide
  have hdescent : baseEnd_8529 < baseStart_8529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8560 : List Nat := [2, 1, 1, 1, 4, 5, 2, 5]
def baseStart_8560 : Nat := 118140960795 + 8560 * 2 ^ 59
def prefixEnd_8560 : Nat := 4983230072969 + 3 ^ 40 * 8560 * 2
def baseEnd_8560 : Nat := 651169541124702616391

theorem tailTrace_8560 : CollatzResearch.WordTrace tailWord_8560 prefixEnd_8560 651169541124702616391 := by
  unfold tailWord_8560
  simp only [CollatzResearch.WordTrace]
  refine ⟨156104424498028388359567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 208139232664037851146089 156104424498028388359567)
  ·
    refine ⟨234156636747042582539351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156104424498028388359567 234156636747042582539351)
    ·
      refine ⟨351234955120563873809027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234156636747042582539351 351234955120563873809027)
      ·
        refine ⟨526852432680845810713541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351234955120563873809027 526852432680845810713541)
        ·
          refine ⟨98784831127658589508789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 526852432680845810713541 98784831127658589508789)
          ·
            refine ⟨9261077918217992766449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98784831127658589508789 9261077918217992766449)
            ·
              refine ⟨6945808438663494574837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9261077918217992766449 6945808438663494574837)
              ·
                refine ⟨651169541124702616391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6945808438663494574837 651169541124702616391)
                ·
                  rfl

theorem cell21_8560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 5].length) (baseStart_8560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_8560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_8560 prefixEnd_8560 := by exact prefixLift 8560
  have htrace : WordTrace (prefixWord ++ tailWord_8560) baseStart_8560 baseEnd_8560 := by
    simpa [prefixWord, tailWord_8560, baseEnd_8560] using wordTrace_append hprefix tailTrace_8560
  have hstable : (prefixWord ++ tailWord_8560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8560).length < 2 ^ (prefixWord ++ tailWord_8560).sum := by decide
  have hdescent : baseEnd_8560 < baseStart_8560 := by decide
  rcases family_descends (prefixWord ++ tailWord_8560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8566 : List Nat := [5, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_8566 : Nat := 118140960795 + 8566 * 2 ^ 59
def prefixEnd_8566 : Nat := 4983230072969 + 3 ^ 40 * 8566 * 2
def baseEnd_8566 : Nat := 1954877905119430749161

theorem tailTrace_8566 : CollatzResearch.WordTrace tailWord_8566 prefixEnd_8566 1954877905119430749161 := by
  unfold tailWord_8566
  simp only [CollatzResearch.WordTrace]
  refine ⟨19526730435894987589847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 208285124649546534291701 19526730435894987589847)
  ·
    refine ⟨29290095653842481384771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19526730435894987589847 29290095653842481384771)
    ·
      refine ⟨43935143480763722077157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29290095653842481384771 43935143480763722077157)
      ·
        refine ⟨8237839402643197889467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43935143480763722077157 8237839402643197889467)
        ·
          refine ⟨12356759103964796834201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8237839402643197889467 12356759103964796834201)
          ·
            refine ⟨9267569327973597625651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12356759103964796834201 9267569327973597625651)
            ·
              refine ⟨13901353991960396438477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9267569327973597625651 13901353991960396438477)
              ·
                refine ⟨5213007746985148664429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13901353991960396438477 5213007746985148664429)
                ·
                  refine ⟨1954877905119430749161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5213007746985148664429 1954877905119430749161)
                  ·
                    rfl

theorem cell21_8566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_8566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_8566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_8566 prefixEnd_8566 := by exact prefixLift 8566
  have htrace : WordTrace (prefixWord ++ tailWord_8566) baseStart_8566 baseEnd_8566 := by
    simpa [prefixWord, tailWord_8566, baseEnd_8566] using wordTrace_append hprefix tailTrace_8566
  have hstable : (prefixWord ++ tailWord_8566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8566).length < 2 ^ (prefixWord ++ tailWord_8566).sum := by decide
  have hdescent : baseEnd_8566 < baseStart_8566 := by decide
  rcases family_descends (prefixWord ++ tailWord_8566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8588 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 6]
def baseStart_8588 : Nat := 118140960795 + 8588 * 2 ^ 59
def prefixEnd_8588 : Nat := 4983230072969 + 3 ^ 40 * 8588 * 2
def baseEnd_8588 : Nat := 1959898604852281382449

theorem tailTrace_8588 : CollatzResearch.WordTrace tailWord_8588 prefixEnd_8588 1959898604852281382449 := by
  unfold tailWord_8588
  simp only [CollatzResearch.WordTrace]
  refine ⟨156615046447308779369209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 208820061929745039158945 156615046447308779369209)
  ·
    refine ⟨117461284835481584526907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156615046447308779369209 117461284835481584526907)
    ·
      refine ⟨176191927253222376790361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117461284835481584526907 176191927253222376790361)
      ·
        refine ⟨132143945439916782592771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176191927253222376790361 132143945439916782592771)
        ·
          refine ⟨198215918159875173889157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132143945439916782592771 198215918159875173889157)
          ·
            refine ⟨37165484654976595104217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198215918159875173889157 37165484654976595104217)
            ·
              refine ⟨27874113491232446328163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37165484654976595104217 27874113491232446328163)
              ·
                refine ⟨41811170236848669492245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27874113491232446328163 41811170236848669492245)
                ·
                  refine ⟨1959898604852281382449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41811170236848669492245 1959898604852281382449)
                  ·
                    rfl

theorem cell21_8588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_8588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_8588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_8588 prefixEnd_8588 := by exact prefixLift 8588
  have htrace : WordTrace (prefixWord ++ tailWord_8588) baseStart_8588 baseEnd_8588 := by
    simpa [prefixWord, tailWord_8588, baseEnd_8588] using wordTrace_append hprefix tailTrace_8588
  have hstable : (prefixWord ++ tailWord_8588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8588).length < 2 ^ (prefixWord ++ tailWord_8588).sum := by decide
  have hdescent : baseEnd_8588 < baseStart_8588 := by decide
  rcases family_descends (prefixWord ++ tailWord_8588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8709 : List Nat := [1, 3, 1, 1, 2, 2, 3, 3, 5]
def baseStart_8709 : Nat := 118140960795 + 8709 * 2 ^ 59
def prefixEnd_8709 : Nat := 4983230072969 + 3 ^ 40 * 8709 * 2
def baseEnd_8709 : Nat := 1987512453382959865535

theorem tailTrace_8709 : CollatzResearch.WordTrace tailWord_8709 prefixEnd_8709 1987512453382959865535 := by
  unfold tailWord_8709
  simp only [CollatzResearch.WordTrace]
  refine ⟨317643325456255223893181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 211762216970836815928787 317643325456255223893181)
  ·
    refine ⟨119116247046095708959943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 317643325456255223893181 119116247046095708959943)
    ·
      refine ⟨178674370569143563439915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119116247046095708959943 178674370569143563439915)
      ·
        refine ⟨268011555853715345159873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178674370569143563439915 268011555853715345159873)
        ·
          refine ⟨201008666890286508869905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268011555853715345159873 201008666890286508869905)
          ·
            refine ⟨150756500167714881652429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201008666890286508869905 150756500167714881652429)
            ·
              refine ⟨56533687562893080619661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150756500167714881652429 56533687562893080619661)
              ·
                refine ⟨21200132836084905232373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56533687562893080619661 21200132836084905232373)
                ·
                  refine ⟨1987512453382959865535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21200132836084905232373 1987512453382959865535)
                  ·
                    rfl

theorem cell21_8709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_8709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_8709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_8709 prefixEnd_8709 := by exact prefixLift 8709
  have htrace : WordTrace (prefixWord ++ tailWord_8709) baseStart_8709 baseEnd_8709 := by
    simpa [prefixWord, tailWord_8709, baseEnd_8709] using wordTrace_append hprefix tailTrace_8709
  have hstable : (prefixWord ++ tailWord_8709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8709).length < 2 ^ (prefixWord ++ tailWord_8709).sum := by decide
  have hdescent : baseEnd_8709 < baseStart_8709 := by decide
  rcases family_descends (prefixWord ++ tailWord_8709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8754 : List Nat := [3, 2, 1, 1, 2, 1, 11]
def baseStart_8754 : Nat := 118140960795 + 8754 * 2 ^ 59
def prefixEnd_8754 : Nat := 4983230072969 + 3 ^ 40 * 8754 * 2
def baseEnd_8754 : Nat := 221975785163653512827

theorem tailTrace_8754 : CollatzResearch.WordTrace tailWord_8754 prefixEnd_8754 221975785163653512827 := by
  unfold tailWord_8754
  simp only [CollatzResearch.WordTrace]
  refine ⟨79821152573306977320329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 212856406862151939520877 79821152573306977320329)
  ·
    refine ⟨59865864429980232990247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79821152573306977320329 59865864429980232990247)
    ·
      refine ⟨89798796644970349485371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59865864429980232990247 89798796644970349485371)
      ·
        refine ⟨134698194967455524228057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89798796644970349485371 134698194967455524228057)
        ·
          refine ⟨101023646225591643171043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134698194967455524228057 101023646225591643171043)
          ·
            refine ⟨151535469338387464756565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101023646225591643171043 151535469338387464756565)
            ·
              refine ⟨221975785163653512827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 151535469338387464756565 221975785163653512827)
              ·
                rfl

theorem cell21_8754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 11].length) (baseStart_8754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_8754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_8754 prefixEnd_8754 := by exact prefixLift 8754
  have htrace : WordTrace (prefixWord ++ tailWord_8754) baseStart_8754 baseEnd_8754 := by
    simpa [prefixWord, tailWord_8754, baseEnd_8754] using wordTrace_append hprefix tailTrace_8754
  have hstable : (prefixWord ++ tailWord_8754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8754).length < 2 ^ (prefixWord ++ tailWord_8754).sum := by decide
  have hdescent : baseEnd_8754 < baseStart_8754 := by decide
  rcases family_descends (prefixWord ++ tailWord_8754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8799 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 8]
def baseStart_8799 : Nat := 118140960795 + 8799 * 2 ^ 59
def prefixEnd_8799 : Nat := 4983230072969 + 3 ^ 40 * 8799 * 2
def baseEnd_8799 : Nat := 2008051679562803365351

theorem tailTrace_8799 : CollatzResearch.WordTrace tailWord_8799 prefixEnd_8799 2008051679562803365351 := by
  unfold tailWord_8799
  simp only [CollatzResearch.WordTrace]
  refine ⟨320925895130200594669451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 213950596753467063112967 320925895130200594669451)
  ·
    refine ⟨481388842695300892004177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 320925895130200594669451 481388842695300892004177)
    ·
      refine ⟨361041632021475669003133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 481388842695300892004177 361041632021475669003133)
      ·
        refine ⟨135390612008053375876175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 361041632021475669003133 135390612008053375876175)
        ·
          refine ⟨203085918012080063814263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135390612008053375876175 203085918012080063814263)
          ·
            refine ⟨304628877018120095721395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203085918012080063814263 304628877018120095721395)
            ·
              refine ⟨456943315527180143582093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304628877018120095721395 456943315527180143582093)
              ·
                refine ⟨171353743322692553843285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 456943315527180143582093 171353743322692553843285)
                ·
                  refine ⟨2008051679562803365351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 171353743322692553843285 2008051679562803365351)
                  ·
                    rfl

theorem cell21_8799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 8].length) (baseStart_8799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_8799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_8799 prefixEnd_8799 := by exact prefixLift 8799
  have htrace : WordTrace (prefixWord ++ tailWord_8799) baseStart_8799 baseEnd_8799 := by
    simpa [prefixWord, tailWord_8799, baseEnd_8799] using wordTrace_append hprefix tailTrace_8799
  have hstable : (prefixWord ++ tailWord_8799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8799).length < 2 ^ (prefixWord ++ tailWord_8799).sum := by decide
  have hdescent : baseEnd_8799 < baseStart_8799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8937 : List Nat := [1, 2, 1, 1, 1, 2, 7, 1, 5]
def baseStart_8937 : Nat := 118140960795 + 8937 * 2 ^ 59
def prefixEnd_8937 : Nat := 4983230072969 + 3 ^ 40 * 8937 * 2
def baseEnd_8937 : Nat := 2039545159705230065069

theorem tailTrace_8937 : CollatzResearch.WordTrace tailWord_8937 prefixEnd_8937 2039545159705230065069 := by
  unfold tailWord_8937
  simp only [CollatzResearch.WordTrace]
  refine ⟨325959168630250163193065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 217306112420166775462043 325959168630250163193065)
  ·
    refine ⟨244469376472687622394799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 325959168630250163193065 244469376472687622394799)
    ·
      refine ⟨366704064709031433592199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244469376472687622394799 366704064709031433592199)
      ·
        refine ⟨550056097063547150388299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366704064709031433592199 550056097063547150388299)
        ·
          refine ⟨825084145595320725582449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550056097063547150388299 825084145595320725582449)
          ·
            refine ⟨618813109196490544186837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 825084145595320725582449 618813109196490544186837)
            ·
              refine ⟨14503432246792747129379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 618813109196490544186837 14503432246792747129379)
              ·
                refine ⟨21755148370189120694069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14503432246792747129379 21755148370189120694069)
                ·
                  refine ⟨2039545159705230065069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21755148370189120694069 2039545159705230065069)
                  ·
                    rfl

theorem cell21_8937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_8937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_8937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_8937 prefixEnd_8937 := by exact prefixLift 8937
  have htrace : WordTrace (prefixWord ++ tailWord_8937) baseStart_8937 baseEnd_8937 := by
    simpa [prefixWord, tailWord_8937, baseEnd_8937] using wordTrace_append hprefix tailTrace_8937
  have hstable : (prefixWord ++ tailWord_8937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8937).length < 2 ^ (prefixWord ++ tailWord_8937).sum := by decide
  have hdescent : baseEnd_8937 < baseStart_8937 := by decide
  rcases family_descends (prefixWord ++ tailWord_8937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8988 : List Nat := [2, 2, 3, 1, 1, 5, 2, 2, 3]
def baseStart_8988 : Nat := 118140960795 + 8988 * 2 ^ 59
def prefixEnd_8988 : Nat := 4983230072969 + 3 ^ 40 * 8988 * 2
def baseEnd_8988 : Nat := 2051184054540474714965

theorem tailTrace_8988 : CollatzResearch.WordTrace tailWord_8988 prefixEnd_8988 2051184054540474714965 := by
  unfold tailWord_8988
  simp only [CollatzResearch.WordTrace]
  refine ⟨163909645722742936649809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 218546194296990582199745 163909645722742936649809)
  ·
    refine ⟨122932234292057202487357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163909645722742936649809 122932234292057202487357)
    ·
      refine ⟨46099587859521450932759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122932234292057202487357 46099587859521450932759)
      ·
        refine ⟨69149381789282176399139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46099587859521450932759 69149381789282176399139)
        ·
          refine ⟨103724072683923264598709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69149381789282176399139 103724072683923264598709)
          ·
            refine ⟨9724131814117806056129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103724072683923264598709 9724131814117806056129)
            ·
              refine ⟨7293098860588354542097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9724131814117806056129 7293098860588354542097)
              ·
                refine ⟨5469824145441265906573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7293098860588354542097 5469824145441265906573)
                ·
                  refine ⟨2051184054540474714965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5469824145441265906573 2051184054540474714965)
                  ·
                    rfl

theorem cell21_8988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_8988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_8988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_8988 prefixEnd_8988 := by exact prefixLift 8988
  have htrace : WordTrace (prefixWord ++ tailWord_8988) baseStart_8988 baseEnd_8988 := by
    simpa [prefixWord, tailWord_8988, baseEnd_8988] using wordTrace_append hprefix tailTrace_8988
  have hstable : (prefixWord ++ tailWord_8988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8988).length < 2 ^ (prefixWord ++ tailWord_8988).sum := by decide
  have hdescent : baseEnd_8988 < baseStart_8988 := by decide
  rcases family_descends (prefixWord ++ tailWord_8988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9013 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 7]
def baseStart_9013 : Nat := 118140960795 + 9013 * 2 ^ 59
def prefixEnd_9013 : Nat := 4983230072969 + 3 ^ 40 * 9013 * 2
def baseEnd_9013 : Nat := 2056889395145986798247

theorem tailTrace_9013 : CollatzResearch.WordTrace tailWord_9013 prefixEnd_9013 2056889395145986798247 := by
  unfold tailWord_9013
  simp only [CollatzResearch.WordTrace]
  refine ⟨328731116354915142959693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 219154077569943428639795 328731116354915142959693)
  ·
    refine ⟨123274168633093178609885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 328731116354915142959693 123274168633093178609885)
    ·
      refine ⟨46227813237409941978707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123274168633093178609885 46227813237409941978707)
      ·
        refine ⟨69341719856114912968061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46227813237409941978707 69341719856114912968061)
        ·
          refine ⟨26003144946043092363023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69341719856114912968061 26003144946043092363023)
          ·
            refine ⟨39004717419064638544535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26003144946043092363023 39004717419064638544535)
            ·
              refine ⟨58507076128596957816803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39004717419064638544535 58507076128596957816803)
              ·
                refine ⟨87760614192895436725205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58507076128596957816803 87760614192895436725205)
                ·
                  refine ⟨2056889395145986798247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 87760614192895436725205 2056889395145986798247)
                  ·
                    rfl

theorem cell21_9013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_9013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9013 prefixEnd_9013 := by exact prefixLift 9013
  have htrace : WordTrace (prefixWord ++ tailWord_9013) baseStart_9013 baseEnd_9013 := by
    simpa [prefixWord, tailWord_9013, baseEnd_9013] using wordTrace_append hprefix tailTrace_9013
  have hstable : (prefixWord ++ tailWord_9013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9013).length < 2 ^ (prefixWord ++ tailWord_9013).sum := by decide
  have hdescent : baseEnd_9013 < baseStart_9013 := by decide
  rcases family_descends (prefixWord ++ tailWord_9013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9027 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 6]
def baseStart_9027 : Nat := 118140960795 + 9027 * 2 ^ 59
def prefixEnd_9027 : Nat := 4983230072969 + 3 ^ 40 * 9027 * 2
def baseEnd_9027 : Nat := 2060084385885073564885

theorem tailTrace_9027 : CollatzResearch.WordTrace tailWord_9027 prefixEnd_9027 2060084385885073564885 := by
  unfold tailWord_9027
  simp only [CollatzResearch.WordTrace]
  refine ⟨329241738304195533969335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 219494492202797022646223 329241738304195533969335)
  ·
    refine ⟨493862607456293300954003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 329241738304195533969335 493862607456293300954003)
    ·
      refine ⟨740793911184439951431005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 493862607456293300954003 740793911184439951431005)
      ·
        refine ⟨277797716694164981786627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 740793911184439951431005 277797716694164981786627)
        ·
          refine ⟨416696575041247472679941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277797716694164981786627 416696575041247472679941)
          ·
            refine ⟨78130607820233901127489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 416696575041247472679941 78130607820233901127489)
            ·
              refine ⟨58597955865175425845617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78130607820233901127489 58597955865175425845617)
              ·
                refine ⟨43948466898881569384213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58597955865175425845617 43948466898881569384213)
                ·
                  refine ⟨2060084385885073564885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43948466898881569384213 2060084385885073564885)
                  ·
                    rfl

theorem cell21_9027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 6].length) (baseStart_9027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9027 prefixEnd_9027 := by exact prefixLift 9027
  have htrace : WordTrace (prefixWord ++ tailWord_9027) baseStart_9027 baseEnd_9027 := by
    simpa [prefixWord, tailWord_9027, baseEnd_9027] using wordTrace_append hprefix tailTrace_9027
  have hstable : (prefixWord ++ tailWord_9027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9027).length < 2 ^ (prefixWord ++ tailWord_9027).sum := by decide
  have hdescent : baseEnd_9027 < baseStart_9027 := by decide
  rcases family_descends (prefixWord ++ tailWord_9027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9244 : List Nat := [2, 2, 3, 1, 4, 2, 2, 5]
def baseStart_9244 : Nat := 118140960795 + 9244 * 2 ^ 59
def prefixEnd_9244 : Nat := 4983230072969 + 3 ^ 40 * 9244 * 2
def baseEnd_9244 : Nat := 703202247446972815925

theorem tailTrace_9244 : CollatzResearch.WordTrace tailWord_9244 prefixEnd_9244 703202247446972815925 := by
  unfold tailWord_9244
  simp only [CollatzResearch.WordTrace]
  refine ⟨168578189259020797309393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 224770919012027729745857 168578189259020797309393)
  ·
    refine ⟨126433641944265597982045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168578189259020797309393 126433641944265597982045)
    ·
      refine ⟨47412615729099599243267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126433641944265597982045 47412615729099599243267)
      ·
        refine ⟨71118923593649398864901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47412615729099599243267 71118923593649398864901)
        ·
          refine ⟨13334798173809262287169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71118923593649398864901 13334798173809262287169)
          ·
            refine ⟨10001098630356946715377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13334798173809262287169 10001098630356946715377)
            ·
              refine ⟨7500823972767710036533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10001098630356946715377 7500823972767710036533)
              ·
                refine ⟨703202247446972815925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7500823972767710036533 703202247446972815925)
                ·
                  rfl

theorem cell21_9244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 5].length) (baseStart_9244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9244 prefixEnd_9244 := by exact prefixLift 9244
  have htrace : WordTrace (prefixWord ++ tailWord_9244) baseStart_9244 baseEnd_9244 := by
    simpa [prefixWord, tailWord_9244, baseEnd_9244] using wordTrace_append hprefix tailTrace_9244
  have hstable : (prefixWord ++ tailWord_9244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9244).length < 2 ^ (prefixWord ++ tailWord_9244).sum := by decide
  have hdescent : baseEnd_9244 < baseStart_9244 := by decide
  rcases family_descends (prefixWord ++ tailWord_9244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9348 : List Nat := [2, 3, 2, 1, 2, 2, 2, 3, 4]
def baseStart_9348 : Nat := 118140960795 + 9348 * 2 ^ 59
def prefixEnd_9348 : Nat := 4983230072969 + 3 ^ 40 * 9348 * 2
def baseEnd_9348 : Nat := 2133340959259848714229

theorem tailTrace_9348 : CollatzResearch.WordTrace tailWord_9348 prefixEnd_9348 2133340959259848714229 := by
  unfold tailWord_9348
  simp only [CollatzResearch.WordTrace]
  refine ⟨170474785070633678202349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 227299713427511570936465 170474785070633678202349)
  ·
    refine ⟨63928044401487629325881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170474785070633678202349 63928044401487629325881)
    ·
      refine ⟨47946033301115721994411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63928044401487629325881 47946033301115721994411)
      ·
        refine ⟨71919049951673582991617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47946033301115721994411 71919049951673582991617)
        ·
          refine ⟨53939287463755187243713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71919049951673582991617 53939287463755187243713)
          ·
            refine ⟨40454465597816390432785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53939287463755187243713 40454465597816390432785)
            ·
              refine ⟨30340849198362292824589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40454465597816390432785 30340849198362292824589)
              ·
                refine ⟨11377818449385859809221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30340849198362292824589 11377818449385859809221)
                ·
                  refine ⟨2133340959259848714229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11377818449385859809221 2133340959259848714229)
                  ·
                    rfl

theorem cell21_9348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_9348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9348 prefixEnd_9348 := by exact prefixLift 9348
  have htrace : WordTrace (prefixWord ++ tailWord_9348) baseStart_9348 baseEnd_9348 := by
    simpa [prefixWord, tailWord_9348, baseEnd_9348] using wordTrace_append hprefix tailTrace_9348
  have hstable : (prefixWord ++ tailWord_9348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9348).length < 2 ^ (prefixWord ++ tailWord_9348).sum := by decide
  have hdescent : baseEnd_9348 < baseStart_9348 := by decide
  rcases family_descends (prefixWord ++ tailWord_9348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9376 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 7]
def baseStart_9376 : Nat := 118140960795 + 9376 * 2 ^ 59
def prefixEnd_9376 : Nat := 4983230072969 + 3 ^ 40 * 9376 * 2
def baseEnd_9376 : Nat := 2139730940738022247505

theorem tailTrace_9376 : CollatzResearch.WordTrace tailWord_9376 prefixEnd_9376 2139730940738022247505 := by
  unfold tailWord_9376
  simp only [CollatzResearch.WordTrace]
  refine ⟨170985407019914069211991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 227980542693218758949321 170985407019914069211991)
  ·
    refine ⟨256478110529871103817987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170985407019914069211991 256478110529871103817987)
    ·
      refine ⟨384717165794806655726981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256478110529871103817987 384717165794806655726981)
      ·
        refine ⟨72134468586526247948809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 384717165794806655726981 72134468586526247948809)
        ·
          refine ⟨54100851439894685961607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72134468586526247948809 54100851439894685961607)
          ·
            refine ⟨81151277159842028942411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54100851439894685961607 81151277159842028942411)
            ·
              refine ⟨121726915739763043413617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81151277159842028942411 121726915739763043413617)
              ·
                refine ⟨91295186804822282560213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121726915739763043413617 91295186804822282560213)
                ·
                  refine ⟨2139730940738022247505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 91295186804822282560213 2139730940738022247505)
                  ·
                    rfl

theorem cell21_9376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_9376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9376 prefixEnd_9376 := by exact prefixLift 9376
  have htrace : WordTrace (prefixWord ++ tailWord_9376) baseStart_9376 baseEnd_9376 := by
    simpa [prefixWord, tailWord_9376, baseEnd_9376] using wordTrace_append hprefix tailTrace_9376
  have hstable : (prefixWord ++ tailWord_9376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9376).length < 2 ^ (prefixWord ++ tailWord_9376).sum := by decide
  have hdescent : baseEnd_9376 < baseStart_9376 := by decide
  rcases family_descends (prefixWord ++ tailWord_9376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9393 : List Nat := [1, 2, 2, 5, 1, 1, 1, 3, 5]
def baseStart_9393 : Nat := 118140960795 + 9393 * 2 ^ 59
def prefixEnd_9393 : Nat := 4983230072969 + 3 ^ 40 * 9393 * 2
def baseEnd_9393 : Nat := 2143610572349770464137

theorem tailTrace_9393 : CollatzResearch.WordTrace tailWord_9393 prefixEnd_9393 2143610572349770464137 := by
  unfold tailWord_9393
  simp only [CollatzResearch.WordTrace]
  refine ⟨342590854978240041792833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 228393903318826694528555 342590854978240041792833)
  ·
    refine ⟨256943141233680031344625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 342590854978240041792833 256943141233680031344625)
    ·
      refine ⟨192707355925260023508469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256943141233680031344625 192707355925260023508469)
      ·
        refine ⟨18066314617993127203919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 192707355925260023508469 18066314617993127203919)
        ·
          refine ⟨27099471926989690805879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18066314617993127203919 27099471926989690805879)
          ·
            refine ⟨40649207890484536208819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27099471926989690805879 40649207890484536208819)
            ·
              refine ⟨60973811835726804313229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40649207890484536208819 60973811835726804313229)
              ·
                refine ⟨22865179438397551617461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60973811835726804313229 22865179438397551617461)
                ·
                  refine ⟨2143610572349770464137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22865179438397551617461 2143610572349770464137)
                  ·
                    rfl

theorem cell21_9393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_9393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9393 prefixEnd_9393 := by exact prefixLift 9393
  have htrace : WordTrace (prefixWord ++ tailWord_9393) baseStart_9393 baseEnd_9393 := by
    simpa [prefixWord, tailWord_9393, baseEnd_9393] using wordTrace_append hprefix tailTrace_9393
  have hstable : (prefixWord ++ tailWord_9393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9393).length < 2 ^ (prefixWord ++ tailWord_9393).sum := by decide
  have hdescent : baseEnd_9393 < baseStart_9393 := by decide
  rcases family_descends (prefixWord ++ tailWord_9393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9407 : List Nat := [1, 1, 2, 2, 2, 2, 2, 5, 4]
def baseStart_9407 : Nat := 118140960795 + 9407 * 2 ^ 59
def prefixEnd_9407 : Nat := 4983230072969 + 3 ^ 40 * 9407 * 2
def baseEnd_9407 : Nat := 2146805563088857230775

theorem tailTrace_9407 : CollatzResearch.WordTrace tailWord_9407 prefixEnd_9407 2146805563088857230775 := by
  unfold tailWord_9407
  simp only [CollatzResearch.WordTrace]
  refine ⟨343101476927520432802475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 228734317951680288534983 343101476927520432802475)
  ·
    refine ⟨514652215391280649203713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 343101476927520432802475 514652215391280649203713)
    ·
      refine ⟨385989161543460486902785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 514652215391280649203713 385989161543460486902785)
      ·
        refine ⟨289491871157595365177089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385989161543460486902785 289491871157595365177089)
        ·
          refine ⟨217118903368196523882817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289491871157595365177089 217118903368196523882817)
          ·
            refine ⟨162839177526147392912113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217118903368196523882817 162839177526147392912113)
            ·
              refine ⟨122129383144610544684085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162839177526147392912113 122129383144610544684085)
              ·
                refine ⟨11449629669807238564133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122129383144610544684085 11449629669807238564133)
                ·
                  refine ⟨2146805563088857230775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11449629669807238564133 2146805563088857230775)
                  ·
                    rfl

theorem cell21_9407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 4].length) (baseStart_9407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9407 prefixEnd_9407 := by exact prefixLift 9407
  have htrace : WordTrace (prefixWord ++ tailWord_9407) baseStart_9407 baseEnd_9407 := by
    simpa [prefixWord, tailWord_9407, baseEnd_9407] using wordTrace_append hprefix tailTrace_9407
  have hstable : (prefixWord ++ tailWord_9407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9407).length < 2 ^ (prefixWord ++ tailWord_9407).sum := by decide
  have hdescent : baseEnd_9407 < baseStart_9407 := by decide
  rcases family_descends (prefixWord ++ tailWord_9407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9458 : List Nat := [3, 2, 1, 3, 3, 2, 2, 1, 4]
def baseStart_9458 : Nat := 118140960795 + 9458 * 2 ^ 59
def prefixEnd_9458 : Nat := 4983230072969 + 3 ^ 40 * 9458 * 2
def baseEnd_9458 : Nat := 2158444457924101880671

theorem tailTrace_9458 : CollatzResearch.WordTrace tailWord_9458 prefixEnd_9458 2158444457924101880671 := by
  unfold tailWord_9458
  simp only [CollatzResearch.WordTrace]
  refine ⟨86240399935689035727257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 229974399828504095272685 86240399935689035727257)
  ·
    refine ⟨64680299951766776795443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86240399935689035727257 64680299951766776795443)
    ·
      refine ⟨97020449927650165193165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64680299951766776795443 97020449927650165193165)
      ·
        refine ⟨36382668722868811947437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97020449927650165193165 36382668722868811947437)
        ·
          refine ⟨13643500771075804480289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36382668722868811947437 13643500771075804480289)
          ·
            refine ⟨10232625578306853360217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13643500771075804480289 10232625578306853360217)
            ·
              refine ⟨7674469183730140020163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10232625578306853360217 7674469183730140020163)
              ·
                refine ⟨11511703775595210030245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7674469183730140020163 11511703775595210030245)
                ·
                  refine ⟨2158444457924101880671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11511703775595210030245 2158444457924101880671)
                  ·
                    rfl

theorem cell21_9458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_9458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9458 prefixEnd_9458 := by exact prefixLift 9458
  have htrace : WordTrace (prefixWord ++ tailWord_9458) baseStart_9458 baseEnd_9458 := by
    simpa [prefixWord, tailWord_9458, baseEnd_9458] using wordTrace_append hprefix tailTrace_9458
  have hstable : (prefixWord ++ tailWord_9458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9458).length < 2 ^ (prefixWord ++ tailWord_9458).sum := by decide
  have hdescent : baseEnd_9458 < baseStart_9458 := by decide
  rcases family_descends (prefixWord ++ tailWord_9458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9517 : List Nat := [1, 5, 3, 1, 1, 1, 2, 3, 4]
def baseStart_9517 : Nat := 118140960795 + 9517 * 2 ^ 59
def prefixEnd_9517 : Nat := 4983230072969 + 3 ^ 40 * 9517 * 2
def baseEnd_9517 : Nat := 2171909061753110397217

theorem tailTrace_9517 : CollatzResearch.WordTrace tailWord_9517 prefixEnd_9517 2171909061753110397217 := by
  unfold tailWord_9517
  simp only [CollatzResearch.WordTrace]
  refine ⟨347113506529009219306805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 231409004352672812871203 347113506529009219306805)
  ·
    refine ⟨32541891237094614310013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 347113506529009219306805 32541891237094614310013)
    ·
      refine ⟨12203209213910480366255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32541891237094614310013 12203209213910480366255)
      ·
        refine ⟨18304813820865720549383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12203209213910480366255 18304813820865720549383)
        ·
          refine ⟨27457220731298580824075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18304813820865720549383 27457220731298580824075)
          ·
            refine ⟨41185831096947871236113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27457220731298580824075 41185831096947871236113)
            ·
              refine ⟨30889373322710903427085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41185831096947871236113 30889373322710903427085)
              ·
                refine ⟨11583514996016588785157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30889373322710903427085 11583514996016588785157)
                ·
                  refine ⟨2171909061753110397217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11583514996016588785157 2171909061753110397217)
                  ·
                    rfl

theorem cell21_9517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_9517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9517 prefixEnd_9517 := by exact prefixLift 9517
  have htrace : WordTrace (prefixWord ++ tailWord_9517) baseStart_9517 baseEnd_9517 := by
    simpa [prefixWord, tailWord_9517, baseEnd_9517] using wordTrace_append hprefix tailTrace_9517
  have hstable : (prefixWord ++ tailWord_9517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9517).length < 2 ^ (prefixWord ++ tailWord_9517).sum := by decide
  have hdescent : baseEnd_9517 < baseStart_9517 := by decide
  rcases family_descends (prefixWord ++ tailWord_9517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9545 : List Nat := [1, 2, 1, 1, 2, 3, 3, 5, 3]
def baseStart_9545 : Nat := 118140960795 + 9545 * 2 ^ 59
def prefixEnd_9545 : Nat := 4983230072969 + 3 ^ 40 * 9545 * 2
def baseEnd_9545 : Nat := 2178299043231283930493

theorem tailTrace_9545 : CollatzResearch.WordTrace tailWord_9545 prefixEnd_9545 2178299043231283930493 := by
  unfold tailWord_9545
  simp only [CollatzResearch.WordTrace]
  refine ⟨348134750427570001326089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 232089833618380000884059 348134750427570001326089)
  ·
    refine ⟨261101062820677500994567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 348134750427570001326089 261101062820677500994567)
    ·
      refine ⟨391651594231016251491851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261101062820677500994567 391651594231016251491851)
      ·
        refine ⟨587477391346524377237777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391651594231016251491851 587477391346524377237777)
        ·
          refine ⟨440608043509893282928333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 587477391346524377237777 440608043509893282928333)
          ·
            refine ⟨165228016316209981098125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 440608043509893282928333 165228016316209981098125)
            ·
              refine ⟨61960506118578742911797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165228016316209981098125 61960506118578742911797)
              ·
                refine ⟨5808797448616757147981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61960506118578742911797 5808797448616757147981)
                ·
                  refine ⟨2178299043231283930493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5808797448616757147981 2178299043231283930493)
                  ·
                    rfl

theorem cell21_9545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 3].length) (baseStart_9545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9545 prefixEnd_9545 := by exact prefixLift 9545
  have htrace : WordTrace (prefixWord ++ tailWord_9545) baseStart_9545 baseEnd_9545 := by
    simpa [prefixWord, tailWord_9545, baseEnd_9545] using wordTrace_append hprefix tailTrace_9545
  have hstable : (prefixWord ++ tailWord_9545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9545).length < 2 ^ (prefixWord ++ tailWord_9545).sum := by decide
  have hdescent : baseEnd_9545 < baseStart_9545 := by decide
  rcases family_descends (prefixWord ++ tailWord_9545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9559 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 6]
def baseStart_9559 : Nat := 118140960795 + 9559 * 2 ^ 59
def prefixEnd_9559 : Nat := 4983230072969 + 3 ^ 40 * 9559 * 2
def baseEnd_9559 : Nat := 2181494033970370697131

theorem tailTrace_9559 : CollatzResearch.WordTrace tailWord_9559 prefixEnd_9559 2181494033970370697131 := by
  unfold tailWord_9559
  simp only [CollatzResearch.WordTrace]
  refine ⟨348645372376850392335731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 232430248251233594890487 348645372376850392335731)
  ·
    refine ⟨522968058565275588503597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 348645372376850392335731 522968058565275588503597)
    ·
      refine ⟨196113021961978345688849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 522968058565275588503597 196113021961978345688849)
      ·
        refine ⟨147084766471483759266637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196113021961978345688849 147084766471483759266637)
        ·
          refine ⟨55156787426806409724989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147084766471483759266637 55156787426806409724989)
          ·
            refine ⟨20683795285052403646871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55156787426806409724989 20683795285052403646871)
            ·
              refine ⟨31025692927578605470307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20683795285052403646871 31025692927578605470307)
              ·
                refine ⟨46538539391367908205461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31025692927578605470307 46538539391367908205461)
                ·
                  refine ⟨2181494033970370697131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46538539391367908205461 2181494033970370697131)
                  ·
                    rfl

theorem cell21_9559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 6].length) (baseStart_9559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9559 prefixEnd_9559 := by exact prefixLift 9559
  have htrace : WordTrace (prefixWord ++ tailWord_9559) baseStart_9559 baseEnd_9559 := by
    simpa [prefixWord, tailWord_9559, baseEnd_9559] using wordTrace_append hprefix tailTrace_9559
  have hstable : (prefixWord ++ tailWord_9559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9559).length < 2 ^ (prefixWord ++ tailWord_9559).sum := by decide
  have hdescent : baseEnd_9559 < baseStart_9559 := by decide
  rcases family_descends (prefixWord ++ tailWord_9559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9573 : List Nat := [1, 3, 1, 3, 1, 2, 2, 8]
def baseStart_9573 : Nat := 118140960795 + 9573 * 2 ^ 59
def prefixEnd_9573 : Nat := 4983230072969 + 3 ^ 40 * 9573 * 2
def baseEnd_9573 : Nat := 728229674903152487923

theorem tailTrace_9573 : CollatzResearch.WordTrace tailWord_9573 prefixEnd_9573 728229674903152487923 := by
  unfold tailWord_9573
  simp only [CollatzResearch.WordTrace]
  refine ⟨349155994326130783345373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 232770662884087188896915 349155994326130783345373)
  ·
    refine ⟨130933497872299043754515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 349155994326130783345373 130933497872299043754515)
    ·
      refine ⟨196400246808448565631773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130933497872299043754515 196400246808448565631773)
      ·
        refine ⟨73650092553168212111915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196400246808448565631773 73650092553168212111915)
        ·
          refine ⟨110475138829752318167873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73650092553168212111915 110475138829752318167873)
          ·
            refine ⟨82856354122314238625905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110475138829752318167873 82856354122314238625905)
            ·
              refine ⟨62142265591735678969429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82856354122314238625905 62142265591735678969429)
              ·
                refine ⟨728229674903152487923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 62142265591735678969429 728229674903152487923)
                ·
                  rfl

theorem cell21_9573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 8].length) (baseStart_9573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9573 prefixEnd_9573 := by exact prefixLift 9573
  have htrace : WordTrace (prefixWord ++ tailWord_9573) baseStart_9573 baseEnd_9573 := by
    simpa [prefixWord, tailWord_9573, baseEnd_9573] using wordTrace_append hprefix tailTrace_9573
  have hstable : (prefixWord ++ tailWord_9573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9573).length < 2 ^ (prefixWord ++ tailWord_9573).sum := by decide
  have hdescent : baseEnd_9573 < baseStart_9573 := by decide
  rcases family_descends (prefixWord ++ tailWord_9573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9621 : List Nat := [1, 3, 2, 1, 1, 2, 2, 6, 3]
def baseStart_9621 : Nat := 118140960795 + 9621 * 2 ^ 59
def prefixEnd_9621 : Nat := 4983230072969 + 3 ^ 40 * 9621 * 2
def baseEnd_9621 : Nat := 2195643278672040663671

theorem tailTrace_9621 : CollatzResearch.WordTrace tailWord_9621 prefixEnd_9621 2195643278672040663671 := by
  unfold tailWord_9621
  simp only [CollatzResearch.WordTrace]
  refine ⟨350906698152234981092717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 233937798768156654061811 350906698152234981092717)
  ·
    refine ⟨131590011807088117909769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 350906698152234981092717 131590011807088117909769)
    ·
      refine ⟨98692508855316088432327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131590011807088117909769 98692508855316088432327)
      ·
        refine ⟨148038763282974132648491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98692508855316088432327 148038763282974132648491)
        ·
          refine ⟨222058144924461198972737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148038763282974132648491 222058144924461198972737)
          ·
            refine ⟨166543608693345899229553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222058144924461198972737 166543608693345899229553)
            ·
              refine ⟨124907706520009424422165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166543608693345899229553 124907706520009424422165)
              ·
                refine ⟨5855048743125441769789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124907706520009424422165 5855048743125441769789)
                ·
                  refine ⟨2195643278672040663671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5855048743125441769789 2195643278672040663671)
                  ·
                    rfl

theorem cell21_9621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_9621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9621 prefixEnd_9621 := by exact prefixLift 9621
  have htrace : WordTrace (prefixWord ++ tailWord_9621) baseStart_9621 baseEnd_9621 := by
    simpa [prefixWord, tailWord_9621, baseEnd_9621] using wordTrace_append hprefix tailTrace_9621
  have hstable : (prefixWord ++ tailWord_9621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9621).length < 2 ^ (prefixWord ++ tailWord_9621).sum := by decide
  have hdescent : baseEnd_9621 < baseStart_9621 := by decide
  rcases family_descends (prefixWord ++ tailWord_9621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9635 : List Nat := [1, 1, 1, 4, 1, 3, 3, 3, 4]
def baseStart_9635 : Nat := 118140960795 + 9635 * 2 ^ 59
def prefixEnd_9635 : Nat := 4983230072969 + 3 ^ 40 * 9635 * 2
def baseEnd_9635 : Nat := 2198838269411127430309

theorem tailTrace_9635 : CollatzResearch.WordTrace tailWord_9635 prefixEnd_9635 2198838269411127430309 := by
  unfold tailWord_9635
  simp only [CollatzResearch.WordTrace]
  refine ⟨351417320101515372102359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 234278213401010248068239 351417320101515372102359)
  ·
    refine ⟨527125980152273058153539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 351417320101515372102359 527125980152273058153539)
    ·
      refine ⟨790688970228409587230309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 527125980152273058153539 790688970228409587230309)
      ·
        refine ⟨148254181917826797605683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 790688970228409587230309 148254181917826797605683)
        ·
          refine ⟨222381272876740196408525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148254181917826797605683 222381272876740196408525)
          ·
            refine ⟨83392977328777573653197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222381272876740196408525 83392977328777573653197)
            ·
              refine ⟨31272366498291590119949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83392977328777573653197 31272366498291590119949)
              ·
                refine ⟨11727137436859346294981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31272366498291590119949 11727137436859346294981)
                ·
                  refine ⟨2198838269411127430309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11727137436859346294981 2198838269411127430309)
                  ·
                    rfl

theorem cell21_9635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 4].length) (baseStart_9635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9635 prefixEnd_9635 := by exact prefixLift 9635
  have htrace : WordTrace (prefixWord ++ tailWord_9635) baseStart_9635 baseEnd_9635 := by
    simpa [prefixWord, tailWord_9635, baseEnd_9635] using wordTrace_append hprefix tailTrace_9635
  have hstable : (prefixWord ++ tailWord_9635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9635).length < 2 ^ (prefixWord ++ tailWord_9635).sum := by decide
  have hdescent : baseEnd_9635 < baseStart_9635 := by decide
  rcases family_descends (prefixWord ++ tailWord_9635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9649 : List Nat := [1, 2, 2, 4, 1, 1, 1, 9]
def baseStart_9649 : Nat := 118140960795 + 9649 * 2 ^ 59
def prefixEnd_9649 : Nat := 4983230072969 + 3 ^ 40 * 9649 * 2
def baseEnd_9649 : Nat := 734011086716738065649

theorem tailTrace_9649 : CollatzResearch.WordTrace tailWord_9649 prefixEnd_9649 734011086716738065649 := by
  unfold tailWord_9649
  simp only [CollatzResearch.WordTrace]
  refine ⟨351927942050795763112001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 234618628033863842074667 351927942050795763112001)
  ·
    refine ⟨263945956538096822334001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 351927942050795763112001 263945956538096822334001)
    ·
      refine ⟨197959467403572616750501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263945956538096822334001 197959467403572616750501)
      ·
        refine ⟨37117400138169865640719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197959467403572616750501 37117400138169865640719)
        ·
          refine ⟨55676100207254798461079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37117400138169865640719 55676100207254798461079)
          ·
            refine ⟨83514150310882197691619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55676100207254798461079 83514150310882197691619)
            ·
              refine ⟨125271225466323296537429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83514150310882197691619 125271225466323296537429)
              ·
                refine ⟨734011086716738065649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 125271225466323296537429 734011086716738065649)
                ·
                  rfl

theorem cell21_9649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 9].length) (baseStart_9649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9649 prefixEnd_9649 := by exact prefixLift 9649
  have htrace : WordTrace (prefixWord ++ tailWord_9649) baseStart_9649 baseEnd_9649 := by
    simpa [prefixWord, tailWord_9649, baseEnd_9649] using wordTrace_append hprefix tailTrace_9649
  have hstable : (prefixWord ++ tailWord_9649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9649).length < 2 ^ (prefixWord ++ tailWord_9649).sum := by decide
  have hdescent : baseEnd_9649 < baseStart_9649 := by decide
  rcases family_descends (prefixWord ++ tailWord_9649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9714 : List Nat := [3, 2, 1, 4, 1, 1, 1, 5, 3]
def baseStart_9714 : Nat := 118140960795 + 9714 * 2 ^ 59
def prefixEnd_9714 : Nat := 4983230072969 + 3 ^ 40 * 9714 * 2
def baseEnd_9714 : Nat := 2216867145724545613481

theorem tailTrace_9714 : CollatzResearch.WordTrace tailWord_9714 prefixEnd_9714 2216867145724545613481 := by
  unfold tailWord_9714
  simp only [CollatzResearch.WordTrace]
  refine ⟨88574671703827966057049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 236199124543541242818797 88574671703827966057049)
  ·
    refine ⟨66431003777870974542787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88574671703827966057049 66431003777870974542787)
    ·
      refine ⟨99646505666806461814181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66431003777870974542787 99646505666806461814181)
      ·
        refine ⟨18683719812526211590159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99646505666806461814181 18683719812526211590159)
        ·
          refine ⟨28025579718789317385239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18683719812526211590159 28025579718789317385239)
          ·
            refine ⟨42038369578183976077859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28025579718789317385239 42038369578183976077859)
            ·
              refine ⟨63057554367275964116789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42038369578183976077859 63057554367275964116789)
              ·
                refine ⟨5911645721932121635949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63057554367275964116789 5911645721932121635949)
                ·
                  refine ⟨2216867145724545613481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5911645721932121635949 2216867145724545613481)
                  ·
                    rfl

theorem cell21_9714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_9714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9714 prefixEnd_9714 := by exact prefixLift 9714
  have htrace : WordTrace (prefixWord ++ tailWord_9714) baseStart_9714 baseEnd_9714 := by
    simpa [prefixWord, tailWord_9714, baseEnd_9714] using wordTrace_append hprefix tailTrace_9714
  have hstable : (prefixWord ++ tailWord_9714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9714).length < 2 ^ (prefixWord ++ tailWord_9714).sum := by decide
  have hdescent : baseEnd_9714 < baseStart_9714 := by decide
  rcases family_descends (prefixWord ++ tailWord_9714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9725 : List Nat := [1, 4, 1, 1, 1, 5, 8]
def baseStart_9725 : Nat := 118140960795 + 9725 * 2 ^ 59
def prefixEnd_9725 : Nat := 4983230072969 + 3 ^ 40 * 9725 * 2
def baseEnd_9725 : Nat := 246597499510107881125

theorem tailTrace_9725 : CollatzResearch.WordTrace tailWord_9725 prefixEnd_9725 246597499510107881125 := by
  unfold tailWord_9725
  simp only [CollatzResearch.WordTrace]
  refine ⟨354699889775460742878629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 236466593183640495252419 354699889775460742878629)
  ·
    refine ⟨66506229332898889289743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 354699889775460742878629 66506229332898889289743)
    ·
      refine ⟨99759343999348333934615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66506229332898889289743 99759343999348333934615)
      ·
        refine ⟨149639015999022500901923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99759343999348333934615 149639015999022500901923)
        ·
          refine ⟨224458523998533751352885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149639015999022500901923 224458523998533751352885)
          ·
            refine ⟨21042986624862539189333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 224458523998533751352885 21042986624862539189333)
            ·
              refine ⟨246597499510107881125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 21042986624862539189333 246597499510107881125)
              ·
                rfl

theorem cell21_9725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 8].length) (baseStart_9725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9725 prefixEnd_9725 := by exact prefixLift 9725
  have htrace : WordTrace (prefixWord ++ tailWord_9725) baseStart_9725 baseEnd_9725 := by
    simpa [prefixWord, tailWord_9725, baseEnd_9725] using wordTrace_append hprefix tailTrace_9725
  have hstable : (prefixWord ++ tailWord_9725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9725).length < 2 ^ (prefixWord ++ tailWord_9725).sum := by decide
  have hdescent : baseEnd_9725 < baseStart_9725 := by decide
  rcases family_descends (prefixWord ++ tailWord_9725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9756 : List Nat := [2, 2, 3, 1, 2, 1, 1, 4, 5]
def baseStart_9756 : Nat := 118140960795 + 9756 * 2 ^ 59
def prefixEnd_9756 : Nat := 4983230072969 + 3 ^ 40 * 9756 * 2
def baseEnd_9756 : Nat := 2226452117941805913395

theorem tailTrace_9756 : CollatzResearch.WordTrace tailWord_9756 prefixEnd_9756 2226452117941805913395 := by
  unfold tailWord_9756
  simp only [CollatzResearch.WordTrace]
  refine ⟨177915276331576518628561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 237220368442102024838081 177915276331576518628561)
  ·
    refine ⟨133436457248682388971421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177915276331576518628561 133436457248682388971421)
    ·
      refine ⟨50038671468255895864283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133436457248682388971421 50038671468255895864283)
      ·
        refine ⟨75058007202383843796425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50038671468255895864283 75058007202383843796425)
        ·
          refine ⟨56293505401787882847319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75058007202383843796425 56293505401787882847319)
          ·
            refine ⟨84440258102681824270979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56293505401787882847319 84440258102681824270979)
            ·
              refine ⟨126660387154022736406469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84440258102681824270979 126660387154022736406469)
              ·
                refine ⟨23748822591379263076213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126660387154022736406469 23748822591379263076213)
                ·
                  refine ⟨2226452117941805913395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23748822591379263076213 2226452117941805913395)
                  ·
                    rfl

theorem cell21_9756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_9756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9756 prefixEnd_9756 := by exact prefixLift 9756
  have htrace : WordTrace (prefixWord ++ tailWord_9756) baseStart_9756 baseEnd_9756 := by
    simpa [prefixWord, tailWord_9756, baseEnd_9756] using wordTrace_append hprefix tailTrace_9756
  have hstable : (prefixWord ++ tailWord_9756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9756).length < 2 ^ (prefixWord ++ tailWord_9756).sum := by decide
  have hdescent : baseEnd_9756 < baseStart_9756 := by decide
  rcases family_descends (prefixWord ++ tailWord_9756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9804 : List Nat := [2, 2, 1, 3, 1, 3, 4, 1, 4]
def baseStart_9804 : Nat := 118140960795 + 9804 * 2 ^ 59
def prefixEnd_9804 : Nat := 4983230072969 + 3 ^ 40 * 9804 * 2
def baseEnd_9804 : Nat := 2237406371904389113297

theorem tailTrace_9804 : CollatzResearch.WordTrace tailWord_9804 prefixEnd_9804 2237406371904389113297 := by
  unfold tailWord_9804
  simp only [CollatzResearch.WordTrace]
  refine ⟨178790628244628617502233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 238387504326171490002977 178790628244628617502233)
  ·
    refine ⟨134092971183471463126675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178790628244628617502233 134092971183471463126675)
    ·
      refine ⟨201139456775207194690013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134092971183471463126675 201139456775207194690013)
      ·
        refine ⟨75427296290702698008755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201139456775207194690013 75427296290702698008755)
        ·
          refine ⟨113140944436054047013133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75427296290702698008755 113140944436054047013133)
          ·
            refine ⟨42427854163520267629925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113140944436054047013133 42427854163520267629925)
            ·
              refine ⟨7955222655660050180611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42427854163520267629925 7955222655660050180611)
              ·
                refine ⟨11932833983490075270917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7955222655660050180611 11932833983490075270917)
                ·
                  refine ⟨2237406371904389113297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11932833983490075270917 2237406371904389113297)
                  ·
                    rfl

theorem cell21_9804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_9804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9804 prefixEnd_9804 := by exact prefixLift 9804
  have htrace : WordTrace (prefixWord ++ tailWord_9804) baseStart_9804 baseEnd_9804 := by
    simpa [prefixWord, tailWord_9804, baseEnd_9804] using wordTrace_append hprefix tailTrace_9804
  have hstable : (prefixWord ++ tailWord_9804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9804).length < 2 ^ (prefixWord ++ tailWord_9804).sum := by decide
  have hdescent : baseEnd_9804 < baseStart_9804 := by decide
  rcases family_descends (prefixWord ++ tailWord_9804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9849 : List Nat := [1, 2, 1, 3, 3, 1, 3, 4, 3]
def baseStart_9849 : Nat := 118140960795 + 9849 * 2 ^ 59
def prefixEnd_9849 : Nat := 4983230072969 + 3 ^ 40 * 9849 * 2
def baseEnd_9849 : Nat := 2247675984994310863205

theorem tailTrace_9849 : CollatzResearch.WordTrace tailWord_9849 prefixEnd_9849 2247675984994310863205 := by
  unfold tailWord_9849
  simp only [CollatzResearch.WordTrace]
  refine ⟨359222541326229920392601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 239481694217486613595067 359222541326229920392601)
  ·
    refine ⟨269416905994672440294451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 359222541326229920392601 269416905994672440294451)
    ·
      refine ⟨404125358992008660441677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269416905994672440294451 404125358992008660441677)
      ·
        refine ⟨151547009622003247665629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 404125358992008660441677 151547009622003247665629)
        ·
          refine ⟨56830128608251217874611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151547009622003247665629 56830128608251217874611)
          ·
            refine ⟨85245192912376826811917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56830128608251217874611 85245192912376826811917)
            ·
              refine ⟨31966947342141310054469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85245192912376826811917 31966947342141310054469)
              ·
                refine ⟨5993802626651495635213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31966947342141310054469 5993802626651495635213)
                ·
                  refine ⟨2247675984994310863205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5993802626651495635213 2247675984994310863205)
                  ·
                    rfl

theorem cell21_9849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 3].length) (baseStart_9849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9849 prefixEnd_9849 := by exact prefixLift 9849
  have htrace : WordTrace (prefixWord ++ tailWord_9849) baseStart_9849 baseEnd_9849 := by
    simpa [prefixWord, tailWord_9849, baseEnd_9849] using wordTrace_append hprefix tailTrace_9849
  have hstable : (prefixWord ++ tailWord_9849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9849).length < 2 ^ (prefixWord ++ tailWord_9849).sum := by decide
  have hdescent : baseEnd_9849 < baseStart_9849 := by decide
  rcases family_descends (prefixWord ++ tailWord_9849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9863 : List Nat := [1, 1, 4, 2, 1, 3, 2, 3, 4]
def baseStart_9863 : Nat := 118140960795 + 9863 * 2 ^ 59
def prefixEnd_9863 : Nat := 4983230072969 + 3 ^ 40 * 9863 * 2
def baseEnd_9863 : Nat := 2250870975733397629843

theorem tailTrace_9863 : CollatzResearch.WordTrace tailWord_9863 prefixEnd_9863 2250870975733397629843 := by
  unfold tailWord_9863
  simp only [CollatzResearch.WordTrace]
  refine ⟨359733163275510311402243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 239822108850340207601495 359733163275510311402243)
  ·
    refine ⟨539599744913265467103365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 359733163275510311402243 539599744913265467103365)
    ·
      refine ⟨101174952171237275081881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 539599744913265467103365 101174952171237275081881)
      ·
        refine ⟨75881214128427956311411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101174952171237275081881 75881214128427956311411)
        ·
          refine ⟨113821821192641934467117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75881214128427956311411 113821821192641934467117)
          ·
            refine ⟨42683182947240725425169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113821821192641934467117 42683182947240725425169)
            ·
              refine ⟨32012387210430544068877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42683182947240725425169 32012387210430544068877)
              ·
                refine ⟨12004645203911454025829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32012387210430544068877 12004645203911454025829)
                ·
                  refine ⟨2250870975733397629843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12004645203911454025829 2250870975733397629843)
                  ·
                    rfl

theorem cell21_9863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 4].length) (baseStart_9863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9863 prefixEnd_9863 := by exact prefixLift 9863
  have htrace : WordTrace (prefixWord ++ tailWord_9863) baseStart_9863 baseEnd_9863 := by
    simpa [prefixWord, tailWord_9863, baseEnd_9863] using wordTrace_append hprefix tailTrace_9863
  have hstable : (prefixWord ++ tailWord_9863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9863).length < 2 ^ (prefixWord ++ tailWord_9863).sum := by decide
  have hdescent : baseEnd_9863 < baseStart_9863 := by decide
  rcases family_descends (prefixWord ++ tailWord_9863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9891 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 7]
def baseStart_9891 : Nat := 118140960795 + 9891 * 2 ^ 59
def prefixEnd_9891 : Nat := 4983230072969 + 3 ^ 40 * 9891 * 2
def baseEnd_9891 : Nat := 2257260957211571163119

theorem tailTrace_9891 : CollatzResearch.WordTrace tailWord_9891 prefixEnd_9891 2257260957211571163119 := by
  unfold tailWord_9891
  simp only [CollatzResearch.WordTrace]
  refine ⟨360754407174071093421527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 240502938116047395614351 360754407174071093421527)
  ·
    refine ⟨541131610761106640132291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 360754407174071093421527 541131610761106640132291)
    ·
      refine ⟨811697416141659960198437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 541131610761106640132291 811697416141659960198437)
      ·
        refine ⟨152193265526561242537207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 811697416141659960198437 152193265526561242537207)
        ·
          refine ⟨228289898289841863805811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152193265526561242537207 228289898289841863805811)
          ·
            refine ⟨342434847434762795708717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228289898289841863805811 342434847434762795708717)
            ·
              refine ⟨128413067788036048390769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 342434847434762795708717 128413067788036048390769)
              ·
                refine ⟨96309800841027036293077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128413067788036048390769 96309800841027036293077)
                ·
                  refine ⟨2257260957211571163119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 96309800841027036293077 2257260957211571163119)
                  ·
                    rfl

theorem cell21_9891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 7].length) (baseStart_9891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9891 prefixEnd_9891 := by exact prefixLift 9891
  have htrace : WordTrace (prefixWord ++ tailWord_9891) baseStart_9891 baseEnd_9891 := by
    simpa [prefixWord, tailWord_9891, baseEnd_9891] using wordTrace_append hprefix tailTrace_9891
  have hstable : (prefixWord ++ tailWord_9891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9891).length < 2 ^ (prefixWord ++ tailWord_9891).sum := by decide
  have hdescent : baseEnd_9891 < baseStart_9891 := by decide
  rcases family_descends (prefixWord ++ tailWord_9891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9959 : List Nat := [1, 1, 5, 4, 2, 1, 1, 1, 5]
def baseStart_9959 : Nat := 118140960795 + 9959 * 2 ^ 59
def prefixEnd_9959 : Nat := 4983230072969 + 3 ^ 40 * 9959 * 2
def baseEnd_9959 : Nat := 2272779483658564029647

theorem tailTrace_9959 : CollatzResearch.WordTrace tailWord_9959 prefixEnd_9959 2272779483658564029647 := by
  unfold tailWord_9959
  simp only [CollatzResearch.WordTrace]
  refine ⟨363234570927718706896931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 242156380618479137931287 363234570927718706896931)
  ·
    refine ⟨544851856391578060345397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 363234570927718706896931 544851856391578060345397)
    ·
      refine ⟨51079861536710443157381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 544851856391578060345397 51079861536710443157381)
      ·
        refine ⟨9577474038133208092009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51079861536710443157381 9577474038133208092009)
        ·
          refine ⟨7183105528599906069007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9577474038133208092009 7183105528599906069007)
          ·
            refine ⟨10774658292899859103511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7183105528599906069007 10774658292899859103511)
            ·
              refine ⟨16161987439349788655267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10774658292899859103511 16161987439349788655267)
              ·
                refine ⟨24242981159024682982901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16161987439349788655267 24242981159024682982901)
                ·
                  refine ⟨2272779483658564029647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24242981159024682982901 2272779483658564029647)
                  ·
                    rfl

theorem cell21_9959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 5].length) (baseStart_9959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9959 prefixEnd_9959 := by exact prefixLift 9959
  have htrace : WordTrace (prefixWord ++ tailWord_9959) baseStart_9959 baseEnd_9959 := by
    simpa [prefixWord, tailWord_9959, baseEnd_9959] using wordTrace_append hprefix tailTrace_9959
  have hstable : (prefixWord ++ tailWord_9959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9959).length < 2 ^ (prefixWord ++ tailWord_9959).sum := by decide
  have hdescent : baseEnd_9959 < baseStart_9959 := by decide
  rcases family_descends (prefixWord ++ tailWord_9959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9998 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_9998 : Nat := 118140960795 + 9998 * 2 ^ 59
def prefixEnd_9998 : Nat := 4983230072969 + 3 ^ 40 * 9998 * 2
def baseEnd_9998 : Nat := 2281679815003162879567

theorem tailTrace_9998 : CollatzResearch.WordTrace tailWord_9998 prefixEnd_9998 2281679815003162879567 := by
  unfold tailWord_9998
  simp only [CollatzResearch.WordTrace]
  refine ⟨45582127223303545945831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 243104678524285578377765 45582127223303545945831)
  ·
    refine ⟨68373190834955318918747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45582127223303545945831 68373190834955318918747)
    ·
      refine ⟨102559786252432978378121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68373190834955318918747 102559786252432978378121)
      ·
        refine ⟨76919839689324733783591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102559786252432978378121 76919839689324733783591)
        ·
          refine ⟨115379759533987100675387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76919839689324733783591 115379759533987100675387)
          ·
            refine ⟨173069639300980651013081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115379759533987100675387 173069639300980651013081)
            ·
              refine ⟨129802229475735488259811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173069639300980651013081 129802229475735488259811)
              ·
                refine ⟨194703344213603232389717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129802229475735488259811 194703344213603232389717)
                ·
                  refine ⟨2281679815003162879567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 194703344213603232389717 2281679815003162879567)
                  ·
                    rfl

theorem cell21_9998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_9998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_9998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_9998 prefixEnd_9998 := by exact prefixLift 9998
  have htrace : WordTrace (prefixWord ++ tailWord_9998) baseStart_9998 baseEnd_9998 := by
    simpa [prefixWord, tailWord_9998, baseEnd_9998] using wordTrace_append hprefix tailTrace_9998
  have hstable : (prefixWord ++ tailWord_9998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9998).length < 2 ^ (prefixWord ++ tailWord_9998).sum := by decide
  have hdescent : baseEnd_9998 < baseStart_9998 := by decide
  rcases family_descends (prefixWord ++ tailWord_9998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10004 : List Nat := [2, 4, 4, 1, 2, 8]
def baseStart_10004 : Nat := 118140960795 + 10004 * 2 ^ 59
def prefixEnd_10004 : Nat := 4983230072969 + 3 ^ 40 * 10004 * 2
def baseEnd_10004 : Nat := 84557373953647621465

theorem tailTrace_10004 : CollatzResearch.WordTrace tailWord_10004 prefixEnd_10004 84557373953647621465 := by
  unfold tailWord_10004
  simp only [CollatzResearch.WordTrace]
  refine ⟨182437927882345696142533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 243250570509794261523377 182437927882345696142533)
  ·
    refine ⟨34207111477939818026725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182437927882345696142533 34207111477939818026725)
    ·
      refine ⟨6413833402113715880011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34207111477939818026725 6413833402113715880011)
      ·
        refine ⟨9620750103170573820017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6413833402113715880011 9620750103170573820017)
        ·
          refine ⟨7215562577377930365013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9620750103170573820017 7215562577377930365013)
          ·
            refine ⟨84557373953647621465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 7215562577377930365013 84557373953647621465)
            ·
              rfl

theorem cell21_10004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 8].length) (baseStart_10004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10004 prefixEnd_10004 := by exact prefixLift 10004
  have htrace : WordTrace (prefixWord ++ tailWord_10004) baseStart_10004 baseEnd_10004 := by
    simpa [prefixWord, tailWord_10004, baseEnd_10004] using wordTrace_append hprefix tailTrace_10004
  have hstable : (prefixWord ++ tailWord_10004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10004).length < 2 ^ (prefixWord ++ tailWord_10004).sum := by decide
  have hdescent : baseEnd_10004 < baseStart_10004 := by decide
  rcases family_descends (prefixWord ++ tailWord_10004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10015 : List Nat := [1, 1, 2, 4, 2, 1, 4, 2, 4]
def baseStart_10015 : Nat := 118140960795 + 10015 * 2 ^ 59
def prefixEnd_10015 : Nat := 4983230072969 + 3 ^ 40 * 10015 * 2
def baseEnd_10015 : Nat := 2285559446614911096199

theorem tailTrace_10015 : CollatzResearch.WordTrace tailWord_10015 prefixEnd_10015 2285559446614911096199 := by
  unfold tailWord_10015
  simp only [CollatzResearch.WordTrace]
  refine ⟨365277058724840270935499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 243518039149893513956999 365277058724840270935499)
  ·
    refine ⟨547915588087260406403249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 365277058724840270935499 547915588087260406403249)
    ·
      refine ⟨410936691065445304802437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 547915588087260406403249 410936691065445304802437)
      ·
        refine ⟨77050629574770994650457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 410936691065445304802437 77050629574770994650457)
        ·
          refine ⟨57787972181078245987843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77050629574770994650457 57787972181078245987843)
          ·
            refine ⟨86681958271617368981765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57787972181078245987843 86681958271617368981765)
            ·
              refine ⟨16252867175928256684081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86681958271617368981765 16252867175928256684081)
              ·
                refine ⟨12189650381946192513061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16252867175928256684081 12189650381946192513061)
                ·
                  refine ⟨2285559446614911096199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12189650381946192513061 2285559446614911096199)
                  ·
                    rfl

theorem cell21_10015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 4].length) (baseStart_10015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10015 prefixEnd_10015 := by exact prefixLift 10015
  have htrace : WordTrace (prefixWord ++ tailWord_10015) baseStart_10015 baseEnd_10015 := by
    simpa [prefixWord, tailWord_10015, baseEnd_10015] using wordTrace_append hprefix tailTrace_10015
  have hstable : (prefixWord ++ tailWord_10015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10015).length < 2 ^ (prefixWord ++ tailWord_10015).sum := by decide
  have hdescent : baseEnd_10015 < baseStart_10015 := by decide
  rcases family_descends (prefixWord ++ tailWord_10015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10074 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 6]
def baseStart_10074 : Nat := 118140960795 + 10074 * 2 ^ 59
def prefixEnd_10074 : Nat := 4983230072969 + 3 ^ 40 * 10074 * 2
def baseEnd_10074 : Nat := 2299024050443919612745

theorem tailTrace_10074 : CollatzResearch.WordTrace tailWord_10074 prefixEnd_10074 2299024050443919612745 := by
  unfold tailWord_10074
  simp only [CollatzResearch.WordTrace]
  refine ⟨91857241377773336833319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 244952643674062231555517 91857241377773336833319)
  ·
    refine ⟨137785862066660005249979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91857241377773336833319 137785862066660005249979)
    ·
      refine ⟨206678793099990007874969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137785862066660005249979 206678793099990007874969)
      ·
        refine ⟨155009094824992505906227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206678793099990007874969 155009094824992505906227)
        ·
          refine ⟨232513642237488758859341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155009094824992505906227 232513642237488758859341)
          ·
            refine ⟨87192615839058284572253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232513642237488758859341 87192615839058284572253)
            ·
              refine ⟨32697230939646856714595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87192615839058284572253 32697230939646856714595)
              ·
                refine ⟨49045846409470285071893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32697230939646856714595 49045846409470285071893)
                ·
                  refine ⟨2299024050443919612745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49045846409470285071893 2299024050443919612745)
                  ·
                    rfl

theorem cell21_10074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_10074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10074 prefixEnd_10074 := by exact prefixLift 10074
  have htrace : WordTrace (prefixWord ++ tailWord_10074) baseStart_10074 baseEnd_10074 := by
    simpa [prefixWord, tailWord_10074, baseEnd_10074] using wordTrace_append hprefix tailTrace_10074
  have hstable : (prefixWord ++ tailWord_10074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10074).length < 2 ^ (prefixWord ++ tailWord_10074).sum := by decide
  have hdescent : baseEnd_10074 < baseStart_10074 := by decide
  rcases family_descends (prefixWord ++ tailWord_10074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10122 : List Nat := [3, 1, 2, 4, 2, 2, 7]
def baseStart_10122 : Nat := 118140960795 + 10122 * 2 ^ 59
def prefixEnd_10122 : Nat := 4983230072969 + 3 ^ 40 * 10122 * 2
def baseEnd_10122 : Nat := 256664256045166979183

theorem tailTrace_10122 : CollatzResearch.WordTrace tailWord_10122 prefixEnd_10122 256664256045166979183 := by
  unfold tailWord_10122
  simp only [CollatzResearch.WordTrace]
  refine ⟨92294917334299386270155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 246119779558131696720413 92294917334299386270155)
  ·
    refine ⟨138442376001449079405233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92294917334299386270155 138442376001449079405233)
    ·
      refine ⟨103831782001086809553925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138442376001449079405233 103831782001086809553925)
      ·
        refine ⟨19468459125203776791361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103831782001086809553925 19468459125203776791361)
        ·
          refine ⟨14601344343902832593521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19468459125203776791361 14601344343902832593521)
          ·
            refine ⟨10951008257927124445141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14601344343902832593521 10951008257927124445141)
            ·
              refine ⟨256664256045166979183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10951008257927124445141 256664256045166979183)
              ·
                rfl

theorem cell21_10122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 7].length) (baseStart_10122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10122 prefixEnd_10122 := by exact prefixLift 10122
  have htrace : WordTrace (prefixWord ++ tailWord_10122) baseStart_10122 baseEnd_10122 := by
    simpa [prefixWord, tailWord_10122, baseEnd_10122] using wordTrace_append hprefix tailTrace_10122
  have hstable : (prefixWord ++ tailWord_10122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10122).length < 2 ^ (prefixWord ++ tailWord_10122).sum := by decide
  have hdescent : baseEnd_10122 < baseStart_10122 := by decide
  rcases family_descends (prefixWord ++ tailWord_10122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10271 : List Nat := [1, 1, 2, 4, 1, 2, 1, 4, 5]
def baseStart_10271 : Nat := 118140960795 + 10271 * 2 ^ 59
def prefixEnd_10271 : Nat := 4983230072969 + 3 ^ 40 * 10271 * 2
def baseEnd_10271 : Nat := 2343982134415354829009

theorem tailTrace_10271 : CollatzResearch.WordTrace tailWord_10271 prefixEnd_10271 2343982134415354829009 := by
  unfold tailWord_10271
  simp only [CollatzResearch.WordTrace]
  refine ⟨374614145797395992254667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 249742763864930661503111 374614145797395992254667)
  ·
    refine ⟨561921218696093988382001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 374614145797395992254667 561921218696093988382001)
    ·
      refine ⟨421440914022070491286501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 561921218696093988382001 421440914022070491286501)
      ·
        refine ⟨79020171379138217116219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 421440914022070491286501 79020171379138217116219)
        ·
          refine ⟨118530257068707325674329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79020171379138217116219 118530257068707325674329)
          ·
            refine ⟨88897692801530494255747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118530257068707325674329 88897692801530494255747)
            ·
              refine ⟨133346539202295741383621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88897692801530494255747 133346539202295741383621)
              ·
                refine ⟨25002476100430451509429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133346539202295741383621 25002476100430451509429)
                ·
                  refine ⟨2343982134415354829009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25002476100430451509429 2343982134415354829009)
                  ·
                    rfl

theorem cell21_10271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 5].length) (baseStart_10271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10271 prefixEnd_10271 := by exact prefixLift 10271
  have htrace : WordTrace (prefixWord ++ tailWord_10271) baseStart_10271 baseEnd_10271 := by
    simpa [prefixWord, tailWord_10271, baseEnd_10271] using wordTrace_append hprefix tailTrace_10271
  have hstable : (prefixWord ++ tailWord_10271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10271).length < 2 ^ (prefixWord ++ tailWord_10271).sum := by decide
  have hdescent : baseEnd_10271 < baseStart_10271 := by decide
  rcases family_descends (prefixWord ++ tailWord_10271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10280 : List Nat := [2, 1, 5, 3, 2, 1, 1, 3, 3]
def baseStart_10280 : Nat := 118140960795 + 10280 * 2 ^ 59
def prefixEnd_10280 : Nat := 4983230072969 + 3 ^ 40 * 10280 * 2
def baseEnd_10280 : Nat := 2346036057033339178991

theorem tailTrace_10280 : CollatzResearch.WordTrace tailWord_10280 prefixEnd_10280 2346036057033339178991 := by
  unfold tailWord_10280
  simp only [CollatzResearch.WordTrace]
  refine ⟨187471201382395264666147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 249961601843193686221529 187471201382395264666147)
  ·
    refine ⟨281206802073592896999221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187471201382395264666147 281206802073592896999221)
    ·
      refine ⟨26363137694399334093677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 281206802073592896999221 26363137694399334093677)
      ·
        refine ⟨9886176635399750285129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26363137694399334093677 9886176635399750285129)
        ·
          refine ⟨7414632476549812713847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9886176635399750285129 7414632476549812713847)
          ·
            refine ⟨11121948714824719070771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7414632476549812713847 11121948714824719070771)
            ·
              refine ⟨16682923072237078606157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11121948714824719070771 16682923072237078606157)
              ·
                refine ⟨6256096152088904477309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16682923072237078606157 6256096152088904477309)
                ·
                  refine ⟨2346036057033339178991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6256096152088904477309 2346036057033339178991)
                  ·
                    rfl

theorem cell21_10280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 3].length) (baseStart_10280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10280 prefixEnd_10280 := by exact prefixLift 10280
  have htrace : WordTrace (prefixWord ++ tailWord_10280) baseStart_10280 baseEnd_10280 := by
    simpa [prefixWord, tailWord_10280, baseEnd_10280] using wordTrace_append hprefix tailTrace_10280
  have hstable : (prefixWord ++ tailWord_10280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10280).length < 2 ^ (prefixWord ++ tailWord_10280).sum := by decide
  have hdescent : baseEnd_10280 < baseStart_10280 := by decide
  rcases family_descends (prefixWord ++ tailWord_10280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10305 : List Nat := [1, 2, 5, 1, 2, 3, 1, 1, 5]
def baseStart_10305 : Nat := 118140960795 + 10305 * 2 ^ 59
def prefixEnd_10305 : Nat := 4983230072969 + 3 ^ 40 * 10305 * 2
def baseEnd_10305 : Nat := 2351741397638851262273

theorem tailTrace_10305 : CollatzResearch.WordTrace tailWord_10305 prefixEnd_10305 2351741397638851262273 := by
  unfold tailWord_10305
  simp only [CollatzResearch.WordTrace]
  refine ⟨375854227674219798992369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 250569485116146532661579 375854227674219798992369)
  ·
    refine ⟨281890670755664849244277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 375854227674219798992369 281890670755664849244277)
    ·
      refine ⟨26427250383343579616651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 281890670755664849244277 26427250383343579616651)
      ·
        refine ⟨39640875575015369424977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26427250383343579616651 39640875575015369424977)
        ·
          refine ⟨29730656681261527068733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39640875575015369424977 29730656681261527068733)
          ·
            refine ⟨11148996255473072650775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29730656681261527068733 11148996255473072650775)
            ·
              refine ⟨16723494383209608976163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11148996255473072650775 16723494383209608976163)
              ·
                refine ⟨25085241574814413464245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16723494383209608976163 25085241574814413464245)
                ·
                  refine ⟨2351741397638851262273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25085241574814413464245 2351741397638851262273)
                  ·
                    rfl

theorem cell21_10305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 5].length) (baseStart_10305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10305 prefixEnd_10305 := by exact prefixLift 10305
  have htrace : WordTrace (prefixWord ++ tailWord_10305) baseStart_10305 baseEnd_10305 := by
    simpa [prefixWord, tailWord_10305, baseEnd_10305] using wordTrace_append hprefix tailTrace_10305
  have hstable : (prefixWord ++ tailWord_10305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10305).length < 2 ^ (prefixWord ++ tailWord_10305).sum := by decide
  have hdescent : baseEnd_10305 < baseStart_10305 := by decide
  rcases family_descends (prefixWord ++ tailWord_10305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10316 : List Nat := [2, 2, 1, 3, 1, 1, 3, 8]
def baseStart_10316 : Nat := 118140960795 + 10316 * 2 ^ 59
def prefixEnd_10316 : Nat := 4983230072969 + 3 ^ 40 * 10316 * 2
def baseEnd_10316 : Nat := 784750582501758859639

theorem tailTrace_10316 : CollatzResearch.WordTrace tailWord_10316 prefixEnd_10316 784750582501758859639 := by
  unfold tailWord_10316
  simp only [CollatzResearch.WordTrace]
  refine ⟨188127715317184338821401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 250836953756245785095201 188127715317184338821401)
  ·
    refine ⟨141095786487888254116051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188127715317184338821401 141095786487888254116051)
    ·
      refine ⟨211643679731832381174077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141095786487888254116051 211643679731832381174077)
      ·
        refine ⟨79366379899437142940279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211643679731832381174077 79366379899437142940279)
        ·
          refine ⟨119049569849155714410419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79366379899437142940279 119049569849155714410419)
          ·
            refine ⟨178574354773733571615629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119049569849155714410419 178574354773733571615629)
            ·
              refine ⟨66965383040150089355861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178574354773733571615629 66965383040150089355861)
              ·
                refine ⟨784750582501758859639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 66965383040150089355861 784750582501758859639)
                ·
                  rfl

theorem cell21_10316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 8].length) (baseStart_10316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10316 prefixEnd_10316 := by exact prefixLift 10316
  have htrace : WordTrace (prefixWord ++ tailWord_10316) baseStart_10316 baseEnd_10316 := by
    simpa [prefixWord, tailWord_10316, baseEnd_10316] using wordTrace_append hprefix tailTrace_10316
  have hstable : (prefixWord ++ tailWord_10316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10316).length < 2 ^ (prefixWord ++ tailWord_10316).sum := by decide
  have hdescent : baseEnd_10316 < baseStart_10316 := by decide
  rcases family_descends (prefixWord ++ tailWord_10316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10423 : List Nat := [1, 1, 3, 1, 4, 2, 1, 3, 5]
def baseStart_10423 : Nat := 118140960795 + 10423 * 2 ^ 59
def prefixEnd_10423 : Nat := 4983230072969 + 3 ^ 40 * 10423 * 2
def baseEnd_10423 : Nat := 2378670605296868295365

theorem tailTrace_10423 : CollatzResearch.WordTrace tailWord_10423 prefixEnd_10423 2378670605296868295365 := by
  unfold tailWord_10423
  simp only [CollatzResearch.WordTrace]
  refine ⟨380158041246725951787923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 253438694164483967858615 380158041246725951787923)
  ·
    refine ⟨570237061870088927681885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 380158041246725951787923 570237061870088927681885)
    ·
      refine ⟨213838898201283347880707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 570237061870088927681885 213838898201283347880707)
      ·
        refine ⟨320758347301925021821061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213838898201283347880707 320758347301925021821061)
        ·
          refine ⟨60142190119110941591449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 320758347301925021821061 60142190119110941591449)
          ·
            refine ⟨45106642589333206193587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60142190119110941591449 45106642589333206193587)
            ·
              refine ⟨67659963883999809290381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45106642589333206193587 67659963883999809290381)
              ·
                refine ⟨25372486456499928483893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67659963883999809290381 25372486456499928483893)
                ·
                  refine ⟨2378670605296868295365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25372486456499928483893 2378670605296868295365)
                  ·
                    rfl

theorem cell21_10423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 5].length) (baseStart_10423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10423 prefixEnd_10423 := by exact prefixLift 10423
  have htrace : WordTrace (prefixWord ++ tailWord_10423) baseStart_10423 baseEnd_10423 := by
    simpa [prefixWord, tailWord_10423, baseEnd_10423] using wordTrace_append hprefix tailTrace_10423
  have hstable : (prefixWord ++ tailWord_10423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10423).length < 2 ^ (prefixWord ++ tailWord_10423).sum := by decide
  have hdescent : baseEnd_10423 < baseStart_10423 := by decide
  rcases family_descends (prefixWord ++ tailWord_10423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10533 : List Nat := [1, 3, 1, 2, 5, 1, 1, 4, 3]
def baseStart_10533 : Nat := 118140960795 + 10533 * 2 ^ 59
def prefixEnd_10533 : Nat := 4983230072969 + 3 ^ 40 * 10533 * 2
def baseEnd_10533 : Nat := 2403774103961121461807

theorem tailTrace_10533 : CollatzResearch.WordTrace tailWord_10533 prefixEnd_10533 2403774103961121461807 := by
  unfold tailWord_10533
  simp only [CollatzResearch.WordTrace]
  refine ⟨384170070848214738292253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 256113380565476492194835 384170070848214738292253)
  ·
    refine ⟨144063776568080526859595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 384170070848214738292253 144063776568080526859595)
    ·
      refine ⟨216095664852120790289393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144063776568080526859595 216095664852120790289393)
      ·
        refine ⟨162071748639090592717045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216095664852120790289393 162071748639090592717045)
        ·
          refine ⟨15194226434914743067223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 162071748639090592717045 15194226434914743067223)
          ·
            refine ⟨22791339652372114600835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15194226434914743067223 22791339652372114600835)
            ·
              refine ⟨34187009478558171901253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22791339652372114600835 34187009478558171901253)
              ·
                refine ⟨6410064277229657231485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34187009478558171901253 6410064277229657231485)
                ·
                  refine ⟨2403774103961121461807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6410064277229657231485 2403774103961121461807)
                  ·
                    rfl

theorem cell21_10533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_10533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10533 prefixEnd_10533 := by exact prefixLift 10533
  have htrace : WordTrace (prefixWord ++ tailWord_10533) baseStart_10533 baseEnd_10533 := by
    simpa [prefixWord, tailWord_10533, baseEnd_10533] using wordTrace_append hprefix tailTrace_10533
  have hstable : (prefixWord ++ tailWord_10533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10533).length < 2 ^ (prefixWord ++ tailWord_10533).sum := by decide
  have hdescent : baseEnd_10533 < baseStart_10533 := by decide
  rcases family_descends (prefixWord ++ tailWord_10533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10592 : List Nat := [2, 1, 1, 3, 5, 1, 2, 1, 5]
def baseStart_10592 : Nat := 118140960795 + 10592 * 2 ^ 59
def prefixEnd_10592 : Nat := 4983230072969 + 3 ^ 40 * 10592 * 2
def baseEnd_10592 : Nat := 2417238707790129978353

theorem tailTrace_10592 : CollatzResearch.WordTrace tailWord_10592 prefixEnd_10592 2417238707790129978353 := by
  unfold tailWord_10592
  simp only [CollatzResearch.WordTrace]
  refine ⟨193160988817233907345015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 257547985089645209793353 193160988817233907345015)
  ·
    refine ⟨289741483225850861017523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193160988817233907345015 289741483225850861017523)
    ·
      refine ⟨434612224838776291526285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289741483225850861017523 434612224838776291526285)
      ·
        refine ⟨162979584314541109322357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 434612224838776291526285 162979584314541109322357)
        ·
          refine ⟨15279336029488228998971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 162979584314541109322357 15279336029488228998971)
          ·
            refine ⟨22919004044232343498457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15279336029488228998971 22919004044232343498457)
            ·
              refine ⟨17189253033174257623843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22919004044232343498457 17189253033174257623843)
              ·
                refine ⟨25783879549761386435765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17189253033174257623843 25783879549761386435765)
                ·
                  refine ⟨2417238707790129978353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25783879549761386435765 2417238707790129978353)
                  ·
                    rfl

theorem cell21_10592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_10592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10592 prefixEnd_10592 := by exact prefixLift 10592
  have htrace : WordTrace (prefixWord ++ tailWord_10592) baseStart_10592 baseEnd_10592 := by
    simpa [prefixWord, tailWord_10592, baseEnd_10592] using wordTrace_append hprefix tailTrace_10592
  have hstable : (prefixWord ++ tailWord_10592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10592).length < 2 ^ (prefixWord ++ tailWord_10592).sum := by decide
  have hdescent : baseEnd_10592 < baseStart_10592 := by decide
  rcases family_descends (prefixWord ++ tailWord_10592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10654 : List Nat := [4, 3, 1, 2, 1, 2, 2, 6]
def baseStart_10654 : Nat := 118140960795 + 10654 * 2 ^ 59
def prefixEnd_10654 : Nat := 4983230072969 + 3 ^ 40 * 10654 * 2
def baseEnd_10654 : Nat := 810462650830599981631

theorem tailTrace_10654 : CollatzResearch.WordTrace tailWord_10654 prefixEnd_10654 810462650830599981631 := by
  unfold tailWord_10654
  simp only [CollatzResearch.WordTrace]
  refine ⟨48572912926231550430877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 259055535606568268964677 48572912926231550430877)
  ·
    refine ⟨18214842347336831411579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48572912926231550430877 18214842347336831411579)
    ·
      refine ⟨27322263521005247117369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18214842347336831411579 27322263521005247117369)
      ·
        refine ⟨20491697640753935338027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27322263521005247117369 20491697640753935338027)
        ·
          refine ⟨30737546461130903007041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20491697640753935338027 30737546461130903007041)
          ·
            refine ⟨23053159845848177255281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30737546461130903007041 23053159845848177255281)
            ·
              refine ⟨17289869884386132941461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23053159845848177255281 17289869884386132941461)
              ·
                refine ⟨810462650830599981631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17289869884386132941461 810462650830599981631)
                ·
                  rfl

theorem cell21_10654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_10654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10654 prefixEnd_10654 := by exact prefixLift 10654
  have htrace : WordTrace (prefixWord ++ tailWord_10654) baseStart_10654 baseEnd_10654 := by
    simpa [prefixWord, tailWord_10654, baseEnd_10654] using wordTrace_append hprefix tailTrace_10654
  have hstable : (prefixWord ++ tailWord_10654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10654).length < 2 ^ (prefixWord ++ tailWord_10654).sum := by decide
  have hdescent : baseEnd_10654 < baseStart_10654 := by decide
  rcases family_descends (prefixWord ++ tailWord_10654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10657 : List Nat := [1, 2, 3, 5, 1, 2, 2, 1, 4]
def baseStart_10657 : Nat := 118140960795 + 10657 * 2 ^ 59
def prefixEnd_10657 : Nat := 4983230072969 + 3 ^ 40 * 10657 * 2
def baseEnd_10657 : Nat := 2432072593364461394887

theorem tailTrace_10657 : CollatzResearch.WordTrace tailWord_10657 prefixEnd_10657 2432072593364461394887 := by
  unfold tailWord_10657
  simp only [CollatzResearch.WordTrace]
  refine ⟨388692722398983915806225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 259128481599322610537483 388692722398983915806225)
  ·
    refine ⟨291519541799237936854669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 388692722398983915806225 291519541799237936854669)
    ·
      refine ⟨109319828174714226320501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291519541799237936854669 109319828174714226320501)
      ·
        refine ⟨10248733891379458717547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109319828174714226320501 10248733891379458717547)
        ·
          refine ⟨15373100837069188076321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10248733891379458717547 15373100837069188076321)
          ·
            refine ⟨11529825627801891057241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15373100837069188076321 11529825627801891057241)
            ·
              refine ⟨8647369220851418292931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11529825627801891057241 8647369220851418292931)
              ·
                refine ⟨12971053831277127439397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8647369220851418292931 12971053831277127439397)
                ·
                  refine ⟨2432072593364461394887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12971053831277127439397 2432072593364461394887)
                  ·
                    rfl

theorem cell21_10657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 4].length) (baseStart_10657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10657 prefixEnd_10657 := by exact prefixLift 10657
  have htrace : WordTrace (prefixWord ++ tailWord_10657) baseStart_10657 baseEnd_10657 := by
    simpa [prefixWord, tailWord_10657, baseEnd_10657] using wordTrace_append hprefix tailTrace_10657
  have hstable : (prefixWord ++ tailWord_10657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10657).length < 2 ^ (prefixWord ++ tailWord_10657).sum := by decide
  have hdescent : baseEnd_10657 < baseStart_10657 := by decide
  rcases family_descends (prefixWord ++ tailWord_10657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10727 : List Nat := [1, 1, 5, 2, 1, 1, 3, 2, 5]
def baseStart_10727 : Nat := 118140960795 + 10727 * 2 ^ 59
def prefixEnd_10727 : Nat := 4983230072969 + 3 ^ 40 * 10727 * 2
def baseEnd_10727 : Nat := 2448047547059895228077

theorem tailTrace_10727 : CollatzResearch.WordTrace tailWord_10727 prefixEnd_10727 2448047547059895228077 := by
  unfold tailWord_10727
  simp only [CollatzResearch.WordTrace]
  refine ⟨391245832145385870854435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 260830554763590580569623 391245832145385870854435)
  ·
    refine ⟨586868748218078806281653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 391245832145385870854435 586868748218078806281653)
    ·
      refine ⟨55018945145444888088905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 586868748218078806281653 55018945145444888088905)
      ·
        refine ⟨41264208859083666066679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55018945145444888088905 41264208859083666066679)
        ·
          refine ⟨61896313288625499100019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41264208859083666066679 61896313288625499100019)
          ·
            refine ⟨92844469932938248650029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61896313288625499100019 92844469932938248650029)
            ·
              refine ⟨34816676224851843243761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92844469932938248650029 34816676224851843243761)
              ·
                refine ⟨26112507168638882432821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34816676224851843243761 26112507168638882432821)
                ·
                  refine ⟨2448047547059895228077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26112507168638882432821 2448047547059895228077)
                  ·
                    rfl

theorem cell21_10727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 5].length) (baseStart_10727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10727 prefixEnd_10727 := by exact prefixLift 10727
  have htrace : WordTrace (prefixWord ++ tailWord_10727) baseStart_10727 baseEnd_10727 := by
    simpa [prefixWord, tailWord_10727, baseEnd_10727] using wordTrace_append hprefix tailTrace_10727
  have hstable : (prefixWord ++ tailWord_10727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10727).length < 2 ^ (prefixWord ++ tailWord_10727).sum := by decide
  have hdescent : baseEnd_10727 < baseStart_10727 := by decide
  rcases family_descends (prefixWord ++ tailWord_10727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10744 : List Nat := [2, 1, 2, 1, 1, 4, 4, 3, 3]
def baseStart_10744 : Nat := 118140960795 + 10744 * 2 ^ 59
def prefixEnd_10744 : Nat := 4983230072969 + 3 ^ 40 * 10744 * 2
def baseEnd_10744 : Nat := 2451927178671643444709

theorem tailTrace_10744 : CollatzResearch.WordTrace tailWord_10744 prefixEnd_10744 2451927178671643444709 := by
  unfold tailWord_10744
  simp only [CollatzResearch.WordTrace]
  refine ⟨195932936541898887111643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 261243915389198516148857 195932936541898887111643)
  ·
    refine ⟨293899404812848330667465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195932936541898887111643 293899404812848330667465)
    ·
      refine ⟨220424553609636248000599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293899404812848330667465 220424553609636248000599)
      ·
        refine ⟨330636830414454372000899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220424553609636248000599 330636830414454372000899)
        ·
          refine ⟨495955245621681558001349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330636830414454372000899 495955245621681558001349)
          ·
            refine ⟨92991608554065292125253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 495955245621681558001349 92991608554065292125253)
            ·
              refine ⟨17435926603887242273485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92991608554065292125253 17435926603887242273485)
              ·
                refine ⟨6538472476457715852557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17435926603887242273485 6538472476457715852557)
                ·
                  refine ⟨2451927178671643444709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6538472476457715852557 2451927178671643444709)
                  ·
                    rfl

theorem cell21_10744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 3].length) (baseStart_10744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10744 prefixEnd_10744 := by exact prefixLift 10744
  have htrace : WordTrace (prefixWord ++ tailWord_10744) baseStart_10744 baseEnd_10744 := by
    simpa [prefixWord, tailWord_10744, baseEnd_10744] using wordTrace_append hprefix tailTrace_10744
  have hstable : (prefixWord ++ tailWord_10744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10744).length < 2 ^ (prefixWord ++ tailWord_10744).sum := by decide
  have hdescent : baseEnd_10744 < baseStart_10744 := by decide
  rcases family_descends (prefixWord ++ tailWord_10744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10755 : List Nat := [1, 1, 1, 3, 2, 1, 12]
def baseStart_10755 : Nat := 118140960795 + 10755 * 2 ^ 59
def prefixEnd_10755 : Nat := 4983230072969 + 3 ^ 40 * 10755 * 2
def baseEnd_10755 : Nat := 272715280948674306817

theorem tailTrace_10755 : CollatzResearch.WordTrace tailWord_10755 prefixEnd_10755 272715280948674306817 := by
  unfold tailWord_10755
  simp only [CollatzResearch.WordTrace]
  refine ⟨392267076043946652873719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 261511384029297768582479 392267076043946652873719)
  ·
    refine ⟨588400614065919979310579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 392267076043946652873719 588400614065919979310579)
    ·
      refine ⟨882600921098879968965869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 588400614065919979310579 882600921098879968965869)
      ·
        refine ⟨330975345412079988362201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 882600921098879968965869 330975345412079988362201)
        ·
          refine ⟨248231509059059991271651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330975345412079988362201 248231509059059991271651)
          ·
            refine ⟨372347263588589986907477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248231509059059991271651 372347263588589986907477)
            ·
              refine ⟨272715280948674306817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 372347263588589986907477 272715280948674306817)
              ·
                rfl

theorem cell21_10755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 12].length) (baseStart_10755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10755 prefixEnd_10755 := by exact prefixLift 10755
  have htrace : WordTrace (prefixWord ++ tailWord_10755) baseStart_10755 baseEnd_10755 := by
    simpa [prefixWord, tailWord_10755, baseEnd_10755] using wordTrace_append hprefix tailTrace_10755
  have hstable : (prefixWord ++ tailWord_10755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10755).length < 2 ^ (prefixWord ++ tailWord_10755).sum := by decide
  have hdescent : baseEnd_10755 < baseStart_10755 := by decide
  rcases family_descends (prefixWord ++ tailWord_10755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10831 : List Nat := [1, 1, 2, 1, 1, 2, 5, 8]
def baseStart_10831 : Nat := 118140960795 + 10831 * 2 ^ 59
def prefixEnd_10831 : Nat := 4983230072969 + 3 ^ 40 * 10831 * 2
def baseEnd_10831 : Nat := 823927254659608498177

theorem tailTrace_10831 : CollatzResearch.WordTrace tailWord_10831 prefixEnd_10831 823927254659608498177 := by
  unfold tailWord_10831
  simp only [CollatzResearch.WordTrace]
  refine ⟨395039023768611632640347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 263359349179074421760231 395039023768611632640347)
  ·
    refine ⟨592558535652917448960521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 395039023768611632640347 592558535652917448960521)
    ·
      refine ⟨444418901739688086720391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 592558535652917448960521 444418901739688086720391)
      ·
        refine ⟨666628352609532130080587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444418901739688086720391 666628352609532130080587)
        ·
          refine ⟨999942528914298195120881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666628352609532130080587 999942528914298195120881)
          ·
            refine ⟨749956896685723646340661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 999942528914298195120881 749956896685723646340661)
            ·
              refine ⟨70308459064286591844437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 749956896685723646340661 70308459064286591844437)
              ·
                refine ⟨823927254659608498177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 70308459064286591844437 823927254659608498177)
                ·
                  rfl

theorem cell21_10831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 8].length) (baseStart_10831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10831 prefixEnd_10831 := by exact prefixLift 10831
  have htrace : WordTrace (prefixWord ++ tailWord_10831) baseStart_10831 baseEnd_10831 := by
    simpa [prefixWord, tailWord_10831, baseEnd_10831] using wordTrace_append hprefix tailTrace_10831
  have hstable : (prefixWord ++ tailWord_10831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10831).length < 2 ^ (prefixWord ++ tailWord_10831).sum := by decide
  have hdescent : baseEnd_10831 < baseStart_10831 := by decide
  rcases family_descends (prefixWord ++ tailWord_10831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10834 : List Nat := [3, 2, 2, 1, 2, 1, 3, 3, 4]
def baseStart_10834 : Nat := 118140960795 + 10834 * 2 ^ 59
def prefixEnd_10834 : Nat := 4983230072969 + 3 ^ 40 * 10834 * 2
def baseEnd_10834 : Nat := 2472466404851486944525

theorem tailTrace_10834 : CollatzResearch.WordTrace tailWord_10834 prefixEnd_10834 2472466404851486944525 := by
  unfold tailWord_10834
  simp only [CollatzResearch.WordTrace]
  refine ⟨98787110689435786249889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 263432295171828763333037 98787110689435786249889)
  ·
    refine ⟨74090333017076839687417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98787110689435786249889 74090333017076839687417)
    ·
      refine ⟨55567749762807629765563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74090333017076839687417 55567749762807629765563)
      ·
        refine ⟨83351624644211444648345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55567749762807629765563 83351624644211444648345)
        ·
          refine ⟨62513718483158583486259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83351624644211444648345 62513718483158583486259)
          ·
            refine ⟨93770577724737875229389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62513718483158583486259 93770577724737875229389)
            ·
              refine ⟨35163966646776703211021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93770577724737875229389 35163966646776703211021)
              ·
                refine ⟨13186487492541263704133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35163966646776703211021 13186487492541263704133)
                ·
                  refine ⟨2472466404851486944525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13186487492541263704133 2472466404851486944525)
                  ·
                    rfl

theorem cell21_10834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_10834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10834 prefixEnd_10834 := by exact prefixLift 10834
  have htrace : WordTrace (prefixWord ++ tailWord_10834) baseStart_10834 baseEnd_10834 := by
    simpa [prefixWord, tailWord_10834, baseEnd_10834] using wordTrace_append hprefix tailTrace_10834
  have hstable : (prefixWord ++ tailWord_10834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10834).length < 2 ^ (prefixWord ++ tailWord_10834).sum := by decide
  have hdescent : baseEnd_10834 < baseStart_10834 := by decide
  rcases family_descends (prefixWord ++ tailWord_10834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10910 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_10910 : Nat := 118140960795 + 10910 * 2 ^ 59
def prefixEnd_10910 : Nat := 4983230072969 + 3 ^ 40 * 10910 * 2
def baseEnd_10910 : Nat := 2489810640292243677703

theorem tailTrace_10910 : CollatzResearch.WordTrace tailWord_10910 prefixEnd_10910 2489810640292243677703 := by
  unfold tailWord_10910
  simp only [CollatzResearch.WordTrace]
  refine ⟨49740048810301015595773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 265280260321605416510789 49740048810301015595773)
  ·
    refine ⟨18652518303862880848415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49740048810301015595773 18652518303862880848415)
    ·
      refine ⟨27978777455794321272623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18652518303862880848415 27978777455794321272623)
      ·
        refine ⟨41968166183691481908935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27978777455794321272623 41968166183691481908935)
        ·
          refine ⟨62952249275537222863403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41968166183691481908935 62952249275537222863403)
          ·
            refine ⟨94428373913305834295105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62952249275537222863403 94428373913305834295105)
            ·
              refine ⟨70821280434979375721329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94428373913305834295105 70821280434979375721329)
              ·
                refine ⟨53115960326234531790997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70821280434979375721329 53115960326234531790997)
                ·
                  refine ⟨2489810640292243677703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53115960326234531790997 2489810640292243677703)
                  ·
                    rfl

theorem cell21_10910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_10910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10910 prefixEnd_10910 := by exact prefixLift 10910
  have htrace : WordTrace (prefixWord ++ tailWord_10910) baseStart_10910 baseEnd_10910 := by
    simpa [prefixWord, tailWord_10910, baseEnd_10910] using wordTrace_append hprefix tailTrace_10910
  have hstable : (prefixWord ++ tailWord_10910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10910).length < 2 ^ (prefixWord ++ tailWord_10910).sum := by decide
  have hdescent : baseEnd_10910 < baseStart_10910 := by decide
  rcases family_descends (prefixWord ++ tailWord_10910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10913 : List Nat := [1, 2, 3, 3, 3, 1, 2, 3, 3]
def baseStart_10913 : Nat := 118140960795 + 10913 * 2 ^ 59
def prefixEnd_10913 : Nat := 4983230072969 + 3 ^ 40 * 10913 * 2
def baseEnd_10913 : Nat := 2490495281164905127697

theorem tailTrace_10913 : CollatzResearch.WordTrace tailWord_10913 prefixEnd_10913 2490495281164905127697 := by
  unfold tailWord_10913
  simp only [CollatzResearch.WordTrace]
  refine ⟨398029809471539637125393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 265353206314359758083595 398029809471539637125393)
  ·
    refine ⟨298522357103654727844045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 398029809471539637125393 298522357103654727844045)
    ·
      refine ⟨111945883913870522941517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298522357103654727844045 111945883913870522941517)
      ·
        refine ⟨41979706467701446103069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111945883913870522941517 41979706467701446103069)
        ·
          refine ⟨15742389925388042288651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41979706467701446103069 15742389925388042288651)
          ·
            refine ⟨23613584888082063432977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15742389925388042288651 23613584888082063432977)
            ·
              refine ⟨17710188666061547574733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23613584888082063432977 17710188666061547574733)
              ·
                refine ⟨6641320749773080340525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17710188666061547574733 6641320749773080340525)
                ·
                  refine ⟨2490495281164905127697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6641320749773080340525 2490495281164905127697)
                  ·
                    rfl

theorem cell21_10913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 3].length) (baseStart_10913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10913 prefixEnd_10913 := by exact prefixLift 10913
  have htrace : WordTrace (prefixWord ++ tailWord_10913) baseStart_10913 baseEnd_10913 := by
    simpa [prefixWord, tailWord_10913, baseEnd_10913] using wordTrace_append hprefix tailTrace_10913
  have hstable : (prefixWord ++ tailWord_10913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10913).length < 2 ^ (prefixWord ++ tailWord_10913).sum := by decide
  have hdescent : baseEnd_10913 < baseStart_10913 := by decide
  rcases family_descends (prefixWord ++ tailWord_10913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10989 : List Nat := [1, 5, 1, 2, 1, 1, 5, 2, 3]
def baseStart_10989 : Nat := 118140960795 + 10989 * 2 ^ 59
def prefixEnd_10989 : Nat := 4983230072969 + 3 ^ 40 * 10989 * 2
def baseEnd_10989 : Nat := 2507839516605661860875

theorem tailTrace_10989 : CollatzResearch.WordTrace tailWord_10989 prefixEnd_10989 2507839516605661860875 := by
  unfold tailWord_10989
  simp only [CollatzResearch.WordTrace]
  refine ⟨400801757196204616892021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 267201171464136411261347 400801757196204616892021)
  ·
    refine ⟨37575164737144182833627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 400801757196204616892021 37575164737144182833627)
    ·
      refine ⟨56362747105716274250441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37575164737144182833627 56362747105716274250441)
      ·
        refine ⟨42272060329287205687831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56362747105716274250441 42272060329287205687831)
        ·
          refine ⟨63408090493930808531747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42272060329287205687831 63408090493930808531747)
          ·
            refine ⟨95112135740896212797621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63408090493930808531747 95112135740896212797621)
            ·
              refine ⟨8916762725709019949777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95112135740896212797621 8916762725709019949777)
              ·
                refine ⟨6687572044281764962333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8916762725709019949777 6687572044281764962333)
                ·
                  refine ⟨2507839516605661860875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6687572044281764962333 2507839516605661860875)
                  ·
                    rfl

theorem cell21_10989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_10989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_10989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_10989 prefixEnd_10989 := by exact prefixLift 10989
  have htrace : WordTrace (prefixWord ++ tailWord_10989) baseStart_10989 baseEnd_10989 := by
    simpa [prefixWord, tailWord_10989, baseEnd_10989] using wordTrace_append hprefix tailTrace_10989
  have hstable : (prefixWord ++ tailWord_10989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10989).length < 2 ^ (prefixWord ++ tailWord_10989).sum := by decide
  have hdescent : baseEnd_10989 < baseStart_10989 := by decide
  rcases family_descends (prefixWord ++ tailWord_10989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11048 : List Nat := [2, 1, 5, 1, 1, 1, 3, 4, 3]
def baseStart_11048 : Nat := 118140960795 + 11048 * 2 ^ 59
def prefixEnd_11048 : Nat := 4983230072969 + 3 ^ 40 * 11048 * 2
def baseEnd_11048 : Nat := 2521304120434670377421

theorem tailTrace_11048 : CollatzResearch.WordTrace tailWord_11048 prefixEnd_11048 2521304120434670377421 := by
  unfold tailWord_11048
  simp only [CollatzResearch.WordTrace]
  refine ⟨201476831991228846644899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 268635775988305128859865 201476831991228846644899)
  ·
    refine ⟨302215247986843269967349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201476831991228846644899 302215247986843269967349)
    ·
      refine ⟨28332679498766556559439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 302215247986843269967349 28332679498766556559439)
      ·
        refine ⟨42499019248149834839159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28332679498766556559439 42499019248149834839159)
        ·
          refine ⟨63748528872224752258739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42499019248149834839159 63748528872224752258739)
          ·
            refine ⟨95622793308337128388109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63748528872224752258739 95622793308337128388109)
            ·
              refine ⟨35858547490626423145541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95622793308337128388109 35858547490626423145541)
              ·
                refine ⟨6723477654492454339789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35858547490626423145541 6723477654492454339789)
                ·
                  refine ⟨2521304120434670377421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6723477654492454339789 2521304120434670377421)
                  ·
                    rfl

theorem cell21_11048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 3].length) (baseStart_11048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11048 prefixEnd_11048 := by exact prefixLift 11048
  have htrace : WordTrace (prefixWord ++ tailWord_11048) baseStart_11048 baseEnd_11048 := by
    simpa [prefixWord, tailWord_11048, baseEnd_11048] using wordTrace_append hprefix tailTrace_11048
  have hstable : (prefixWord ++ tailWord_11048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11048).length < 2 ^ (prefixWord ++ tailWord_11048).sum := by decide
  have hdescent : baseEnd_11048 < baseStart_11048 := by decide
  rcases family_descends (prefixWord ++ tailWord_11048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11090 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 7]
def baseStart_11090 : Nat := 118140960795 + 11090 * 2 ^ 59
def prefixEnd_11090 : Nat := 4983230072969 + 3 ^ 40 * 11090 * 2
def baseEnd_11090 : Nat := 2530889092651930677335

theorem tailTrace_11090 : CollatzResearch.WordTrace tailWord_11090 prefixEnd_11090 2530889092651930677335 := by
  unfold tailWord_11090
  simp only [CollatzResearch.WordTrace]
  refine ⟨101121382457574716579681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 269657019886865910879149 101121382457574716579681)
  ·
    refine ⟨75841036843181037434761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101121382457574716579681 75841036843181037434761)
    ·
      refine ⟨56880777632385778076071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75841036843181037434761 56880777632385778076071)
      ·
        refine ⟨85321166448578667114107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56880777632385778076071 85321166448578667114107)
        ·
          refine ⟨127981749672868000671161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85321166448578667114107 127981749672868000671161)
          ·
            refine ⟨95986312254651000503371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127981749672868000671161 95986312254651000503371)
            ·
              refine ⟨143979468381976500755057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95986312254651000503371 143979468381976500755057)
              ·
                refine ⟨107984601286482375566293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143979468381976500755057 107984601286482375566293)
                ·
                  refine ⟨2530889092651930677335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 107984601286482375566293 2530889092651930677335)
                  ·
                    rfl

theorem cell21_11090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_11090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11090 prefixEnd_11090 := by exact prefixLift 11090
  have htrace : WordTrace (prefixWord ++ tailWord_11090) baseStart_11090 baseEnd_11090 := by
    simpa [prefixWord, tailWord_11090, baseEnd_11090] using wordTrace_append hprefix tailTrace_11090
  have hstable : (prefixWord ++ tailWord_11090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11090).length < 2 ^ (prefixWord ++ tailWord_11090).sum := by decide
  have hdescent : baseEnd_11090 < baseStart_11090 := by decide
  rcases family_descends (prefixWord ++ tailWord_11090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11107 : List Nat := [1, 1, 1, 5, 3, 2, 2, 1, 5]
def baseStart_11107 : Nat := 118140960795 + 11107 * 2 ^ 59
def prefixEnd_11107 : Nat := 4983230072969 + 3 ^ 40 * 11107 * 2
def baseEnd_11107 : Nat := 2534768724263678893967

theorem tailTrace_11107 : CollatzResearch.WordTrace tailWord_11107 prefixEnd_11107 2534768724263678893967 := by
  unfold tailWord_11107
  simp only [CollatzResearch.WordTrace]
  refine ⟨405105570768710769687575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 270070380512473846458383 405105570768710769687575)
  ·
    refine ⟨607658356153066154531363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 405105570768710769687575 607658356153066154531363)
    ·
      refine ⟨911487534229599231797045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 607658356153066154531363 911487534229599231797045)
      ·
        refine ⟨85451956334024927980973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 911487534229599231797045 85451956334024927980973)
        ·
          refine ⟨32044483625259347992865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85451956334024927980973 32044483625259347992865)
          ·
            refine ⟨24033362718944510994649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32044483625259347992865 24033362718944510994649)
            ·
              refine ⟨18025022039208383245987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24033362718944510994649 18025022039208383245987)
              ·
                refine ⟨27037533058812574868981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18025022039208383245987 27037533058812574868981)
                ·
                  refine ⟨2534768724263678893967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27037533058812574868981 2534768724263678893967)
                  ·
                    rfl

theorem cell21_11107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 5].length) (baseStart_11107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11107 prefixEnd_11107 := by exact prefixLift 11107
  have htrace : WordTrace (prefixWord ++ tailWord_11107) baseStart_11107 baseEnd_11107 := by
    simpa [prefixWord, tailWord_11107, baseEnd_11107] using wordTrace_append hprefix tailTrace_11107
  have hstable : (prefixWord ++ tailWord_11107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11107).length < 2 ^ (prefixWord ++ tailWord_11107).sum := by decide
  have hdescent : baseEnd_11107 < baseStart_11107 := by decide
  rcases family_descends (prefixWord ++ tailWord_11107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11158 : List Nat := [5, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_11158 : Nat := 118140960795 + 11158 * 2 ^ 59
def prefixEnd_11158 : Nat := 4983230072969 + 3 ^ 40 * 11158 * 2
def baseEnd_11158 : Nat := 2546407619098923543863

theorem tailTrace_11158 : CollatzResearch.WordTrace tailWord_11158 prefixEnd_11158 2546407619098923543863 := by
  unfold tailWord_11158
  simp only [CollatzResearch.WordTrace]
  refine ⟨25435355848996654987133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 271310462389297653196085 25435355848996654987133)
  ·
    refine ⟨9538258443373745620175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25435355848996654987133 9538258443373745620175)
    ·
      refine ⟨14307387665060618430263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9538258443373745620175 14307387665060618430263)
      ·
        refine ⟨21461081497590927645395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14307387665060618430263 21461081497590927645395)
        ·
          refine ⟨32191622246386391468093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21461081497590927645395 32191622246386391468093)
          ·
            refine ⟨12071858342394896800535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32191622246386391468093 12071858342394896800535)
            ·
              refine ⟨18107787513592345200803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12071858342394896800535 18107787513592345200803)
              ·
                refine ⟨27161681270388517801205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18107787513592345200803 27161681270388517801205)
                ·
                  refine ⟨2546407619098923543863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27161681270388517801205 2546407619098923543863)
                  ·
                    rfl

theorem cell21_11158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_11158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11158 prefixEnd_11158 := by exact prefixLift 11158
  have htrace : WordTrace (prefixWord ++ tailWord_11158) baseStart_11158 baseEnd_11158 := by
    simpa [prefixWord, tailWord_11158, baseEnd_11158] using wordTrace_append hprefix tailTrace_11158
  have hstable : (prefixWord ++ tailWord_11158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11158).length < 2 ^ (prefixWord ++ tailWord_11158).sum := by decide
  have hdescent : baseEnd_11158 < baseStart_11158 := by decide
  rcases family_descends (prefixWord ++ tailWord_11158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11206 : List Nat := [6, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_11206 : Nat := 118140960795 + 11206 * 2 ^ 59
def prefixEnd_11206 : Nat := 4983230072969 + 3 ^ 40 * 11206 * 2
def baseEnd_11206 : Nat := 2557361873061506743765

theorem tailTrace_11206 : CollatzResearch.WordTrace tailWord_11206 prefixEnd_11206 2557361873061506743765 := by
  unfold tailWord_11206
  simp only [CollatzResearch.WordTrace]
  refine ⟨12772387419064083673171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 272477598273367118360981 12772387419064083673171)
  ·
    refine ⟨19158581128596125509757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12772387419064083673171 19158581128596125509757)
    ·
      refine ⟨7184467923223547066159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19158581128596125509757 7184467923223547066159)
      ·
        refine ⟨10776701884835320599239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7184467923223547066159 10776701884835320599239)
        ·
          refine ⟨16165052827252980898859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10776701884835320599239 16165052827252980898859)
          ·
            refine ⟨24247579240879471348289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16165052827252980898859 24247579240879471348289)
            ·
              refine ⟨18185684430659603511217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24247579240879471348289 18185684430659603511217)
              ·
                refine ⟨13639263322994702633413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18185684430659603511217 13639263322994702633413)
                ·
                  refine ⟨2557361873061506743765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13639263322994702633413 2557361873061506743765)
                  ·
                    rfl

theorem cell21_11206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_11206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11206 prefixEnd_11206 := by exact prefixLift 11206
  have htrace : WordTrace (prefixWord ++ tailWord_11206) baseStart_11206 baseEnd_11206 := by
    simpa [prefixWord, tailWord_11206, baseEnd_11206] using wordTrace_append hprefix tailTrace_11206
  have hstable : (prefixWord ++ tailWord_11206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11206).length < 2 ^ (prefixWord ++ tailWord_11206).sum := by decide
  have hdescent : baseEnd_11206 < baseStart_11206 := by decide
  rcases family_descends (prefixWord ++ tailWord_11206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11214 : List Nat := [4, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_11214 : Nat := 118140960795 + 11214 * 2 ^ 59
def prefixEnd_11214 : Nat := 4983230072969 + 3 ^ 40 * 11214 * 2
def baseEnd_11214 : Nat := 2559187582055270610415

theorem tailTrace_11214 : CollatzResearch.WordTrace tailWord_11214 prefixEnd_11214 2559187582055270610415 := by
  unfold tailWord_11214
  simp only [CollatzResearch.WordTrace]
  refine ⟨51126022672633505479087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 272672120920712029221797 51126022672633505479087)
  ·
    refine ⟨76689034008950258218631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51126022672633505479087 76689034008950258218631)
    ·
      refine ⟨115033551013425387327947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76689034008950258218631 115033551013425387327947)
      ·
        refine ⟨172550326520138080991921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115033551013425387327947 172550326520138080991921)
        ·
          refine ⟨129412744890103560743941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172550326520138080991921 129412744890103560743941)
          ·
            refine ⟨24264889666894417639489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129412744890103560743941 24264889666894417639489)
            ·
              refine ⟨18198667250170813229617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24264889666894417639489 18198667250170813229617)
              ·
                refine ⟨13649000437628109922213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18198667250170813229617 13649000437628109922213)
                ·
                  refine ⟨2559187582055270610415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13649000437628109922213 2559187582055270610415)
                  ·
                    rfl

theorem cell21_11214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_11214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11214 prefixEnd_11214 := by exact prefixLift 11214
  have htrace : WordTrace (prefixWord ++ tailWord_11214) baseStart_11214 baseEnd_11214 := by
    simpa [prefixWord, tailWord_11214, baseEnd_11214] using wordTrace_append hprefix tailTrace_11214
  have hstable : (prefixWord ++ tailWord_11214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11214).length < 2 ^ (prefixWord ++ tailWord_11214).sum := by decide
  have hdescent : baseEnd_11214 < baseStart_11214 := by decide
  rcases family_descends (prefixWord ++ tailWord_11214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11242 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 7]
def baseStart_11242 : Nat := 118140960795 + 11242 * 2 ^ 59
def prefixEnd_11242 : Nat := 4983230072969 + 3 ^ 40 * 11242 * 2
def baseEnd_11242 : Nat := 2565577563533444143691

theorem tailTrace_11242 : CollatzResearch.WordTrace tailWord_11242 prefixEnd_11242 2565577563533444143691 := by
  unfold tailWord_11242
  simp only [CollatzResearch.WordTrace]
  refine ⟨102507356319907206462995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 273352950186419217234653 102507356319907206462995)
  ·
    refine ⟨153761034479860809694493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102507356319907206462995 153761034479860809694493)
    ·
      refine ⟨57660387929947803635435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153761034479860809694493 57660387929947803635435)
      ·
        refine ⟨86490581894921705453153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57660387929947803635435 86490581894921705453153)
        ·
          refine ⟨64867936421191279089865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86490581894921705453153 64867936421191279089865)
          ·
            refine ⟨48650952315893459317399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64867936421191279089865 48650952315893459317399)
            ·
              refine ⟨72976428473840188976099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48650952315893459317399 72976428473840188976099)
              ·
                refine ⟨109464642710760283464149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72976428473840188976099 109464642710760283464149)
                ·
                  refine ⟨2565577563533444143691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 109464642710760283464149 2565577563533444143691)
                  ·
                    rfl

theorem cell21_11242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_11242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11242 prefixEnd_11242 := by exact prefixLift 11242
  have htrace : WordTrace (prefixWord ++ tailWord_11242) baseStart_11242 baseEnd_11242 := by
    simpa [prefixWord, tailWord_11242, baseEnd_11242] using wordTrace_append hprefix tailTrace_11242
  have hstable : (prefixWord ++ tailWord_11242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11242).length < 2 ^ (prefixWord ++ tailWord_11242).sum := by decide
  have hdescent : baseEnd_11242 < baseStart_11242 := by decide
  rcases family_descends (prefixWord ++ tailWord_11242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11256 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 6]
def baseStart_11256 : Nat := 118140960795 + 11256 * 2 ^ 59
def prefixEnd_11256 : Nat := 4983230072969 + 3 ^ 40 * 11256 * 2
def baseEnd_11256 : Nat := 2568772554272530910329

theorem tailTrace_11256 : CollatzResearch.WordTrace tailWord_11256 prefixEnd_11256 2568772554272530910329 := by
  unfold tailWord_11256
  simp only [CollatzResearch.WordTrace]
  refine ⟨205270023614454608430811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 273693364819272811241081 205270023614454608430811)
  ·
    refine ⟨307905035421681912646217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205270023614454608430811 307905035421681912646217)
    ·
      refine ⟨230928776566261434484663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307905035421681912646217 230928776566261434484663)
      ·
        refine ⟨346393164849392151726995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230928776566261434484663 346393164849392151726995)
        ·
          refine ⟨519589747274088227590493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346393164849392151726995 519589747274088227590493)
          ·
            refine ⟨194846155227783085346435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 519589747274088227590493 194846155227783085346435)
            ·
              refine ⟨292269232841674628019653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194846155227783085346435 292269232841674628019653)
              ·
                refine ⟨54800481157813992753685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 292269232841674628019653 54800481157813992753685)
                ·
                  refine ⟨2568772554272530910329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54800481157813992753685 2568772554272530910329)
                  ·
                    rfl

theorem cell21_11256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_11256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11256 prefixEnd_11256 := by exact prefixLift 11256
  have htrace : WordTrace (prefixWord ++ tailWord_11256) baseStart_11256 baseEnd_11256 := by
    simpa [prefixWord, tailWord_11256, baseEnd_11256] using wordTrace_append hprefix tailTrace_11256
  have hstable : (prefixWord ++ tailWord_11256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11256).length < 2 ^ (prefixWord ++ tailWord_11256).sum := by decide
  have hdescent : baseEnd_11256 < baseStart_11256 := by decide
  rcases family_descends (prefixWord ++ tailWord_11256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11290 : List Nat := [3, 1, 1, 3, 1, 2, 5, 1, 4]
def baseStart_11290 : Nat := 118140960795 + 11290 * 2 ^ 59
def prefixEnd_11290 : Nat := 4983230072969 + 3 ^ 40 * 11290 * 2
def baseEnd_11290 : Nat := 2576531817496027343593

theorem tailTrace_11290 : CollatzResearch.WordTrace tailWord_11290 prefixEnd_11290 2576531817496027343593 := by
  unfold tailWord_11290
  simp only [CollatzResearch.WordTrace]
  refine ⟨102945032276433255899831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 274520086070488682399549 102945032276433255899831)
  ·
    refine ⟨154417548414649883849747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102945032276433255899831 154417548414649883849747)
    ·
      refine ⟨231626322621974825774621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154417548414649883849747 231626322621974825774621)
      ·
        refine ⟨86859870983240559665483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231626322621974825774621 86859870983240559665483)
        ·
          refine ⟨130289806474860839498225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86859870983240559665483 130289806474860839498225)
          ·
            refine ⟨97717354856145629623669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130289806474860839498225 97717354856145629623669)
            ·
              refine ⟨9161002017763652777219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97717354856145629623669 9161002017763652777219)
              ·
                refine ⟨13741503026645479165829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9161002017763652777219 13741503026645479165829)
                ·
                  refine ⟨2576531817496027343593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13741503026645479165829 2576531817496027343593)
                  ·
                    rfl

theorem cell21_11290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_11290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11290 prefixEnd_11290 := by exact prefixLift 11290
  have htrace : WordTrace (prefixWord ++ tailWord_11290) baseStart_11290 baseEnd_11290 := by
    simpa [prefixWord, tailWord_11290, baseEnd_11290] using wordTrace_append hprefix tailTrace_11290
  have hstable : (prefixWord ++ tailWord_11290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11290).length < 2 ^ (prefixWord ++ tailWord_11290).sum := by decide
  have hdescent : baseEnd_11290 < baseStart_11290 := by decide
  rcases family_descends (prefixWord ++ tailWord_11290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11335 : List Nat := [1, 1, 4, 1, 3, 4, 1, 1, 5]
def baseStart_11335 : Nat := 118140960795 + 11335 * 2 ^ 59
def prefixEnd_11335 : Nat := 4983230072969 + 3 ^ 40 * 11335 * 2
def baseEnd_11335 : Nat := 2586801430585949093501

theorem tailTrace_11335 : CollatzResearch.WordTrace tailWord_11335 prefixEnd_11335 2586801430585949093501 := by
  unfold tailWord_11335
  simp only [CollatzResearch.WordTrace]
  refine ⟨413421413942705708987459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 275614275961803805991639 413421413942705708987459)
  ·
    refine ⟨620132120914058563481189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 413421413942705708987459 620132120914058563481189)
    ·
      refine ⟨116274772671385980652723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 620132120914058563481189 116274772671385980652723)
      ·
        refine ⟨174412159007078970979085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116274772671385980652723 174412159007078970979085)
        ·
          refine ⟨65404559627654614117157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174412159007078970979085 65404559627654614117157)
          ·
            refine ⟨12263354930185240146967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65404559627654614117157 12263354930185240146967)
            ·
              refine ⟨18395032395277860220451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12263354930185240146967 18395032395277860220451)
              ·
                refine ⟨27592548592916790330677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18395032395277860220451 27592548592916790330677)
                ·
                  refine ⟨2586801430585949093501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27592548592916790330677 2586801430585949093501)
                  ·
                    rfl

theorem cell21_11335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 5].length) (baseStart_11335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11335 prefixEnd_11335 := by exact prefixLift 11335
  have htrace : WordTrace (prefixWord ++ tailWord_11335) baseStart_11335 baseEnd_11335 := by
    simpa [prefixWord, tailWord_11335, baseEnd_11335] using wordTrace_append hprefix tailTrace_11335
  have hstable : (prefixWord ++ tailWord_11335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11335).length < 2 ^ (prefixWord ++ tailWord_11335).sum := by decide
  have hdescent : baseEnd_11335 < baseStart_11335 := by decide
  rcases family_descends (prefixWord ++ tailWord_11335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11349 : List Nat := [1, 3, 2, 2, 1, 2, 3, 3, 4]
def baseStart_11349 : Nat := 118140960795 + 11349 * 2 ^ 59
def prefixEnd_11349 : Nat := 4983230072969 + 3 ^ 40 * 11349 * 2
def baseEnd_11349 : Nat := 2589996421325035860139

theorem tailTrace_11349 : CollatzResearch.WordTrace tailWord_11349 prefixEnd_11349 2589996421325035860139 := by
  unfold tailWord_11349
  simp only [CollatzResearch.WordTrace]
  refine ⟨413932035891986099997101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 275954690594657399998067 413932035891986099997101)
  ·
    refine ⟨155224513459494787498913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 413932035891986099997101 155224513459494787498913)
    ·
      refine ⟨116418385094621090624185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155224513459494787498913 116418385094621090624185)
      ·
        refine ⟨87313788820965817968139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116418385094621090624185 87313788820965817968139)
        ·
          refine ⟨130970683231448726952209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87313788820965817968139 130970683231448726952209)
          ·
            refine ⟨98228012423586545214157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130970683231448726952209 98228012423586545214157)
            ·
              refine ⟨36835504658844954455309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98228012423586545214157 36835504658844954455309)
              ·
                refine ⟨13813314247066857920741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36835504658844954455309 13813314247066857920741)
                ·
                  refine ⟨2589996421325035860139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13813314247066857920741 2589996421325035860139)
                  ·
                    rfl

theorem cell21_11349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_11349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11349 prefixEnd_11349 := by exact prefixLift 11349
  have htrace : WordTrace (prefixWord ++ tailWord_11349) baseStart_11349 baseEnd_11349 := by
    simpa [prefixWord, tailWord_11349, baseEnd_11349] using wordTrace_append hprefix tailTrace_11349
  have hstable : (prefixWord ++ tailWord_11349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11349).length < 2 ^ (prefixWord ++ tailWord_11349).sum := by decide
  have hdescent : baseEnd_11349 < baseStart_11349 := by decide
  rcases family_descends (prefixWord ++ tailWord_11349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11377 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 9]
def baseStart_11377 : Nat := 118140960795 + 11377 * 2 ^ 59
def prefixEnd_11377 : Nat := 4983230072969 + 3 ^ 40 * 11377 * 2
def baseEnd_11377 : Nat := 2596386402803209393415

theorem tailTrace_11377 : CollatzResearch.WordTrace tailWord_11377 prefixEnd_11377 2596386402803209393415 := by
  unfold tailWord_11377
  simp only [CollatzResearch.WordTrace]
  refine ⟨414953279790546882016385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 276635519860364588010923 414953279790546882016385)
  ·
    refine ⟨311214959842910161512289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 414953279790546882016385 311214959842910161512289)
    ·
      refine ⟨233411219882182621134217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311214959842910161512289 233411219882182621134217)
      ·
        refine ⟨175058414911636965850663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233411219882182621134217 175058414911636965850663)
        ·
          refine ⟨262587622367455448775995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175058414911636965850663 262587622367455448775995)
          ·
            refine ⟨393881433551183173163993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262587622367455448775995 393881433551183173163993)
            ·
              refine ⟨295411075163387379872995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393881433551183173163993 295411075163387379872995)
              ·
                refine ⟨443116612745081069809493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295411075163387379872995 443116612745081069809493)
                ·
                  refine ⟨2596386402803209393415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 443116612745081069809493 2596386402803209393415)
                  ·
                    rfl

theorem cell21_11377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_11377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11377 prefixEnd_11377 := by exact prefixLift 11377
  have htrace : WordTrace (prefixWord ++ tailWord_11377) baseStart_11377 baseEnd_11377 := by
    simpa [prefixWord, tailWord_11377, baseEnd_11377] using wordTrace_append hprefix tailTrace_11377
  have hstable : (prefixWord ++ tailWord_11377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11377).length < 2 ^ (prefixWord ++ tailWord_11377).sum := by decide
  have hdescent : baseEnd_11377 < baseStart_11377 := by decide
  rcases family_descends (prefixWord ++ tailWord_11377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11397 : List Nat := [1, 3, 1, 1, 7, 1, 1, 6]
def baseStart_11397 : Nat := 118140960795 + 11397 * 2 ^ 59
def prefixEnd_11397 : Nat := 4983230072969 + 3 ^ 40 * 11397 * 2
def baseEnd_11397 : Nat := 866983558429206353347

theorem tailTrace_11397 : CollatzResearch.WordTrace tailWord_11397 prefixEnd_11397 866983558429206353347 := by
  unfold tailWord_11397
  simp only [CollatzResearch.WordTrace]
  refine ⟨415682739718090297744445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 277121826478726865162963 415682739718090297744445)
  ·
    refine ⟨155881027394283861654167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 415682739718090297744445 155881027394283861654167)
    ·
      refine ⟨233821541091425792481251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155881027394283861654167 233821541091425792481251)
      ·
        refine ⟨350732311637138688721877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233821541091425792481251 350732311637138688721877)
        ·
          refine ⟨8220288553995438016919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 350732311637138688721877 8220288553995438016919)
          ·
            refine ⟨12330432830993157025379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8220288553995438016919 12330432830993157025379)
            ·
              refine ⟨18495649246489735538069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12330432830993157025379 18495649246489735538069)
              ·
                refine ⟨866983558429206353347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18495649246489735538069 866983558429206353347)
                ·
                  rfl

theorem cell21_11397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 6].length) (baseStart_11397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11397 prefixEnd_11397 := by exact prefixLift 11397
  have htrace : WordTrace (prefixWord ++ tailWord_11397) baseStart_11397 baseEnd_11397 := by
    simpa [prefixWord, tailWord_11397, baseEnd_11397] using wordTrace_append hprefix tailTrace_11397
  have hstable : (prefixWord ++ tailWord_11397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11397).length < 2 ^ (prefixWord ++ tailWord_11397).sum := by decide
  have hdescent : baseEnd_11397 < baseStart_11397 := by decide
  rcases family_descends (prefixWord ++ tailWord_11397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11428 : List Nat := [2, 3, 1, 2, 3, 2, 2, 3, 3]
def baseStart_11428 : Nat := 118140960795 + 11428 * 2 ^ 59
def prefixEnd_11428 : Nat := 4983230072969 + 3 ^ 40 * 11428 * 2
def baseEnd_11428 : Nat := 2608025297638454043311

theorem tailTrace_11428 : CollatzResearch.WordTrace tailWord_11428 prefixEnd_11428 2608025297638454043311 := by
  unfold tailWord_11428
  simp only [CollatzResearch.WordTrace]
  refine ⟨208406701302891296061469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 277875601737188394748625 208406701302891296061469)
  ·
    refine ⟨78152512988584236023051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208406701302891296061469 78152512988584236023051)
    ·
      refine ⟨117228769482876354034577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78152512988584236023051 117228769482876354034577)
      ·
        refine ⟨87921577112157265525933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117228769482876354034577 87921577112157265525933)
        ·
          refine ⟨32970591417058974572225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87921577112157265525933 32970591417058974572225)
          ·
            refine ⟨24727943562794230929169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32970591417058974572225 24727943562794230929169)
            ·
              refine ⟨18545957672095673196877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24727943562794230929169 18545957672095673196877)
              ·
                refine ⟨6954734127035877448829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18545957672095673196877 6954734127035877448829)
                ·
                  refine ⟨2608025297638454043311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6954734127035877448829 2608025297638454043311)
                  ·
                    rfl

theorem cell21_11428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_11428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11428 prefixEnd_11428 := by exact prefixLift 11428
  have htrace : WordTrace (prefixWord ++ tailWord_11428) baseStart_11428 baseEnd_11428 := by
    simpa [prefixWord, tailWord_11428, baseEnd_11428] using wordTrace_append hprefix tailTrace_11428
  have hstable : (prefixWord ++ tailWord_11428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11428).length < 2 ^ (prefixWord ++ tailWord_11428).sum := by decide
  have hdescent : baseEnd_11428 < baseStart_11428 := by decide
  rcases family_descends (prefixWord ++ tailWord_11428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11442 : List Nat := [3, 2, 1, 1, 1, 6, 1, 2, 4]
def baseStart_11442 : Nat := 118140960795 + 11442 * 2 ^ 59
def prefixEnd_11442 : Nat := 4983230072969 + 3 ^ 40 * 11442 * 2
def baseEnd_11442 : Nat := 2611220288377540809949

theorem tailTrace_11442 : CollatzResearch.WordTrace tailWord_11442 prefixEnd_11442 2611220288377540809949 := by
  unfold tailWord_11442
  simp only [CollatzResearch.WordTrace]
  refine ⟨104331006138765745783145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 278216016370041988755053 104331006138765745783145)
  ·
    refine ⟨78248254604074309337359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104331006138765745783145 78248254604074309337359)
    ·
      refine ⟨117372381906111464006039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78248254604074309337359 117372381906111464006039)
      ·
        refine ⟨176058572859167196009059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117372381906111464006039 176058572859167196009059)
        ·
          refine ⟨264087859288750794013589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176058572859167196009059 264087859288750794013589)
          ·
            refine ⟨12379118404160193469387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 264087859288750794013589 12379118404160193469387)
            ·
              refine ⟨18568677606240290204081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12379118404160193469387 18568677606240290204081)
              ·
                refine ⟨13926508204680217653061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18568677606240290204081 13926508204680217653061)
                ·
                  refine ⟨2611220288377540809949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13926508204680217653061 2611220288377540809949)
                  ·
                    rfl

theorem cell21_11442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_11442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11442 prefixEnd_11442 := by exact prefixLift 11442
  have htrace : WordTrace (prefixWord ++ tailWord_11442) baseStart_11442 baseEnd_11442 := by
    simpa [prefixWord, tailWord_11442, baseEnd_11442] using wordTrace_append hprefix tailTrace_11442
  have hstable : (prefixWord ++ tailWord_11442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11442).length < 2 ^ (prefixWord ++ tailWord_11442).sum := by decide
  have hdescent : baseEnd_11442 < baseStart_11442 := by decide
  rcases family_descends (prefixWord ++ tailWord_11442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11487 : List Nat := [1, 1, 2, 3, 2, 1, 5, 3, 3]
def baseStart_11487 : Nat := 118140960795 + 11487 * 2 ^ 59
def prefixEnd_11487 : Nat := 4983230072969 + 3 ^ 40 * 11487 * 2
def baseEnd_11487 : Nat := 2621489901467462559857

theorem tailTrace_11487 : CollatzResearch.WordTrace tailWord_11487 prefixEnd_11487 2621489901467462559857 := by
  unfold tailWord_11487
  simp only [CollatzResearch.WordTrace]
  refine ⟨418965309392035668520715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 279310206261357112347143 418965309392035668520715)
  ·
    refine ⟨628447964088053502781073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 418965309392035668520715 628447964088053502781073)
    ·
      refine ⟨471335973066040127085805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 628447964088053502781073 471335973066040127085805)
      ·
        refine ⟨176750989899765047657177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 471335973066040127085805 176750989899765047657177)
        ·
          refine ⟨132563242424823785742883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176750989899765047657177 132563242424823785742883)
          ·
            refine ⟨198844863637235678614325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132563242424823785742883 198844863637235678614325)
            ·
              refine ⟨18641705965990844870093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 198844863637235678614325 18641705965990844870093)
              ·
                refine ⟨6990639737246566826285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18641705965990844870093 6990639737246566826285)
                ·
                  refine ⟨2621489901467462559857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6990639737246566826285 2621489901467462559857)
                  ·
                    rfl

theorem cell21_11487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 3].length) (baseStart_11487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11487 prefixEnd_11487 := by exact prefixLift 11487
  have htrace : WordTrace (prefixWord ++ tailWord_11487) baseStart_11487 baseEnd_11487 := by
    simpa [prefixWord, tailWord_11487, baseEnd_11487] using wordTrace_append hprefix tailTrace_11487
  have hstable : (prefixWord ++ tailWord_11487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11487).length < 2 ^ (prefixWord ++ tailWord_11487).sum := by decide
  have hdescent : baseEnd_11487 < baseStart_11487 := by decide
  rcases family_descends (prefixWord ++ tailWord_11487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11501 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 6]
def baseStart_11501 : Nat := 118140960795 + 11501 * 2 ^ 59
def prefixEnd_11501 : Nat := 4983230072969 + 3 ^ 40 * 11501 * 2
def baseEnd_11501 : Nat := 2624684892206549326495

theorem tailTrace_11501 : CollatzResearch.WordTrace tailWord_11501 prefixEnd_11501 2624684892206549326495 := by
  unfold tailWord_11501
  simp only [CollatzResearch.WordTrace]
  refine ⟨419475931341316059530357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 279650620894210706353571 419475931341316059530357)
  ·
    refine ⟨39325868563248380580971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 419475931341316059530357 39325868563248380580971)
    ·
      refine ⟨58988802844872570871457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39325868563248380580971 58988802844872570871457)
      ·
        refine ⟨44241602133654428153593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58988802844872570871457 44241602133654428153593)
        ·
          refine ⟨33181201600240821115195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44241602133654428153593 33181201600240821115195)
          ·
            refine ⟨49771802400361231672793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33181201600240821115195 49771802400361231672793)
            ·
              refine ⟨37328851800270923754595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49771802400361231672793 37328851800270923754595)
              ·
                refine ⟨55993277700406385631893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37328851800270923754595 55993277700406385631893)
                ·
                  refine ⟨2624684892206549326495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55993277700406385631893 2624684892206549326495)
                  ·
                    rfl

theorem cell21_11501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_11501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11501 prefixEnd_11501 := by exact prefixLift 11501
  have htrace : WordTrace (prefixWord ++ tailWord_11501) baseStart_11501 baseEnd_11501 := by
    simpa [prefixWord, tailWord_11501, baseEnd_11501] using wordTrace_append hprefix tailTrace_11501
  have hstable : (prefixWord ++ tailWord_11501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11501).length < 2 ^ (prefixWord ++ tailWord_11501).sum := by decide
  have hdescent : baseEnd_11501 < baseStart_11501 := by decide
  rcases family_descends (prefixWord ++ tailWord_11501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11518 : List Nat := [4, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_11518 : Nat := 118140960795 + 11518 * 2 ^ 59
def prefixEnd_11518 : Nat := 4983230072969 + 3 ^ 40 * 11518 * 2
def baseEnd_11518 : Nat := 2628564523818297543127

theorem tailTrace_11518 : CollatzResearch.WordTrace tailWord_11518 prefixEnd_11518 2628564523818297543127 := by
  unfold tailWord_11518
  simp only [CollatzResearch.WordTrace]
  refine ⟨52511996534965995362401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 280063981519818641932805 52511996534965995362401)
  ·
    refine ⟨39383997401224496521801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52511996534965995362401 39383997401224496521801)
    ·
      refine ⟨29537998050918372391351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39383997401224496521801 29537998050918372391351)
      ·
        refine ⟨44306997076377558587027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29537998050918372391351 44306997076377558587027)
        ·
          refine ⟨66460495614566337880541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44306997076377558587027 66460495614566337880541)
          ·
            refine ⟨24922685855462376705203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66460495614566337880541 24922685855462376705203)
            ·
              refine ⟨37384028783193565057805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24922685855462376705203 37384028783193565057805)
              ·
                refine ⟨14019010793697586896677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37384028783193565057805 14019010793697586896677)
                ·
                  refine ⟨2628564523818297543127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14019010793697586896677 2628564523818297543127)
                  ·
                    rfl

theorem cell21_11518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_11518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11518 prefixEnd_11518 := by exact prefixLift 11518
  have htrace : WordTrace (prefixWord ++ tailWord_11518) baseStart_11518 baseEnd_11518 := by
    simpa [prefixWord, tailWord_11518, baseEnd_11518] using wordTrace_append hprefix tailTrace_11518
  have hstable : (prefixWord ++ tailWord_11518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11518).length < 2 ^ (prefixWord ++ tailWord_11518).sum := by decide
  have hdescent : baseEnd_11518 < baseStart_11518 := by decide
  rcases family_descends (prefixWord ++ tailWord_11518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11529 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 7]
def baseStart_11529 : Nat := 118140960795 + 11529 * 2 ^ 59
def prefixEnd_11529 : Nat := 4983230072969 + 3 ^ 40 * 11529 * 2
def baseEnd_11529 : Nat := 2631074873684722859771

theorem tailTrace_11529 : CollatzResearch.WordTrace tailWord_11529 prefixEnd_11529 2631074873684722859771 := by
  unfold tailWord_11529
  simp only [CollatzResearch.WordTrace]
  refine ⟨420497175239876841549641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 280331450159917894366427 420497175239876841549641)
  ·
    refine ⟨315372881429907631162231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 420497175239876841549641 315372881429907631162231)
    ·
      refine ⟨473059322144861446743347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315372881429907631162231 473059322144861446743347)
      ·
        refine ⟨709588983217292170115021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473059322144861446743347 709588983217292170115021)
        ·
          refine ⟨266095868706484563793133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 709588983217292170115021 266095868706484563793133)
          ·
            refine ⟨99785950764931711422425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266095868706484563793133 99785950764931711422425)
            ·
              refine ⟨74839463073698783566819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99785950764931711422425 74839463073698783566819)
              ·
                refine ⟨112259194610548175350229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74839463073698783566819 112259194610548175350229)
                ·
                  refine ⟨2631074873684722859771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 112259194610548175350229 2631074873684722859771)
                  ·
                    rfl

theorem cell21_11529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_11529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11529 prefixEnd_11529 := by exact prefixLift 11529
  have htrace : WordTrace (prefixWord ++ tailWord_11529) baseStart_11529 baseEnd_11529 := by
    simpa [prefixWord, tailWord_11529, baseEnd_11529] using wordTrace_append hprefix tailTrace_11529
  have hstable : (prefixWord ++ tailWord_11529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11529).length < 2 ^ (prefixWord ++ tailWord_11529).sum := by decide
  have hdescent : baseEnd_11529 < baseStart_11529 := by decide
  rcases family_descends (prefixWord ++ tailWord_11529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11656 : List Nat := [2, 1, 3, 3, 1, 4, 1, 3, 3]
def baseStart_11656 : Nat := 118140960795 + 11656 * 2 ^ 59
def prefixEnd_11656 : Nat := 4983230072969 + 3 ^ 40 * 11656 * 2
def baseEnd_11656 : Nat := 2660058003960724242845

theorem tailTrace_11656 : CollatzResearch.WordTrace tailWord_11656 prefixEnd_11656 2660058003960724242845 := by
  unfold tailWord_11656
  simp only [CollatzResearch.WordTrace]
  refine ⟨212564622889888765711411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 283419497186518354281881 212564622889888765711411)
  ·
    refine ⟨318846934334833148567117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212564622889888765711411 318846934334833148567117)
    ·
      refine ⟨119567600375562430712669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318846934334833148567117 119567600375562430712669)
      ·
        refine ⟨44837850140835911517251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119567600375562430712669 44837850140835911517251)
        ·
          refine ⟨67256775211253867275877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44837850140835911517251 67256775211253867275877)
          ·
            refine ⟨12610645352110100114227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67256775211253867275877 12610645352110100114227)
            ·
              refine ⟨18915968028165150171341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12610645352110100114227 18915968028165150171341)
              ·
                refine ⟨7093488010561931314253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18915968028165150171341 7093488010561931314253)
                ·
                  refine ⟨2660058003960724242845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7093488010561931314253 2660058003960724242845)
                  ·
                    rfl

theorem cell21_11656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 3].length) (baseStart_11656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11656 prefixEnd_11656 := by exact prefixLift 11656
  have htrace : WordTrace (prefixWord ++ tailWord_11656) baseStart_11656 baseEnd_11656 := by
    simpa [prefixWord, tailWord_11656, baseEnd_11656] using wordTrace_append hprefix tailTrace_11656
  have hstable : (prefixWord ++ tailWord_11656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11656).length < 2 ^ (prefixWord ++ tailWord_11656).sum := by decide
  have hdescent : baseEnd_11656 < baseStart_11656 := by decide
  rcases family_descends (prefixWord ++ tailWord_11656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11732 : List Nat := [2, 4, 1, 2, 3, 1, 1, 4, 3]
def baseStart_11732 : Nat := 118140960795 + 11732 * 2 ^ 59
def prefixEnd_11732 : Nat := 4983230072969 + 3 ^ 40 * 11732 * 2
def baseEnd_11732 : Nat := 2677402239401480976023

theorem tailTrace_11732 : CollatzResearch.WordTrace tailWord_11732 prefixEnd_11732 2677402239401480976023 := by
  unfold tailWord_11732
  simp only [CollatzResearch.WordTrace]
  refine ⟨213950596752221255594725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 285267462336295007459633 213950596752221255594725)
  ·
    refine ⟨40115736891041485424011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213950596752221255594725 40115736891041485424011)
    ·
      refine ⟨60173605336562228136017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40115736891041485424011 60173605336562228136017)
      ·
        refine ⟨45130204002421671102013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60173605336562228136017 45130204002421671102013)
        ·
          refine ⟨16923826500908126663255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45130204002421671102013 16923826500908126663255)
          ·
            refine ⟨25385739751362189994883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16923826500908126663255 25385739751362189994883)
            ·
              refine ⟨38078609627043284992325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25385739751362189994883 38078609627043284992325)
              ·
                refine ⟨7139739305070615936061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38078609627043284992325 7139739305070615936061)
                ·
                  refine ⟨2677402239401480976023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7139739305070615936061 2677402239401480976023)
                  ·
                    rfl

theorem cell21_11732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_11732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11732 prefixEnd_11732 := by exact prefixLift 11732
  have htrace : WordTrace (prefixWord ++ tailWord_11732) baseStart_11732 baseEnd_11732 := by
    simpa [prefixWord, tailWord_11732, baseEnd_11732] using wordTrace_append hprefix tailTrace_11732
  have hstable : (prefixWord ++ tailWord_11732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11732).length < 2 ^ (prefixWord ++ tailWord_11732).sum := by decide
  have hdescent : baseEnd_11732 < baseStart_11732 := by decide
  rcases family_descends (prefixWord ++ tailWord_11732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11771 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 8]
def baseStart_11771 : Nat := 118140960795 + 11771 * 2 ^ 59
def prefixEnd_11771 : Nat := 4983230072969 + 3 ^ 40 * 11771 * 2
def baseEnd_11771 : Nat := 2686302570746079825943

theorem tailTrace_11771 : CollatzResearch.WordTrace tailWord_11771 prefixEnd_11771 2686302570746079825943 := by
  unfold tailWord_11771
  simp only [CollatzResearch.WordTrace]
  refine ⟨429323640363152171859167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 286215760242101447906111 429323640363152171859167)
  ·
    refine ⟨643985460544728257788751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 429323640363152171859167 643985460544728257788751)
    ·
      refine ⟨965978190817092386683127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 643985460544728257788751 965978190817092386683127)
      ·
        refine ⟨1448967286225638580024691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 965978190817092386683127 1448967286225638580024691)
        ·
          refine ⟨2173450929338457870037037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1448967286225638580024691 2173450929338457870037037)
          ·
            refine ⟨815044098501921701263889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2173450929338457870037037 815044098501921701263889)
            ·
              refine ⟨611283073876441275947917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 815044098501921701263889 611283073876441275947917)
              ·
                refine ⟨229231152703665478480469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 611283073876441275947917 229231152703665478480469)
                ·
                  refine ⟨2686302570746079825943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 229231152703665478480469 2686302570746079825943)
                  ·
                    rfl

theorem cell21_11771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 8].length) (baseStart_11771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11771 prefixEnd_11771 := by exact prefixLift 11771
  have htrace : WordTrace (prefixWord ++ tailWord_11771) baseStart_11771 baseEnd_11771 := by
    simpa [prefixWord, tailWord_11771, baseEnd_11771] using wordTrace_append hprefix tailTrace_11771
  have hstable : (prefixWord ++ tailWord_11771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11771).length < 2 ^ (prefixWord ++ tailWord_11771).sum := by decide
  have hdescent : baseEnd_11771 < baseStart_11771 := by decide
  rcases family_descends (prefixWord ++ tailWord_11771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11802 : List Nat := [3, 1, 1, 3, 1, 1, 1, 10]
def baseStart_11802 : Nat := 118140960795 + 11802 * 2 ^ 59
def prefixEnd_11802 : Nat := 4983230072969 + 3 ^ 40 * 11802 * 2
def baseEnd_11802 : Nat := 897792397698971603071

theorem tailTrace_11802 : CollatzResearch.WordTrace tailWord_11802 prefixEnd_11802 897792397698971603071 := by
  unfold tailWord_11802
  simp only [CollatzResearch.WordTrace]
  refine ⟨107613575812711116559415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 286969535500562977491773 107613575812711116559415)
  ·
    refine ⟨161420363719066674839123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107613575812711116559415 161420363719066674839123)
    ·
      refine ⟨242130545578600012258685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161420363719066674839123 242130545578600012258685)
      ·
        refine ⟨90798954591975004597007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242130545578600012258685 90798954591975004597007)
        ·
          refine ⟨136198431887962506895511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90798954591975004597007 136198431887962506895511)
          ·
            refine ⟨204297647831943760343267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136198431887962506895511 204297647831943760343267)
            ·
              refine ⟨306446471747915640514901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204297647831943760343267 306446471747915640514901)
              ·
                refine ⟨897792397698971603071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 306446471747915640514901 897792397698971603071)
                ·
                  rfl

theorem cell21_11802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_11802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11802 prefixEnd_11802 := by exact prefixLift 11802
  have htrace : WordTrace (prefixWord ++ tailWord_11802) baseStart_11802 baseEnd_11802 := by
    simpa [prefixWord, tailWord_11802, baseEnd_11802] using wordTrace_append hprefix tailTrace_11802
  have hstable : (prefixWord ++ tailWord_11802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11802).length < 2 ^ (prefixWord ++ tailWord_11802).sum := by decide
  have hdescent : baseEnd_11802 < baseStart_11802 := by decide
  rcases family_descends (prefixWord ++ tailWord_11802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11836 : List Nat := [2, 2, 2, 2, 5, 1, 7]
def baseStart_11836 : Nat := 118140960795 + 11836 * 2 ^ 59
def prefixEnd_11836 : Nat := 4983230072969 + 3 ^ 40 * 11836 * 2
def baseEnd_11836 : Nat := 300126272924490138053

theorem tailTrace_11836 : CollatzResearch.WordTrace tailWord_11836 prefixEnd_11836 300126272924490138053 := by
  unfold tailWord_11836
  simp only [CollatzResearch.WordTrace]
  refine ⟨215847192563834136487681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 287796256751778848650241 215847192563834136487681)
  ·
    refine ⟨161885394422875602365761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215847192563834136487681 161885394422875602365761)
    ·
      refine ⟨121414045817156701774321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161885394422875602365761 121414045817156701774321)
      ·
        refine ⟨91060534362867526330741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121414045817156701774321 91060534362867526330741)
        ·
          refine ⟨8536925096518830593507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91060534362867526330741 8536925096518830593507)
          ·
            refine ⟨12805387644778245890261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8536925096518830593507 12805387644778245890261)
            ·
              refine ⟨300126272924490138053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12805387644778245890261 300126272924490138053)
              ·
                rfl

theorem cell21_11836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 7].length) (baseStart_11836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11836 prefixEnd_11836 := by exact prefixLift 11836
  have htrace : WordTrace (prefixWord ++ tailWord_11836) baseStart_11836 baseEnd_11836 := by
    simpa [prefixWord, tailWord_11836, baseEnd_11836] using wordTrace_append hprefix tailTrace_11836
  have hstable : (prefixWord ++ tailWord_11836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11836).length < 2 ^ (prefixWord ++ tailWord_11836).sum := by decide
  have hdescent : baseEnd_11836 < baseStart_11836 := by decide
  rcases family_descends (prefixWord ++ tailWord_11836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11909 : List Nat := [1, 3, 1, 1, 4, 1, 2, 3, 5]
def baseStart_11909 : Nat := 118140960795 + 11909 * 2 ^ 59
def prefixEnd_11909 : Nat := 4983230072969 + 3 ^ 40 * 11909 * 2
def baseEnd_11909 : Nat := 2717796050888506525661

theorem tailTrace_11909 : CollatzResearch.WordTrace tailWord_11909 prefixEnd_11909 2717796050888506525661 := by
  unfold tailWord_11909
  simp only [CollatzResearch.WordTrace]
  refine ⟨434356913863201740382781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 289571275908801160255187 434356913863201740382781)
  ·
    refine ⟨162883842698700652643543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 434356913863201740382781 162883842698700652643543)
    ·
      refine ⟨244325764048050978965315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162883842698700652643543 244325764048050978965315)
      ·
        refine ⟨366488646072076468447973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244325764048050978965315 366488646072076468447973)
        ·
          refine ⟨68716621138514337833995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 366488646072076468447973 68716621138514337833995)
          ·
            refine ⟨103074931707771506750993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68716621138514337833995 103074931707771506750993)
            ·
              refine ⟨77306198780828630063245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103074931707771506750993 77306198780828630063245)
              ·
                refine ⟨28989824542810736273717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77306198780828630063245 28989824542810736273717)
                ·
                  refine ⟨2717796050888506525661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28989824542810736273717 2717796050888506525661)
                  ·
                    rfl

theorem cell21_11909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_11909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11909 prefixEnd_11909 := by exact prefixLift 11909
  have htrace : WordTrace (prefixWord ++ tailWord_11909) baseStart_11909 baseEnd_11909 := by
    simpa [prefixWord, tailWord_11909, baseEnd_11909] using wordTrace_append hprefix tailTrace_11909
  have hstable : (prefixWord ++ tailWord_11909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11909).length < 2 ^ (prefixWord ++ tailWord_11909).sum := by decide
  have hdescent : baseEnd_11909 < baseStart_11909 := by decide
  rcases family_descends (prefixWord ++ tailWord_11909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11957 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 6]
def baseStart_11957 : Nat := 118140960795 + 11957 * 2 ^ 59
def prefixEnd_11957 : Nat := 4983230072969 + 3 ^ 40 * 11957 * 2
def baseEnd_11957 : Nat := 2728750304851089725563

theorem tailTrace_11957 : CollatzResearch.WordTrace tailWord_11957 prefixEnd_11957 2728750304851089725563 := by
  unfold tailWord_11957
  simp only [CollatzResearch.WordTrace]
  refine ⟨436107617689305938130125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 290738411792870625420083 436107617689305938130125)
  ·
    refine ⟨163540356633489726798797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 436107617689305938130125 163540356633489726798797)
    ·
      refine ⟨61327633737558647549549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163540356633489726798797 61327633737558647549549)
      ·
        refine ⟨22997862651584492831081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61327633737558647549549 22997862651584492831081)
        ·
          refine ⟨17248396988688369623311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22997862651584492831081 17248396988688369623311)
          ·
            refine ⟨25872595483032554434967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17248396988688369623311 25872595483032554434967)
            ·
              refine ⟨38808893224548831652451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25872595483032554434967 38808893224548831652451)
              ·
                refine ⟨58213339836823247478677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38808893224548831652451 58213339836823247478677)
                ·
                  refine ⟨2728750304851089725563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58213339836823247478677 2728750304851089725563)
                  ·
                    rfl

theorem cell21_11957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_11957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11957 prefixEnd_11957 := by exact prefixLift 11957
  have htrace : WordTrace (prefixWord ++ tailWord_11957) baseStart_11957 baseEnd_11957 := by
    simpa [prefixWord, tailWord_11957, baseEnd_11957] using wordTrace_append hprefix tailTrace_11957
  have hstable : (prefixWord ++ tailWord_11957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11957).length < 2 ^ (prefixWord ++ tailWord_11957).sum := by decide
  have hdescent : baseEnd_11957 < baseStart_11957 := by decide
  rcases family_descends (prefixWord ++ tailWord_11957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11985 : List Nat := [1, 2, 2, 1, 2, 4, 2, 2, 5]
def baseStart_11985 : Nat := 118140960795 + 11985 * 2 ^ 59
def prefixEnd_11985 : Nat := 4983230072969 + 3 ^ 40 * 11985 * 2
def baseEnd_11985 : Nat := 2735140286329263258839

theorem tailTrace_11985 : CollatzResearch.WordTrace tailWord_11985 prefixEnd_11985 2735140286329263258839 := by
  unfold tailWord_11985
  simp only [CollatzResearch.WordTrace]
  refine ⟨437128861587866720149409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 291419241058577813432939 437128861587866720149409)
  ·
    refine ⟨327846646190900040112057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 437128861587866720149409 327846646190900040112057)
    ·
      refine ⟨245884984643175030084043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327846646190900040112057 245884984643175030084043)
      ·
        refine ⟨368827476964762545126065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245884984643175030084043 368827476964762545126065)
        ·
          refine ⟨276620607723571908844549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368827476964762545126065 276620607723571908844549)
          ·
            refine ⟨51866363948169732908353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 276620607723571908844549 51866363948169732908353)
            ·
              refine ⟨38899772961127299681265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51866363948169732908353 38899772961127299681265)
              ·
                refine ⟨29174829720845474760949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38899772961127299681265 29174829720845474760949)
                ·
                  refine ⟨2735140286329263258839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29174829720845474760949 2735140286329263258839)
                  ·
                    rfl

theorem cell21_11985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_11985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11985 prefixEnd_11985 := by exact prefixLift 11985
  have htrace : WordTrace (prefixWord ++ tailWord_11985) baseStart_11985 baseEnd_11985 := by
    simpa [prefixWord, tailWord_11985, baseEnd_11985] using wordTrace_append hprefix tailTrace_11985
  have hstable : (prefixWord ++ tailWord_11985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11985).length < 2 ^ (prefixWord ++ tailWord_11985).sum := by decide
  have hdescent : baseEnd_11985 < baseStart_11985 := by decide
  rcases family_descends (prefixWord ++ tailWord_11985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11988 : List Nat := [2, 4, 1, 3, 1, 1, 4, 5]
def baseStart_11988 : Nat := 118140960795 + 11988 * 2 ^ 59
def prefixEnd_11988 : Nat := 4983230072969 + 3 ^ 40 * 11988 * 2
def baseEnd_11988 : Nat := 911941642400641569611

theorem tailTrace_11988 : CollatzResearch.WordTrace tailWord_11988 prefixEnd_11988 911941642400641569611 := by
  unfold tailWord_11988
  simp only [CollatzResearch.WordTrace]
  refine ⟨218619140288499116254309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 291492187051332155005745 218619140288499116254309)
  ·
    refine ⟨40991088804093584297683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 218619140288499116254309 40991088804093584297683)
    ·
      refine ⟨61486633206140376446525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40991088804093584297683 61486633206140376446525)
      ·
        refine ⟨23057487452302641167447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61486633206140376446525 23057487452302641167447)
        ·
          refine ⟨34586231178453961751171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23057487452302641167447 34586231178453961751171)
          ·
            refine ⟨51879346767680942626757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34586231178453961751171 51879346767680942626757)
            ·
              refine ⟨9727377518940176742517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51879346767680942626757 9727377518940176742517)
              ·
                refine ⟨911941642400641569611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9727377518940176742517 911941642400641569611)
                ·
                  rfl

theorem cell21_11988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 5].length) (baseStart_11988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11988 prefixEnd_11988 := by exact prefixLift 11988
  have htrace : WordTrace (prefixWord ++ tailWord_11988) baseStart_11988 baseEnd_11988 := by
    simpa [prefixWord, tailWord_11988, baseEnd_11988] using wordTrace_append hprefix tailTrace_11988
  have hstable : (prefixWord ++ tailWord_11988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11988).length < 2 ^ (prefixWord ++ tailWord_11988).sum := by decide
  have hdescent : baseEnd_11988 < baseStart_11988 := by decide
  rcases family_descends (prefixWord ++ tailWord_11988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11999 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 8]
def baseStart_11999 : Nat := 118140960795 + 11999 * 2 ^ 59
def prefixEnd_11999 : Nat := 4983230072969 + 3 ^ 40 * 11999 * 2
def baseEnd_11999 : Nat := 2738335277068350025477

theorem tailTrace_11999 : CollatzResearch.WordTrace tailWord_11999 prefixEnd_11999 2738335277068350025477 := by
  unfold tailWord_11999
  simp only [CollatzResearch.WordTrace]
  refine ⟨437639483537147111159051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 291759655691431407439367 437639483537147111159051)
  ·
    refine ⟨656459225305720666738577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 437639483537147111159051 656459225305720666738577)
    ·
      refine ⟨492344418979290500053933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 656459225305720666738577 492344418979290500053933)
      ·
        refine ⟨184629157117233937520225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 492344418979290500053933 184629157117233937520225)
        ·
          refine ⟨138471867837925453140169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184629157117233937520225 138471867837925453140169)
          ·
            refine ⟨103853900878444089855127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138471867837925453140169 103853900878444089855127)
            ·
              refine ⟨155780851317666134782691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103853900878444089855127 155780851317666134782691)
              ·
                refine ⟨233671276976499202174037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155780851317666134782691 233671276976499202174037)
                ·
                  refine ⟨2738335277068350025477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 233671276976499202174037 2738335277068350025477)
                  ·
                    rfl

theorem cell21_11999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 8].length) (baseStart_11999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_11999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_11999 prefixEnd_11999 := by exact prefixLift 11999
  have htrace : WordTrace (prefixWord ++ tailWord_11999) baseStart_11999 baseEnd_11999 := by
    simpa [prefixWord, tailWord_11999, baseEnd_11999] using wordTrace_append hprefix tailTrace_11999
  have hstable : (prefixWord ++ tailWord_11999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11999).length < 2 ^ (prefixWord ++ tailWord_11999).sum := by decide
  have hdescent : baseEnd_11999 < baseStart_11999 := by decide
  rcases family_descends (prefixWord ++ tailWord_11999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12033 : List Nat := [1, 2, 4, 1, 1, 1, 6, 1, 4]
def baseStart_12033 : Nat := 118140960795 + 12033 * 2 ^ 59
def prefixEnd_12033 : Nat := 4983230072969 + 3 ^ 40 * 12033 * 2
def baseEnd_12033 : Nat := 2746094540291846458741

theorem tailTrace_12033 : CollatzResearch.WordTrace tailWord_12033 prefixEnd_12033 2746094540291846458741 := by
  unfold tailWord_12033
  simp only [CollatzResearch.WordTrace]
  refine ⟨438879565413970917896753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 292586376942647278597835 438879565413970917896753)
  ·
    refine ⟨329159674060478188422565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 438879565413970917896753 329159674060478188422565)
    ·
      refine ⟨61717438886339660329231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329159674060478188422565 61717438886339660329231)
      ·
        refine ⟨92576158329509490493847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61717438886339660329231 92576158329509490493847)
        ·
          refine ⟨138864237494264235740771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92576158329509490493847 138864237494264235740771)
          ·
            refine ⟨208296356241396353611157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138864237494264235740771 208296356241396353611157)
            ·
              refine ⟨9763891698815454075523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 208296356241396353611157 9763891698815454075523)
              ·
                refine ⟨14645837548223181113285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9763891698815454075523 14645837548223181113285)
                ·
                  refine ⟨2746094540291846458741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14645837548223181113285 2746094540291846458741)
                  ·
                    rfl

theorem cell21_12033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 4].length) (baseStart_12033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_12033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_12033 prefixEnd_12033 := by exact prefixLift 12033
  have htrace : WordTrace (prefixWord ++ tailWord_12033) baseStart_12033 baseEnd_12033 := by
    simpa [prefixWord, tailWord_12033, baseEnd_12033] using wordTrace_append hprefix tailTrace_12033
  have hstable : (prefixWord ++ tailWord_12033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12033).length < 2 ^ (prefixWord ++ tailWord_12033).sum := by decide
  have hdescent : baseEnd_12033 < baseStart_12033 := by decide
  rcases family_descends (prefixWord ++ tailWord_12033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
