import V185TrunkScan23Chunk1234

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7317098 : List Nat := [3, 1, 3, 2, 1, 4, 1, 2, 1, 5]
def baseStart_7317098 : Nat := 118140960795 + 7317098 * 2 ^ 59
def prefixEnd_7317098 : Nat := 4983230072969 + 3 ^ 40 * 7317098 * 2
def baseEnd_7317098 : Nat := 1252396090017372684708095

theorem tailTrace_7317098 : CollatzResearch.WordTrace tailWord_7317098 prefixEnd_7317098 1252396090017372684708095 := by
  unfold tailWord_7317098
  simp only [CollatzResearch.WordTrace]
  refine ⟨66719122211352770423231987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177917659230274054461951965 66719122211352770423231987)
  ·
    refine ⟨100078683317029155634847981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66719122211352770423231987 100078683317029155634847981)
    ·
      refine ⟨37529506243885933363067993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100078683317029155634847981 37529506243885933363067993)
      ·
        refine ⟨28147129682914450022300995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37529506243885933363067993 28147129682914450022300995)
        ·
          refine ⟨42220694524371675033451493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28147129682914450022300995 42220694524371675033451493)
          ·
            refine ⟨7916380223319689068772155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42220694524371675033451493 7916380223319689068772155)
            ·
              refine ⟨11874570334979533603158233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7916380223319689068772155 11874570334979533603158233)
              ·
                refine ⟨8905927751234650202368675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11874570334979533603158233 8905927751234650202368675)
                ·
                  refine ⟨13358891626851975303553013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8905927751234650202368675 13358891626851975303553013)
                  ·
                    refine ⟨1252396090017372684708095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13358891626851975303553013 1252396090017372684708095)
                    ·
                      rfl

theorem cell23_7317098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_7317098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317098 prefixEnd_7317098 := by exact prefixLift 7317098
  have htrace : WordTrace (prefixWord ++ tailWord_7317098) baseStart_7317098 baseEnd_7317098 := by
    simpa [prefixWord, tailWord_7317098, baseEnd_7317098] using wordTrace_append hprefix tailTrace_7317098
  have hstable : (prefixWord ++ tailWord_7317098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317098).length < 2 ^ (prefixWord ++ tailWord_7317098).sum := by decide
  have hdescent : baseEnd_7317098 < baseStart_7317098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317121 : List Nat := [1, 2, 4, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_7317121 : Nat := 118140960795 + 7317121 * 2 ^ 59
def prefixEnd_7317121 : Nat := 4983230072969 + 3 ^ 40 * 7317121 * 2
def baseEnd_7317121 : Nat := 3757200080107171464136679

theorem tailTrace_7317121 : CollatzResearch.WordTrace tailWord_7317121 prefixEnd_7317121 3757200080107171464136679 := by
  unfold tailWord_7317121
  simp only [CollatzResearch.WordTrace]
  refine ⟨266877327724327756621015217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177918218482885171080676811 266877327724327756621015217)
  ·
    refine ⟨200157995793245817465761413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266877327724327756621015217 200157995793245817465761413)
    ·
      refine ⟨37529624211233590774830265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200157995793245817465761413 37529624211233590774830265)
      ·
        refine ⟨28147218158425193081122699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37529624211233590774830265 28147218158425193081122699)
        ·
          refine ⟨42220827237637789621684049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28147218158425193081122699 42220827237637789621684049)
          ·
            refine ⟨31665620428228342216263037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42220827237637789621684049 31665620428228342216263037)
            ·
              refine ⟨11874607660585628331098639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31665620428228342216263037 11874607660585628331098639)
              ·
                refine ⟨17811911490878442496647959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11874607660585628331098639 17811911490878442496647959)
                ·
                  refine ⟨26717867236317663744971939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17811911490878442496647959 26717867236317663744971939)
                  ·
                    refine ⟨40076800854476495617457909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26717867236317663744971939 40076800854476495617457909)
                    ·
                      refine ⟨3757200080107171464136679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40076800854476495617457909 3757200080107171464136679)
                      ·
                        rfl

theorem cell23_7317121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_7317121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317121 prefixEnd_7317121 := by exact prefixLift 7317121
  have htrace : WordTrace (prefixWord ++ tailWord_7317121) baseStart_7317121 baseEnd_7317121 := by
    simpa [prefixWord, tailWord_7317121, baseEnd_7317121] using wordTrace_append hprefix tailTrace_7317121
  have hstable : (prefixWord ++ tailWord_7317121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317121).length < 2 ^ (prefixWord ++ tailWord_7317121).sum := by decide
  have hdescent : baseEnd_7317121 < baseStart_7317121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317124 : List Nat := [2, 3, 2, 1, 4, 11]
def baseStart_7317124 : Nat := 118140960795 + 7317124 * 2 ^ 59
def prefixEnd_7317124 : Nat := 4983230072969 + 3 ^ 40 * 7317124 * 2
def baseEnd_7317124 : Nat := 15461735063988209680655

theorem tailTrace_7317124 : CollatzResearch.WordTrace tailWord_7317124 prefixEnd_7317124 15461735063988209680655 := by
  unfold tailWord_7317124
  simp only [CollatzResearch.WordTrace]
  refine ⟨133438718571658444066687213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177918291428877925422249617 133438718571658444066687213)
  ·
    refine ⟨50039519464371916525007705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133438718571658444066687213 50039519464371916525007705)
    ·
      refine ⟨37529639598278937393755779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50039519464371916525007705 37529639598278937393755779)
      ·
        refine ⟨56294459397418406090633669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37529639598278937393755779 56294459397418406090633669)
        ·
          refine ⟨10555211137015951141993813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56294459397418406090633669 10555211137015951141993813)
          ·
            refine ⟨15461735063988209680655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10555211137015951141993813 15461735063988209680655)
            ·
              rfl

theorem cell23_7317124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 11].length) (baseStart_7317124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317124 prefixEnd_7317124 := by exact prefixLift 7317124
  have htrace : WordTrace (prefixWord ++ tailWord_7317124) baseStart_7317124 baseEnd_7317124 := by
    simpa [prefixWord, tailWord_7317124, baseEnd_7317124] using wordTrace_append hprefix tailTrace_7317124
  have hstable : (prefixWord ++ tailWord_7317124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317124).length < 2 ^ (prefixWord ++ tailWord_7317124).sum := by decide
  have hdescent : baseEnd_7317124 < baseStart_7317124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317148 : List Nat := [2, 2, 3, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_7317148 : Nat := 118140960795 + 7317148 * 2 ^ 59
def prefixEnd_7317148 : Nat := 4983230072969 + 3 ^ 40 * 7317148 * 2
def baseEnd_7317148 : Nat := 3757213944084842858499055

theorem tailTrace_7317148 : CollatzResearch.WordTrace tailWord_7317148 prefixEnd_7317148 3757213944084842858499055 := by
  unfold tailWord_7317148
  simp only [CollatzResearch.WordTrace]
  refine ⟨133439156247614970116124049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177918874996819960154832065 133439156247614970116124049)
  ·
    refine ⟨100079367185711227587093037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133439156247614970116124049 100079367185711227587093037)
    ·
      refine ⟨37529762694641710345159889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100079367185711227587093037 37529762694641710345159889)
      ·
        refine ⟨28147322020981282758869917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37529762694641710345159889 28147322020981282758869917)
        ·
          refine ⟨10555245757867981034576219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28147322020981282758869917 10555245757867981034576219)
          ·
            refine ⟨15832868636801971551864329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10555245757867981034576219 15832868636801971551864329)
            ·
              refine ⟨11874651477601478663898247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15832868636801971551864329 11874651477601478663898247)
              ·
                refine ⟨17811977216402217995847371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11874651477601478663898247 17811977216402217995847371)
                ·
                  refine ⟨26717965824603326993771057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17811977216402217995847371 26717965824603326993771057)
                  ·
                    refine ⟨20038474368452495245328293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26717965824603326993771057 20038474368452495245328293)
                    ·
                      refine ⟨3757213944084842858499055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20038474368452495245328293 3757213944084842858499055)
                      ·
                        rfl

theorem cell23_7317148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_7317148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317148 prefixEnd_7317148 := by exact prefixLift 7317148
  have htrace : WordTrace (prefixWord ++ tailWord_7317148) baseStart_7317148 baseEnd_7317148 := by
    simpa [prefixWord, tailWord_7317148, baseEnd_7317148] using wordTrace_append hprefix tailTrace_7317148
  have hstable : (prefixWord ++ tailWord_7317148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317148).length < 2 ^ (prefixWord ++ tailWord_7317148).sum := by decide
  have hdescent : baseEnd_7317148 < baseStart_7317148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317161 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 7, 3, 2]
def baseStart_7317161 : Nat := 118140960795 + 7317161 * 2 ^ 59
def prefixEnd_7317161 : Nat := 4983230072969 + 3 ^ 40 * 7317161 * 2
def baseEnd_7317161 : Nat := 3757220619333351307636495

theorem tailTrace_7317161 : CollatzResearch.WordTrace tailWord_7317161 prefixEnd_7317161 3757220619333351307636495 := by
  unfold tailWord_7317161
  simp only [CollatzResearch.WordTrace]
  refine ⟨266878786644182843452471337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177919191096121895634980891 266878786644182843452471337)
  ·
    refine ⟨200159089983137132589353503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266878786644182843452471337 200159089983137132589353503)
    ·
      refine ⟨300238634974705698884030255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200159089983137132589353503 300238634974705698884030255)
      ·
        refine ⟨450357952462058548326045383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300238634974705698884030255 450357952462058548326045383)
        ·
          refine ⟨675536928693087822489068075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450357952462058548326045383 675536928693087822489068075)
          ·
            refine ⟨1013305393039631733733602113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675536928693087822489068075 1013305393039631733733602113)
            ·
              refine ⟨759979044779723800300201585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1013305393039631733733602113 759979044779723800300201585)
              ·
                refine ⟨569984283584792850225151189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759979044779723800300201585 569984283584792850225151189)
                ·
                  refine ⟨13359006646518582427151981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 569984283584792850225151189 13359006646518582427151981)
                  ·
                    refine ⟨5009627492444468410181993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13359006646518582427151981 5009627492444468410181993)
                    ·
                      refine ⟨3757220619333351307636495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5009627492444468410181993 3757220619333351307636495)
                      ·
                        rfl

theorem cell23_7317161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 3, 2].length) (baseStart_7317161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317161 prefixEnd_7317161 := by exact prefixLift 7317161
  have htrace : WordTrace (prefixWord ++ tailWord_7317161) baseStart_7317161 baseEnd_7317161 := by
    simpa [prefixWord, tailWord_7317161, baseEnd_7317161] using wordTrace_append hprefix tailTrace_7317161
  have hstable : (prefixWord ++ tailWord_7317161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317161).length < 2 ^ (prefixWord ++ tailWord_7317161).sum := by decide
  have hdescent : baseEnd_7317161 < baseStart_7317161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317184 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 4, 6]
def baseStart_7317184 : Nat := 118140960795 + 7317184 * 2 ^ 59
def prefixEnd_7317184 : Nat := 4983230072969 + 3 ^ 40 * 7317184 * 2
def baseEnd_7317184 : Nat := 1252410809796134905882963

theorem tailTrace_7317184 : CollatzResearch.WordTrace tailWord_7317184 prefixEnd_7317184 1252410809796134905882963 := by
  unfold tailWord_7317184
  simp only [CollatzResearch.WordTrace]
  refine ⟨133439812761549759190279303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177919750348733012253705737 133439812761549759190279303)
  ·
    refine ⟨200159719142324638785418955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133439812761549759190279303 200159719142324638785418955)
    ·
      refine ⟨300239578713486958178128433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200159719142324638785418955 300239578713486958178128433)
      ·
        refine ⟨225179684035115218633596325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300239578713486958178128433 225179684035115218633596325)
        ·
          refine ⟨42221190756584103493799311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225179684035115218633596325 42221190756584103493799311)
          ·
            refine ⟨63331786134876155240698967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42221190756584103493799311 63331786134876155240698967)
            ·
              refine ⟨94997679202314232861048451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63331786134876155240698967 94997679202314232861048451)
              ·
                refine ⟨142496518803471349291572677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94997679202314232861048451 142496518803471349291572677)
                ·
                  refine ⟨26718097275650877992169877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142496518803471349291572677 26718097275650877992169877)
                  ·
                    refine ⟨1252410809796134905882963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26718097275650877992169877 1252410809796134905882963)
                    ·
                      rfl

theorem cell23_7317184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 4, 6].length) (baseStart_7317184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317184 prefixEnd_7317184 := by exact prefixLift 7317184
  have htrace : WordTrace (prefixWord ++ tailWord_7317184) baseStart_7317184 baseEnd_7317184 := by
    simpa [prefixWord, tailWord_7317184, baseEnd_7317184] using wordTrace_append hprefix tailTrace_7317184
  have hstable : (prefixWord ++ tailWord_7317184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317184).length < 2 ^ (prefixWord ++ tailWord_7317184).sum := by decide
  have hdescent : baseEnd_7317184 < baseStart_7317184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317186 : List Nat := [3, 5, 1, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_7317186 : Nat := 118140960795 + 7317186 * 2 ^ 59
def prefixEnd_7317186 : Nat := 4983230072969 + 3 ^ 40 * 7317186 * 2
def baseEnd_7317186 : Nat := 3757233456349713709823881

theorem tailTrace_7317186 : CollatzResearch.WordTrace tailWord_7317186 prefixEnd_7317186 3757233456349713709823881 := by
  unfold tailWord_7317186
  simp only [CollatzResearch.WordTrace]
  refine ⟨66719924617273068180532853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177919798979394848481420941 66719924617273068180532853)
  ·
    refine ⟨6254992932869350141924955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66719924617273068180532853 6254992932869350141924955)
    ·
      refine ⟨9382489399304025212887433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6254992932869350141924955 9382489399304025212887433)
      ·
        refine ⟨7036867049478018909665575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9382489399304025212887433 7036867049478018909665575)
        ·
          refine ⟨10555300574217028364498363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7036867049478018909665575 10555300574217028364498363)
          ·
            refine ⟨15832950861325542546747545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10555300574217028364498363 15832950861325542546747545)
            ·
              refine ⟨11874713145994156910060659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15832950861325542546747545 11874713145994156910060659)
              ·
                refine ⟨17812069718991235365090989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11874713145994156910060659 17812069718991235365090989)
                ·
                  refine ⟨6679526144621713261909121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17812069718991235365090989 6679526144621713261909121)
                  ·
                    refine ⟨5009644608466284946431841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6679526144621713261909121 5009644608466284946431841)
                    ·
                      refine ⟨3757233456349713709823881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5009644608466284946431841 3757233456349713709823881)
                      ·
                        rfl

theorem cell23_7317186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_7317186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317186 prefixEnd_7317186 := by exact prefixLift 7317186
  have htrace : WordTrace (prefixWord ++ tailWord_7317186) baseStart_7317186 baseEnd_7317186 := by
    simpa [prefixWord, tailWord_7317186, baseEnd_7317186] using wordTrace_append hprefix tailTrace_7317186
  have hstable : (prefixWord ++ tailWord_7317186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317186).length < 2 ^ (prefixWord ++ tailWord_7317186).sum := by decide
  have hdescent : baseEnd_7317186 < baseStart_7317186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317202 : List Nat := [3, 2, 2, 2, 2, 2, 3, 1, 2, 1, 3]
def baseStart_7317202 : Nat := 118140960795 + 7317202 * 2 ^ 59
def prefixEnd_7317202 : Nat := 4983230072969 + 3 ^ 40 * 7317202 * 2
def baseEnd_7317202 : Nat := 3757241672040185647223807

theorem tailTrace_7317202 : CollatzResearch.WordTrace tailWord_7317202 prefixEnd_7317202 3757241672040185647223807 := by
  unfold tailWord_7317202
  simp only [CollatzResearch.WordTrace]
  refine ⟨66720070509258576863678465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177920188024689538303142573 66720070509258576863678465)
  ·
    refine ⟨50040052881943932647758849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66720070509258576863678465 50040052881943932647758849)
    ·
      refine ⟨37530039661457949485819137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50040052881943932647758849 37530039661457949485819137)
      ·
        refine ⟨28147529746093462114364353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37530039661457949485819137 28147529746093462114364353)
        ·
          refine ⟨21110647309570096585773265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28147529746093462114364353 21110647309570096585773265)
          ·
            refine ⟨15832985482177572439329949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21110647309570096585773265 15832985482177572439329949)
            ·
              refine ⟨5937369555816589664748731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15832985482177572439329949 5937369555816589664748731)
              ·
                refine ⟨8906054333724884497123097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5937369555816589664748731 8906054333724884497123097)
                ·
                  refine ⟨6679540750293663372842323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8906054333724884497123097 6679540750293663372842323)
                  ·
                    refine ⟨10019311125440495059263485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6679540750293663372842323 10019311125440495059263485)
                    ·
                      refine ⟨3757241672040185647223807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10019311125440495059263485 3757241672040185647223807)
                      ·
                        rfl

theorem cell23_7317202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_7317202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317202 prefixEnd_7317202 := by exact prefixLift 7317202
  have htrace : WordTrace (prefixWord ++ tailWord_7317202) baseStart_7317202 baseEnd_7317202 := by
    simpa [prefixWord, tailWord_7317202, baseEnd_7317202] using wordTrace_append hprefix tailTrace_7317202
  have hstable : (prefixWord ++ tailWord_7317202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317202).length < 2 ^ (prefixWord ++ tailWord_7317202).sum := by decide
  have hdescent : baseEnd_7317202 < baseStart_7317202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317298 : List Nat := [3, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_7317298 : Nat := 118140960795 + 7317298 * 2 ^ 59
def prefixEnd_7317298 : Nat := 4983230072969 + 3 ^ 40 * 7317298 * 2
def baseEnd_7317298 : Nat := 3757290966183017271623365

theorem tailTrace_7317298 : CollatzResearch.WordTrace tailWord_7317298 prefixEnd_7317298 3757290966183017271623365 := by
  unfold tailWord_7317298
  simp only [CollatzResearch.WordTrace]
  refine ⟨66720945861171628962552137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177922522296457677233472365 66720945861171628962552137)
  ·
    refine ⟨50040709395878721721914103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66720945861171628962552137 50040709395878721721914103)
    ·
      refine ⟨75061064093818082582871155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50040709395878721721914103 75061064093818082582871155)
      ·
        refine ⟨112591596140727123874306733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75061064093818082582871155 112591596140727123874306733)
        ·
          refine ⟨42221848552772671452865025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112591596140727123874306733 42221848552772671452865025)
          ·
            refine ⟨31666386414579503589648769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42221848552772671452865025 31666386414579503589648769)
            ·
              refine ⟨23749789810934627692236577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31666386414579503589648769 23749789810934627692236577)
              ·
                refine ⟨17812342358200970769177433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23749789810934627692236577 17812342358200970769177433)
                ·
                  refine ⟨13359256768650728076883075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17812342358200970769177433 13359256768650728076883075)
                  ·
                    refine ⟨20038885152976092115324613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13359256768650728076883075 20038885152976092115324613)
                    ·
                      refine ⟨3757290966183017271623365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20038885152976092115324613 3757290966183017271623365)
                      ·
                        rfl

theorem cell23_7317298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_7317298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317298 prefixEnd_7317298 := by exact prefixLift 7317298
  have htrace : WordTrace (prefixWord ++ tailWord_7317298) baseStart_7317298 baseEnd_7317298 := by
    simpa [prefixWord, tailWord_7317298, baseEnd_7317298] using wordTrace_append hprefix tailTrace_7317298
  have hstable : (prefixWord ++ tailWord_7317298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317298).length < 2 ^ (prefixWord ++ tailWord_7317298).sum := by decide
  have hdescent : baseEnd_7317298 < baseStart_7317298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317321 : List Nat := [1, 2, 1, 1, 2, 4, 1, 5, 6]
def baseStart_7317321 : Nat := 118140960795 + 7317321 * 2 ^ 59
def prefixEnd_7317321 : Nat := 4983230072969 + 3 ^ 40 * 7317321 * 2
def baseEnd_7317321 : Nat := 417478086248674520181751

theorem tailTrace_7317321 : CollatzResearch.WordTrace tailWord_7317321 prefixEnd_7317321 417478086248674520181751 := by
  unfold tailWord_7317321
  simp only [CollatzResearch.WordTrace]
  refine ⟨266884622323603190778295817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177923081549068793852197211 266884622323603190778295817)
  ·
    refine ⟨200163466742702393083721863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266884622323603190778295817 200163466742702393083721863)
    ·
      refine ⟨300245200114053589625582795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200163466742702393083721863 300245200114053589625582795)
      ·
        refine ⟨450367800171080384438374193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300245200114053589625582795 450367800171080384438374193)
        ·
          refine ⟨337775850128310288328780645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450367800171080384438374193 337775850128310288328780645)
          ·
            refine ⟨63332971899058179061646371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337775850128310288328780645 63332971899058179061646371)
            ·
              refine ⟨94999457848587268592469557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63332971899058179061646371 94999457848587268592469557)
              ·
                refine ⟨8906199173305056430544021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94999457848587268592469557 8906199173305056430544021)
                ·
                  refine ⟨417478086248674520181751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8906199173305056430544021 417478086248674520181751)
                  ·
                    rfl

theorem cell23_7317321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 6].length) (baseStart_7317321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317321 prefixEnd_7317321 := by exact prefixLift 7317321
  have htrace : WordTrace (prefixWord ++ tailWord_7317321) baseStart_7317321 baseEnd_7317321 := by
    simpa [prefixWord, tailWord_7317321, baseEnd_7317321] using wordTrace_append hprefix tailTrace_7317321
  have hstable : (prefixWord ++ tailWord_7317321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317321).length < 2 ^ (prefixWord ++ tailWord_7317321).sum := by decide
  have hdescent : baseEnd_7317321 < baseStart_7317321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317325 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_7317325 : Nat := 118140960795 + 7317325 * 2 ^ 59
def prefixEnd_7317325 : Nat := 4983230072969 + 3 ^ 40 * 7317325 * 2
def baseEnd_7317325 : Nat := 1252434943386896221995247

theorem tailTrace_7317325 : CollatzResearch.WordTrace tailWord_7317325 prefixEnd_7317325 1252434943386896221995247 := by
  unfold tailWord_7317325
  simp only [CollatzResearch.WordTrace]
  refine ⟨266884768215588699461441429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177923178810392466307627619 266884768215588699461441429)
  ·
    refine ⟨12510223510105720287255067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 266884768215588699461441429 12510223510105720287255067)
    ·
      refine ⟨18765335265158580430882601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12510223510105720287255067 18765335265158580430882601)
      ·
        refine ⟨14074001448868935323161951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18765335265158580430882601 14074001448868935323161951)
        ·
          refine ⟨21111002173303402984742927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14074001448868935323161951 21111002173303402984742927)
          ·
            refine ⟨31666503259955104477114391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21111002173303402984742927 31666503259955104477114391)
            ·
              refine ⟨47499754889932656715671587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31666503259955104477114391 47499754889932656715671587)
              ·
                refine ⟨71249632334898985073507381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47499754889932656715671587 71249632334898985073507381)
                ·
                  refine ⟨6679653031396779850641317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71249632334898985073507381 6679653031396779850641317)
                  ·
                    refine ⟨1252434943386896221995247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6679653031396779850641317 1252434943386896221995247)
                    ·
                      rfl

theorem cell23_7317325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_7317325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317325 prefixEnd_7317325 := by exact prefixLift 7317325
  have htrace : WordTrace (prefixWord ++ tailWord_7317325) baseStart_7317325 baseEnd_7317325 := by
    simpa [prefixWord, tailWord_7317325, baseEnd_7317325] using wordTrace_append hprefix tailTrace_7317325
  have hstable : (prefixWord ++ tailWord_7317325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317325).length < 2 ^ (prefixWord ++ tailWord_7317325).sum := by decide
  have hdescent : baseEnd_7317325 < baseStart_7317325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317358 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_7317358 : Nat := 118140960795 + 7317358 * 2 ^ 59
def prefixEnd_7317358 : Nat := 4983230072969 + 3 ^ 40 * 7317358 * 2
def baseEnd_7317358 : Nat := 3757321775022287036873089

theorem tailTrace_7317358 : CollatzResearch.WordTrace tailWord_7317358 prefixEnd_7317358 3757321775022287036873089 := by
  unfold tailWord_7317358
  simp only [CollatzResearch.WordTrace]
  refine ⟨33360746478058643262174091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177923981216312764064928485 33360746478058643262174091)
  ·
    refine ⟨50041119717087964893261137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33360746478058643262174091 50041119717087964893261137)
    ·
      refine ⟨37530839787815973669945853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50041119717087964893261137 37530839787815973669945853)
      ·
        refine ⟨14074064920430990126229695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37530839787815973669945853 14074064920430990126229695)
        ·
          refine ⟨21111097380646485189344543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14074064920430990126229695 21111097380646485189344543)
          ·
            refine ⟨31666646070969727784016815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21111097380646485189344543 31666646070969727784016815)
            ·
              refine ⟨47499969106454591676025223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31666646070969727784016815 47499969106454591676025223)
              ·
                refine ⟨71249953659681887514037835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47499969106454591676025223 71249953659681887514037835)
                ·
                  refine ⟨106874930489522831271056753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71249953659681887514037835 106874930489522831271056753)
                  ·
                    refine ⟨80156197867142123453292565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106874930489522831271056753 80156197867142123453292565)
                    ·
                      refine ⟨3757321775022287036873089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80156197867142123453292565 3757321775022287036873089)
                      ·
                        rfl

theorem cell23_7317358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_7317358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317358 prefixEnd_7317358 := by exact prefixLift 7317358
  have htrace : WordTrace (prefixWord ++ tailWord_7317358) baseStart_7317358 baseEnd_7317358 := by
    simpa [prefixWord, tailWord_7317358, baseEnd_7317358] using wordTrace_append hprefix tailTrace_7317358
  have hstable : (prefixWord ++ tailWord_7317358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317358).length < 2 ^ (prefixWord ++ tailWord_7317358).sum := by decide
  have hdescent : baseEnd_7317358 < baseStart_7317358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317388 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 1, 8, 2]
def baseStart_7317388 : Nat := 118140960795 + 7317388 * 2 ^ 59
def prefixEnd_7317388 : Nat := 4983230072969 + 3 ^ 40 * 7317388 * 2
def baseEnd_7317388 : Nat := 3757337179441921919497951

theorem tailTrace_7317388 : CollatzResearch.WordTrace tailWord_7317388 prefixEnd_7317388 3757337179441921919497951 := by
  unfold tailWord_7317388
  simp only [CollatzResearch.WordTrace]
  refine ⟨133443533007180230610492409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177924710676240307480656545 133443533007180230610492409)
  ·
    refine ⟨100082649755385172957869307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133443533007180230610492409 100082649755385172957869307)
    ·
      refine ⟨150123974633077759436803961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100082649755385172957869307 150123974633077759436803961)
      ·
        refine ⟨112592980974808319577602971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150123974633077759436803961 112592980974808319577602971)
        ·
          refine ⟨168889471462212479366404457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112592980974808319577602971 168889471462212479366404457)
          ·
            refine ⟨126667103596659359524803343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168889471462212479366404457 126667103596659359524803343)
            ·
              refine ⟨190000655394989039287205015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126667103596659359524803343 190000655394989039287205015)
              ·
                refine ⟨285000983092483558930807523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190000655394989039287205015 285000983092483558930807523)
                ·
                  refine ⟨427501474638725338396211285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285000983092483558930807523 427501474638725338396211285)
                  ·
                    refine ⟨5009782905922562559330601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 427501474638725338396211285 5009782905922562559330601)
                    ·
                      refine ⟨3757337179441921919497951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5009782905922562559330601 3757337179441921919497951)
                      ·
                        rfl

theorem cell23_7317388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_7317388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317388 prefixEnd_7317388 := by exact prefixLift 7317388
  have htrace : WordTrace (prefixWord ++ tailWord_7317388) baseStart_7317388 baseEnd_7317388 := by
    simpa [prefixWord, tailWord_7317388, baseEnd_7317388] using wordTrace_append hprefix tailTrace_7317388
  have hstable : (prefixWord ++ tailWord_7317388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317388).length < 2 ^ (prefixWord ++ tailWord_7317388).sum := by decide
  have hdescent : baseEnd_7317388 < baseStart_7317388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317399 : List Nat := [1, 1, 3, 3, 1, 5, 1, 3, 1, 1, 3]
def baseStart_7317399 : Nat := 118140960795 + 7317399 * 2 ^ 59
def prefixEnd_7317399 : Nat := 4983230072969 + 3 ^ 40 * 7317399 * 2
def baseEnd_7317399 : Nat := 3757342827729121376460401

theorem tailTrace_7317399 : CollatzResearch.WordTrace tailWord_7317399 prefixEnd_7317399 3757342827729121376460401 := by
  unfold tailWord_7317399
  simp only [CollatzResearch.WordTrace]
  refine ⟨266887467217320610099635251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177924978144880406733090167 266887467217320610099635251)
  ·
    refine ⟨400331200825980915149452877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266887467217320610099635251 400331200825980915149452877)
    ·
      refine ⟨150124200309742843181044829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400331200825980915149452877 150124200309742843181044829)
      ·
        refine ⟨56296575116153566192891811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150124200309742843181044829 56296575116153566192891811)
        ·
          refine ⟨84444862674230349289337717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56296575116153566192891811 84444862674230349289337717)
          ·
            refine ⟨7916705875709095245875411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84444862674230349289337717 7916705875709095245875411)
            ·
              refine ⟨11875058813563642868813117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7916705875709095245875411 11875058813563642868813117)
              ·
                refine ⟨4453147055086366075804919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11875058813563642868813117 4453147055086366075804919)
                ·
                  refine ⟨6679720582629549113707379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4453147055086366075804919 6679720582629549113707379)
                  ·
                    refine ⟨10019580873944323670561069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6679720582629549113707379 10019580873944323670561069)
                    ·
                      refine ⟨3757342827729121376460401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10019580873944323670561069 3757342827729121376460401)
                      ·
                        rfl

theorem cell23_7317399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_7317399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317399 prefixEnd_7317399 := by exact prefixLift 7317399
  have htrace : WordTrace (prefixWord ++ tailWord_7317399) baseStart_7317399 baseEnd_7317399 := by
    simpa [prefixWord, tailWord_7317399, baseEnd_7317399] using wordTrace_append hprefix tailTrace_7317399
  have hstable : (prefixWord ++ tailWord_7317399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317399).length < 2 ^ (prefixWord ++ tailWord_7317399).sum := by decide
  have hdescent : baseEnd_7317399 < baseStart_7317399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317405 : List Nat := [1, 4, 2, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_7317405 : Nat := 118140960795 + 7317405 * 2 ^ 59
def prefixEnd_7317405 : Nat := 4983230072969 + 3 ^ 40 * 7317405 * 2
def baseEnd_7317405 : Nat := 3757345908613048352985373

theorem tailTrace_7317405 : CollatzResearch.WordTrace tailWord_7317405 prefixEnd_7317405 3757345908613048352985373 := by
  unfold tailWord_7317405
  simp only [CollatzResearch.WordTrace]
  refine ⟨266887686055298873124353669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177925124036865915416235779 266887686055298873124353669)
  ·
    refine ⟨50041441135368538710816313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266887686055298873124353669 50041441135368538710816313)
    ·
      refine ⟨37531080851526404033112235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50041441135368538710816313 37531080851526404033112235)
      ·
        refine ⟨56296621277289606049668353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37531080851526404033112235 56296621277289606049668353)
        ·
          refine ⟨42222465957967204537251265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56296621277289606049668353 42222465957967204537251265)
          ·
            refine ⟨31666849468475403402938449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42222465957967204537251265 31666849468475403402938449)
            ·
              refine ⟨23750137101356552552203837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31666849468475403402938449 23750137101356552552203837)
              ·
                refine ⟨8906301413008707207076439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23750137101356552552203837 8906301413008707207076439)
                ·
                  refine ⟨13359452119513060810614659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8906301413008707207076439 13359452119513060810614659)
                  ·
                    refine ⟨20039178179269591215921989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13359452119513060810614659 20039178179269591215921989)
                    ·
                      refine ⟨3757345908613048352985373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20039178179269591215921989 3757345908613048352985373)
                      ·
                        rfl

theorem cell23_7317405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_7317405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317405 prefixEnd_7317405 := by exact prefixLift 7317405
  have htrace : WordTrace (prefixWord ++ tailWord_7317405) baseStart_7317405 baseEnd_7317405 := by
    simpa [prefixWord, tailWord_7317405, baseEnd_7317405] using wordTrace_append hprefix tailTrace_7317405
  have hstable : (prefixWord ++ tailWord_7317405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317405).length < 2 ^ (prefixWord ++ tailWord_7317405).sum := by decide
  have hdescent : baseEnd_7317405 < baseStart_7317405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317408 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 3]
def baseStart_7317408 : Nat := 118140960795 + 7317408 * 2 ^ 59
def prefixEnd_7317408 : Nat := 4983230072969 + 3 ^ 40 * 7317408 * 2
def baseEnd_7317408 : Nat := 3757347449055011841247859

theorem tailTrace_7317408 : CollatzResearch.WordTrace tailWord_7317408 prefixEnd_7317408 3757347449055011841247859 := by
  unfold tailWord_7317408
  simp only [CollatzResearch.WordTrace]
  refine ⟨133443897737144002318356439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177925196982858669757808585 133443897737144002318356439)
  ·
    refine ⟨200165846605716003477534659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133443897737144002318356439 200165846605716003477534659)
    ·
      refine ⟨300248769908574005216301989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200165846605716003477534659 300248769908574005216301989)
      ·
        refine ⟨56296644357857625978056623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300248769908574005216301989 56296644357857625978056623)
        ·
          refine ⟨84444966536786438967084935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56296644357857625978056623 84444966536786438967084935)
          ·
            refine ⟨126667449805179658450627403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84444966536786438967084935 126667449805179658450627403)
            ·
              refine ⟨190001174707769487675941105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126667449805179658450627403 190001174707769487675941105)
              ·
                refine ⟨142500881030827115756955829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190001174707769487675941105 142500881030827115756955829)
                ·
                  refine ⟨13359457596640042102214609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142500881030827115756955829 13359457596640042102214609)
                  ·
                    refine ⟨10019593197480031576660957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13359457596640042102214609 10019593197480031576660957)
                    ·
                      refine ⟨3757347449055011841247859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10019593197480031576660957 3757347449055011841247859)
                      ·
                        rfl

theorem cell23_7317408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_7317408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317408 prefixEnd_7317408 := by exact prefixLift 7317408
  have htrace : WordTrace (prefixWord ++ tailWord_7317408) baseStart_7317408 baseEnd_7317408 := by
    simpa [prefixWord, tailWord_7317408, baseEnd_7317408] using wordTrace_append hprefix tailTrace_7317408
  have hstable : (prefixWord ++ tailWord_7317408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317408).length < 2 ^ (prefixWord ++ tailWord_7317408).sum := by decide
  have hdescent : baseEnd_7317408 < baseStart_7317408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317415 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 4, 4]
def baseStart_7317415 : Nat := 118140960795 + 7317415 * 2 ^ 59
def prefixEnd_7317415 : Nat := 4983230072969 + 3 ^ 40 * 7317415 * 2
def baseEnd_7317415 : Nat := 1252450347806531104620109

theorem tailTrace_7317415 : CollatzResearch.WordTrace tailWord_7317415 prefixEnd_7317415 1252450347806531104620109 := by
  unfold tailWord_7317415
  simp only [CollatzResearch.WordTrace]
  refine ⟨266888050785262644832217699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177925367190175096554811799 266888050785262644832217699)
  ·
    refine ⟨400332076177893967248326549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266888050785262644832217699 400332076177893967248326549)
    ·
      refine ⟨18765566070838779714765307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 400332076177893967248326549 18765566070838779714765307)
      ·
        refine ⟨28148349106258169572147961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18765566070838779714765307 28148349106258169572147961)
        ·
          refine ⟨21111261829693627179110971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28148349106258169572147961 21111261829693627179110971)
          ·
            refine ⟨31666892744540440768666457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21111261829693627179110971 31666892744540440768666457)
            ·
              refine ⟨23750169558405330576499843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31666892744540440768666457 23750169558405330576499843)
              ·
                refine ⟨35625254337607995864749765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23750169558405330576499843 35625254337607995864749765)
                ·
                  refine ⟨6679735188301499224640581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35625254337607995864749765 6679735188301499224640581)
                  ·
                    refine ⟨1252450347806531104620109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6679735188301499224640581 1252450347806531104620109)
                    ·
                      rfl

theorem cell23_7317415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_7317415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317415 prefixEnd_7317415 := by exact prefixLift 7317415
  have htrace : WordTrace (prefixWord ++ tailWord_7317415) baseStart_7317415 baseEnd_7317415 := by
    simpa [prefixWord, tailWord_7317415, baseEnd_7317415] using wordTrace_append hprefix tailTrace_7317415
  have hstable : (prefixWord ++ tailWord_7317415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317415).length < 2 ^ (prefixWord ++ tailWord_7317415).sum := by decide
  have hdescent : baseEnd_7317415 < baseStart_7317415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317416 : List Nat := [2, 1, 6, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_7317416 : Nat := 118140960795 + 7317416 * 2 ^ 59
def prefixEnd_7317416 : Nat := 4983230072969 + 3 ^ 40 * 7317416 * 2
def baseEnd_7317416 : Nat := 3757351556900247809947823

theorem tailTrace_7317416 : CollatzResearch.WordTrace tailWord_7317416 prefixEnd_7317416 3757351556900247809947823 := by
  unfold tailWord_7317416
  simp only [CollatzResearch.WordTrace]
  refine ⟨133444043629129511001502051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177925391505506014668669401 133444043629129511001502051)
  ·
    refine ⟨200166065443694266502253077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133444043629129511001502051 200166065443694266502253077)
    ·
      refine ⟨9382784317673168742293113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 200166065443694266502253077 9382784317673168742293113)
      ·
        refine ⟨7037088238254876556719835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9382784317673168742293113 7037088238254876556719835)
        ·
          refine ⟨10555632357382314835079753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7037088238254876556719835 10555632357382314835079753)
          ·
            refine ⟨7916724268036736126309815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10555632357382314835079753 7916724268036736126309815)
            ·
              refine ⟨11875086402055104189464723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7916724268036736126309815 11875086402055104189464723)
              ·
                refine ⟨17812629603082656284197085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11875086402055104189464723 17812629603082656284197085)
                ·
                  refine ⟨6679736101155996106573907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17812629603082656284197085 6679736101155996106573907)
                  ·
                    refine ⟨10019604151733994159860861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6679736101155996106573907 10019604151733994159860861)
                    ·
                      refine ⟨3757351556900247809947823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10019604151733994159860861 3757351556900247809947823)
                      ·
                        rfl

theorem cell23_7317416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_7317416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317416 prefixEnd_7317416 := by exact prefixLift 7317416
  have htrace : WordTrace (prefixWord ++ tailWord_7317416) baseStart_7317416 baseEnd_7317416 := by
    simpa [prefixWord, tailWord_7317416, baseEnd_7317416] using wordTrace_append hprefix tailTrace_7317416
  have hstable : (prefixWord ++ tailWord_7317416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317416).length < 2 ^ (prefixWord ++ tailWord_7317416).sum := by decide
  have hdescent : baseEnd_7317416 < baseStart_7317416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317431 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 6]
def baseStart_7317431 : Nat := 118140960795 + 7317431 * 2 ^ 59
def prefixEnd_7317431 : Nat := 4983230072969 + 3 ^ 40 * 7317431 * 2
def baseEnd_7317431 : Nat := 3757359259110065251260253

theorem tailTrace_7317431 : CollatzResearch.WordTrace tailWord_7317431 prefixEnd_7317431 3757359259110065251260253 := by
  unfold tailWord_7317431
  simp only [CollatzResearch.WordTrace]
  refine ⟨266888634353204679564800147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177925756235469786376533431 266888634353204679564800147)
  ·
    refine ⟨400332951529807019347200221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266888634353204679564800147 400332951529807019347200221)
    ·
      refine ⟨150124856823677632255200083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400332951529807019347200221 150124856823677632255200083)
      ·
        refine ⟨225187285235516448382800125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150124856823677632255200083 225187285235516448382800125)
        ·
          refine ⟨84445231963318668143550047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225187285235516448382800125 84445231963318668143550047)
          ·
            refine ⟨126667847944978002215325071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84445231963318668143550047 126667847944978002215325071)
            ·
              refine ⟨190001771917467003322987607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126667847944978002215325071 190001771917467003322987607)
              ·
                refine ⟨285002657876200504984481411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190001771917467003322987607 285002657876200504984481411)
                ·
                  refine ⟨427503986814300757476722117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285002657876200504984481411 427503986814300757476722117)
                  ·
                    refine ⟨80156997527681392026885397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 427503986814300757476722117 80156997527681392026885397)
                    ·
                      refine ⟨3757359259110065251260253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80156997527681392026885397 3757359259110065251260253)
                      ·
                        rfl

theorem cell23_7317431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_7317431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317431 prefixEnd_7317431 := by exact prefixLift 7317431
  have htrace : WordTrace (prefixWord ++ tailWord_7317431) baseStart_7317431 baseEnd_7317431 := by
    simpa [prefixWord, tailWord_7317431, baseEnd_7317431] using wordTrace_append hprefix tailTrace_7317431
  have hstable : (prefixWord ++ tailWord_7317431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317431).length < 2 ^ (prefixWord ++ tailWord_7317431).sum := by decide
  have hdescent : baseEnd_7317431 < baseStart_7317431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317512 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 4, 2, 2]
def baseStart_7317512 : Nat := 118140960795 + 7317512 * 2 ^ 59
def prefixEnd_7317512 : Nat := 4983230072969 + 3 ^ 40 * 7317512 * 2
def baseEnd_7317512 : Nat := 3757400851043079434347381

theorem tailTrace_7317512 : CollatzResearch.WordTrace tailWord_7317512 prefixEnd_7317512 3757400851043079434347381 := by
  unfold tailWord_7317512
  simp only [CollatzResearch.WordTrace]
  refine ⟨133445794332955615199249395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177927725777274153598999193 133445794332955615199249395)
  ·
    refine ⟨200168691499433422798874093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133445794332955615199249395 200168691499433422798874093)
    ·
      refine ⟨75063259312287533549577785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200168691499433422798874093 75063259312287533549577785)
      ·
        refine ⟨56297444484215650162183339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75063259312287533549577785 56297444484215650162183339)
        ·
          refine ⟨84446166726323475243275009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56297444484215650162183339 84446166726323475243275009)
          ·
            refine ⟨63334625044742606432456257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84446166726323475243275009 63334625044742606432456257)
            ·
              refine ⟨47500968783556954824342193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63334625044742606432456257 47500968783556954824342193)
              ·
                refine ⟨35625726587667716118256645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47500968783556954824342193 35625726587667716118256645)
                ·
                  refine ⟨6679823735187696772173121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35625726587667716118256645 6679823735187696772173121)
                  ·
                    refine ⟨5009867801390772579129841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6679823735187696772173121 5009867801390772579129841)
                    ·
                      refine ⟨3757400851043079434347381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5009867801390772579129841 3757400851043079434347381)
                      ·
                        rfl

theorem cell23_7317512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_7317512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317512 prefixEnd_7317512 := by exact prefixLift 7317512
  have htrace : WordTrace (prefixWord ++ tailWord_7317512) baseStart_7317512 baseEnd_7317512 := by
    simpa [prefixWord, tailWord_7317512, baseEnd_7317512] using wordTrace_append hprefix tailTrace_7317512
  have hstable : (prefixWord ++ tailWord_7317512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317512).length < 2 ^ (prefixWord ++ tailWord_7317512).sum := by decide
  have hdescent : baseEnd_7317512 < baseStart_7317512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317518 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 9]
def baseStart_7317518 : Nat := 118140960795 + 7317518 * 2 ^ 59
def prefixEnd_7317518 : Nat := 4983230072969 + 3 ^ 40 * 7317518 * 2
def baseEnd_7317518 : Nat := 417489325769667378985817

theorem tailTrace_7317518 : CollatzResearch.WordTrace tailWord_7317518 prefixEnd_7317518 417489325769667378985817 := by
  unfold tailWord_7317518
  simp only [CollatzResearch.WordTrace]
  refine ⟨33361475937986186677902151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177927871669259662282144805 33361475937986186677902151)
  ·
    refine ⟨50042213906979280016853227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33361475937986186677902151 50042213906979280016853227)
    ·
      refine ⟨75063320860468920025279841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50042213906979280016853227 75063320860468920025279841)
      ·
        refine ⟨56297490645351690018959881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75063320860468920025279841 56297490645351690018959881)
        ·
          refine ⟨42223117984013767514219911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56297490645351690018959881 42223117984013767514219911)
          ·
            refine ⟨63334676976020651271329867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42223117984013767514219911 63334676976020651271329867)
            ·
              refine ⟨95002015464030976906994801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63334676976020651271329867 95002015464030976906994801)
              ·
                refine ⟨71251511598023232680246101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95002015464030976906994801 71251511598023232680246101)
                ·
                  refine ⟨417489325769667378985817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71251511598023232680246101 417489325769667378985817)
                  ·
                    rfl

theorem cell23_7317518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_7317518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317518 prefixEnd_7317518 := by exact prefixLift 7317518
  have htrace : WordTrace (prefixWord ++ tailWord_7317518) baseStart_7317518 baseEnd_7317518 := by
    simpa [prefixWord, tailWord_7317518, baseEnd_7317518] using wordTrace_append hprefix tailTrace_7317518
  have hstable : (prefixWord ++ tailWord_7317518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317518).length < 2 ^ (prefixWord ++ tailWord_7317518).sum := by decide
  have hdescent : baseEnd_7317518 < baseStart_7317518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317535 : List Nat := [1, 1, 2, 4, 1, 2, 1, 6, 5]
def baseStart_7317535 : Nat := 118140960795 + 7317535 * 2 ^ 59
def prefixEnd_7317535 : Nat := 4983230072969 + 3 ^ 40 * 7317535 * 2
def baseEnd_7317535 : Nat := 417490295677570316039975

theorem tailTrace_7317535 : CollatzResearch.WordTrace tailWord_7317535 prefixEnd_7317535 417490295677570316039975 := by
  unfold tailWord_7317535
  simp only [CollatzResearch.WordTrace]
  refine ⟨266892427544827905326586059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177928285029885270217724039 266892427544827905326586059)
  ·
    refine ⟨400338641317241857989879089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266892427544827905326586059 400338641317241857989879089)
    ·
      refine ⟨300253980987931393492409317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400338641317241857989879089 300253980987931393492409317)
      ·
        refine ⟨56297621435237136279826747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300253980987931393492409317 56297621435237136279826747)
        ·
          refine ⟨84446432152855704419740121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56297621435237136279826747 84446432152855704419740121)
          ·
            refine ⟨63334824114641778314805091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84446432152855704419740121 63334824114641778314805091)
            ·
              refine ⟨95002236171962667472207637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63334824114641778314805091 95002236171962667472207637)
              ·
                refine ⟨4453229820560750037759733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95002236171962667472207637 4453229820560750037759733)
                ·
                  refine ⟨417490295677570316039975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4453229820560750037759733 417490295677570316039975)
                  ·
                    rfl

theorem cell23_7317535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 5].length) (baseStart_7317535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317535 prefixEnd_7317535 := by exact prefixLift 7317535
  have htrace : WordTrace (prefixWord ++ tailWord_7317535) baseStart_7317535 baseEnd_7317535 := by
    simpa [prefixWord, tailWord_7317535, baseEnd_7317535] using wordTrace_append hprefix tailTrace_7317535
  have hstable : (prefixWord ++ tailWord_7317535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317535).length < 2 ^ (prefixWord ++ tailWord_7317535).sum := by decide
  have hdescent : baseEnd_7317535 < baseStart_7317535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317548 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 6, 5]
def baseStart_7317548 : Nat := 118140960795 + 7317548 * 2 ^ 59
def prefixEnd_7317548 : Nat := 4983230072969 + 3 ^ 40 * 7317548 * 2
def baseEnd_7317548 : Nat := 1252473112115547097832405

theorem tailTrace_7317548 : CollatzResearch.WordTrace tailWord_7317548 prefixEnd_7317548 1252473112115547097832405 := by
  unfold tailWord_7317548
  simp only [CollatzResearch.WordTrace]
  refine ⟨133446450846890404273404649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177928601129187205697872865 133446450846890404273404649)
  ·
    refine ⟨100084838135167803205053487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133446450846890404273404649 100084838135167803205053487)
    ·
      refine ⟨150127257202751704807580231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100084838135167803205053487 150127257202751704807580231)
      ·
        refine ⟨225190885804127557211370347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150127257202751704807580231 225190885804127557211370347)
        ·
          refine ⟨337786328706191335817055521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225190885804127557211370347 337786328706191335817055521)
          ·
            refine ⟨253339746529643501862791641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337786328706191335817055521 253339746529643501862791641)
            ·
              refine ⟨190004809897232626397093731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253339746529643501862791641 190004809897232626397093731)
              ·
                refine ⟨285007214845848939595640597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190004809897232626397093731 285007214845848939595640597)
                ·
                  refine ⟨13359713195899169043545653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 285007214845848939595640597 13359713195899169043545653)
                  ·
                    refine ⟨1252473112115547097832405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13359713195899169043545653 1252473112115547097832405)
                    ·
                      rfl

theorem cell23_7317548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_7317548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317548 prefixEnd_7317548 := by exact prefixLift 7317548
  have htrace : WordTrace (prefixWord ++ tailWord_7317548) baseStart_7317548 baseEnd_7317548 := by
    simpa [prefixWord, tailWord_7317548, baseEnd_7317548] using wordTrace_append hprefix tailTrace_7317548
  have hstable : (prefixWord ++ tailWord_7317548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317548).length < 2 ^ (prefixWord ++ tailWord_7317548).sum := by decide
  have hdescent : baseEnd_7317548 < baseStart_7317548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317555 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 2, 5, 2]
def baseStart_7317555 : Nat := 118140960795 + 7317555 * 2 ^ 59
def prefixEnd_7317555 : Nat := 4983230072969 + 3 ^ 40 * 7317555 * 2
def baseEnd_7317555 : Nat := 3757422930711222766109683

theorem tailTrace_7317555 : CollatzResearch.WordTrace tailWord_7317555 prefixEnd_7317555 3757422930711222766109683 := by
  unfold tailWord_7317555
  simp only [CollatzResearch.WordTrace]
  refine ⟨266893157004755448742314119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177928771336503632494876079 266893157004755448742314119)
  ·
    refine ⟨400339735507133173113471179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266893157004755448742314119 400339735507133173113471179)
    ·
      refine ⟨600509603260699759670206769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400339735507133173113471179 600509603260699759670206769)
      ·
        refine ⟨450382202445524819752655077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600509603260699759670206769 450382202445524819752655077)
        ·
          refine ⟨84446662958535903703622827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 450382202445524819752655077 84446662958535903703622827)
          ·
            refine ⟨126669994437803855555434241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84446662958535903703622827 126669994437803855555434241)
            ·
              refine ⟨95002495828352891666575681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126669994437803855555434241 95002495828352891666575681)
              ·
                refine ⟨71251871871264668749931761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95002495828352891666575681 71251871871264668749931761)
                ·
                  refine ⟨53438903903448501562448821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71251871871264668749931761 53438903903448501562448821)
                  ·
                    refine ⟨5009897240948297021479577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53438903903448501562448821 5009897240948297021479577)
                    ·
                      refine ⟨3757422930711222766109683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5009897240948297021479577 3757422930711222766109683)
                      ·
                        rfl

theorem cell23_7317555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 5, 2].length) (baseStart_7317555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317555 prefixEnd_7317555 := by exact prefixLift 7317555
  have htrace : WordTrace (prefixWord ++ tailWord_7317555) baseStart_7317555 baseEnd_7317555 := by
    simpa [prefixWord, tailWord_7317555, baseEnd_7317555] using wordTrace_append hprefix tailTrace_7317555
  have hstable : (prefixWord ++ tailWord_7317555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317555).length < 2 ^ (prefixWord ++ tailWord_7317555).sum := by decide
  have hdescent : baseEnd_7317555 < baseStart_7317555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317565 : List Nat := [1, 4, 1, 3, 1, 1, 2, 3, 2, 5]
def baseStart_7317565 : Nat := 118140960795 + 7317565 * 2 ^ 59
def prefixEnd_7317565 : Nat := 4983230072969 + 3 ^ 40 * 7317565 * 2
def baseEnd_7317565 : Nat := 1252476021839255908994879

theorem tailTrace_7317565 : CollatzResearch.WordTrace tailWord_7317565 prefixEnd_7317565 1252476021839255908994879 := by
  unfold tailWord_7317565
  simp only [CollatzResearch.WordTrace]
  refine ⟨266893521734719220450178149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177929014489812813633452099 266893521734719220450178149)
  ·
    refine ⟨50042535325259853834408403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266893521734719220450178149 50042535325259853834408403)
    ·
      refine ⟨75063802987889780751612605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50042535325259853834408403 75063802987889780751612605)
      ·
        refine ⟨28148926120458667781854727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75063802987889780751612605 28148926120458667781854727)
        ·
          refine ⟨42223389180688001672782091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28148926120458667781854727 42223389180688001672782091)
          ·
            refine ⟨63335083771032002509173137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42223389180688001672782091 63335083771032002509173137)
            ·
              refine ⟨47501312828274001881879853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63335083771032002509173137 47501312828274001881879853)
              ·
                refine ⟨17812992310602750705704945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47501312828274001881879853 17812992310602750705704945)
                ·
                  refine ⟨13359744232952063029278709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17812992310602750705704945 13359744232952063029278709)
                  ·
                    refine ⟨1252476021839255908994879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13359744232952063029278709 1252476021839255908994879)
                    ·
                      rfl

theorem cell23_7317565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_7317565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317565 prefixEnd_7317565 := by exact prefixLift 7317565
  have htrace : WordTrace (prefixWord ++ tailWord_7317565) baseStart_7317565 baseEnd_7317565 := by
    simpa [prefixWord, tailWord_7317565, baseEnd_7317565] using wordTrace_append hprefix tailTrace_7317565
  have hstable : (prefixWord ++ tailWord_7317565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317565).length < 2 ^ (prefixWord ++ tailWord_7317565).sum := by decide
  have hdescent : baseEnd_7317565 < baseStart_7317565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317569 : List Nat := [1, 2, 5, 1, 2, 3, 1, 3, 5]
def baseStart_7317569 : Nat := 118140960795 + 7317569 * 2 ^ 59
def prefixEnd_7317569 : Nat := 4983230072969 + 3 ^ 40 * 7317569 * 2
def baseEnd_7317569 : Nat := 417492235493376190148291

theorem tailTrace_7317569 : CollatzResearch.WordTrace tailWord_7317569 prefixEnd_7317569 417492235493376190148291 := by
  unfold tailWord_7317569
  simp only [CollatzResearch.WordTrace]
  refine ⟨266893667626704729133323761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177929111751136486088882507 266893667626704729133323761)
  ·
    refine ⟨200170250720028546849992821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266893667626704729133323761 200170250720028546849992821)
    ·
      refine ⟨18765961005002676267186827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200170250720028546849992821 18765961005002676267186827)
      ·
        refine ⟨28148941507504014400780241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18765961005002676267186827 28148941507504014400780241)
        ·
          refine ⟨21111706130628010800585181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28148941507504014400780241 21111706130628010800585181)
          ·
            refine ⟨7916889798985504050219443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21111706130628010800585181 7916889798985504050219443)
            ·
              refine ⟨11875334698478256075329165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7916889798985504050219443 11875334698478256075329165)
              ·
                refine ⟨4453250511929346028248437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11875334698478256075329165 4453250511929346028248437)
                ·
                  refine ⟨417492235493376190148291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4453250511929346028248437 417492235493376190148291)
                  ·
                    rfl

theorem cell23_7317569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 5].length) (baseStart_7317569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317569 prefixEnd_7317569 := by exact prefixLift 7317569
  have htrace : WordTrace (prefixWord ++ tailWord_7317569) baseStart_7317569 baseEnd_7317569 := by
    simpa [prefixWord, tailWord_7317569, baseEnd_7317569] using wordTrace_append hprefix tailTrace_7317569
  have hstable : (prefixWord ++ tailWord_7317569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317569).length < 2 ^ (prefixWord ++ tailWord_7317569).sum := by decide
  have hdescent : baseEnd_7317569 < baseStart_7317569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317642 : List Nat := [3, 1, 2, 3, 1, 3, 2, 2, 6]
def baseStart_7317642 : Nat := 118140960795 + 7317642 * 2 ^ 59
def prefixEnd_7317642 : Nat := 4983230072969 + 3 ^ 40 * 7317642 * 2
def baseEnd_7317642 : Nat := 417496400392018213969087

theorem tailTrace_7317642 : CollatzResearch.WordTrace tailWord_7317642 prefixEnd_7317642 417496400392018213969087 := by
  unfold tailWord_7317642
  simp only [CollatzResearch.WordTrace]
  refine ⟨66724082538860065650182795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177930886770293508400487453 66724082538860065650182795)
  ·
    refine ⟨100086123808290098475274193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66724082538860065650182795 100086123808290098475274193)
    ·
      refine ⟨75064592856217573856455645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100086123808290098475274193 75064592856217573856455645)
      ·
        refine ⟨28149222321081590196170867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75064592856217573856455645 28149222321081590196170867)
        ·
          refine ⟨42223833481622385294256301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28149222321081590196170867 42223833481622385294256301)
          ·
            refine ⟨15833937555608394485346113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42223833481622385294256301 15833937555608394485346113)
            ·
              refine ⟨11875453166706295864009585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15833937555608394485346113 11875453166706295864009585)
              ·
                refine ⟨8906589875029721898007189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11875453166706295864009585 8906589875029721898007189)
                ·
                  refine ⟨417496400392018213969087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8906589875029721898007189 417496400392018213969087)
                  ·
                    rfl

theorem cell23_7317642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 6].length) (baseStart_7317642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317642 prefixEnd_7317642 := by exact prefixLift 7317642
  have htrace : WordTrace (prefixWord ++ tailWord_7317642) baseStart_7317642 baseEnd_7317642 := by
    simpa [prefixWord, tailWord_7317642, baseEnd_7317642] using wordTrace_append hprefix tailTrace_7317642
  have hstable : (prefixWord ++ tailWord_7317642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317642).length < 2 ^ (prefixWord ++ tailWord_7317642).sum := by decide
  have hdescent : baseEnd_7317642 < baseStart_7317642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317646 : List Nat := [4, 1, 1, 3, 3, 1, 1, 4, 1, 4]
def baseStart_7317646 : Nat := 118140960795 + 7317646 * 2 ^ 59
def prefixEnd_7317646 : Nat := 4983230072969 + 3 ^ 40 * 7317646 * 2
def baseEnd_7317646 : Nat := 1252489885816927303357255

theorem tailTrace_7317646 : CollatzResearch.WordTrace tailWord_7317646 prefixEnd_7317646 1252489885816927303357255 := by
  unfold tailWord_7317646
  simp only [CollatzResearch.WordTrace]
  refine ⟨33362059505928221410484599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177930984031617180855917861 33362059505928221410484599)
  ·
    refine ⟨50043089258892332115726899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33362059505928221410484599 50043089258892332115726899)
    ·
      refine ⟨75064633888338498173590349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50043089258892332115726899 75064633888338498173590349)
      ·
        refine ⟨28149237708126936815096381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75064633888338498173590349 28149237708126936815096381)
        ·
          refine ⟨10555964140547601305661143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28149237708126936815096381 10555964140547601305661143)
          ·
            refine ⟨15833946210821401958491715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10555964140547601305661143 15833946210821401958491715)
            ·
              refine ⟨23750919316232102937737573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15833946210821401958491715 23750919316232102937737573)
              ·
                refine ⟨4453297371793519300825795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23750919316232102937737573 4453297371793519300825795)
                ·
                  refine ⟨6679946057690278951238693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4453297371793519300825795 6679946057690278951238693)
                  ·
                    refine ⟨1252489885816927303357255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6679946057690278951238693 1252489885816927303357255)
                    ·
                      rfl

theorem cell23_7317646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_7317646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317646 prefixEnd_7317646 := by exact prefixLift 7317646
  have htrace : WordTrace (prefixWord ++ tailWord_7317646) baseStart_7317646 baseEnd_7317646 := by
    simpa [prefixWord, tailWord_7317646, baseEnd_7317646] using wordTrace_append hprefix tailTrace_7317646
  have hstable : (prefixWord ++ tailWord_7317646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317646).length < 2 ^ (prefixWord ++ tailWord_7317646).sum := by decide
  have hdescent : baseEnd_7317646 < baseStart_7317646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317695 : List Nat := [1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 5]
def baseStart_7317695 : Nat := 118140960795 + 7317695 * 2 ^ 59
def prefixEnd_7317695 : Nat := 4983230072969 + 3 ^ 40 * 7317695 * 2
def baseEnd_7317695 : Nat := 3757494818002852218359039

theorem tailTrace_7317695 : CollatzResearch.WordTrace tailWord_7317695 prefixEnd_7317695 3757494818002852218359039 := by
  unfold tailWord_7317695
  simp only [CollatzResearch.WordTrace]
  refine ⟨266898263224248252652410539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177932175482832168434940359 266898263224248252652410539)
  ·
    refine ⟨400347394836372378978615809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266898263224248252652410539 400347394836372378978615809)
    ·
      refine ⟨300260546127279284233961857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400347394836372378978615809 300260546127279284233961857)
      ·
        refine ⟨225195409595459463175471393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300260546127279284233961857 225195409595459463175471393)
        ·
          refine ⟨168896557196594597381603545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225195409595459463175471393 168896557196594597381603545)
          ·
            refine ⟨126672417897445948036202659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168896557196594597381603545 126672417897445948036202659)
            ·
              refine ⟨190008626846168922054303989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126672417897445948036202659 190008626846168922054303989)
              ·
                refine ⟨17813308766828336442590999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190008626846168922054303989 17813308766828336442590999)
                ·
                  refine ⟨26719963150242504663886499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17813308766828336442590999 26719963150242504663886499)
                  ·
                    refine ⟨40079944725363756995829749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26719963150242504663886499 40079944725363756995829749)
                    ·
                      refine ⟨3757494818002852218359039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40079944725363756995829749 3757494818002852218359039)
                      ·
                        rfl

theorem cell23_7317695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_7317695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317695 prefixEnd_7317695 := by exact prefixLift 7317695
  have htrace : WordTrace (prefixWord ++ tailWord_7317695) baseStart_7317695 baseEnd_7317695 := by
    simpa [prefixWord, tailWord_7317695, baseEnd_7317695] using wordTrace_append hprefix tailTrace_7317695
  have hstable : (prefixWord ++ tailWord_7317695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317695).length < 2 ^ (prefixWord ++ tailWord_7317695).sum := by decide
  have hdescent : baseEnd_7317695 < baseStart_7317695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317722 : List Nat := [3, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4]
def baseStart_7317722 : Nat := 118140960795 + 7317722 * 2 ^ 59
def prefixEnd_7317722 : Nat := 4983230072969 + 3 ^ 40 * 7317722 * 2
def baseEnd_7317722 : Nat := 3757508681980523612721415

theorem tailTrace_7317722 : CollatzResearch.WordTrace tailWord_7317722 prefixEnd_7317722 3757508681980523612721415 := by
  unfold tailWord_7317722
  simp only [CollatzResearch.WordTrace]
  refine ⟨66724811998787609065910855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177932831996766957509095613 66724811998787609065910855)
  ·
    refine ⟨100087217998181413598866283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66724811998787609065910855 100087217998181413598866283)
    ·
      refine ⟨150130826997272120398299425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100087217998181413598866283 150130826997272120398299425)
      ·
        refine ⟨112598120247954090298724569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150130826997272120398299425 112598120247954090298724569)
        ·
          refine ⟨84448590185965567724043427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112598120247954090298724569 84448590185965567724043427)
          ·
            refine ⟨126672885278948351586065141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84448590185965567724043427 126672885278948351586065141)
            ·
              refine ⟨11875582994901407961193607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126672885278948351586065141 11875582994901407961193607)
              ·
                refine ⟨17813374492352111941790411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11875582994901407961193607 17813374492352111941790411)
                ·
                  refine ⟨26720061738528167912685617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17813374492352111941790411 26720061738528167912685617)
                  ·
                    refine ⟨20040046303896125934514213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26720061738528167912685617 20040046303896125934514213)
                    ·
                      refine ⟨3757508681980523612721415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20040046303896125934514213 3757508681980523612721415)
                      ·
                        rfl

theorem cell23_7317722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_7317722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317722 prefixEnd_7317722 := by exact prefixLift 7317722
  have htrace : WordTrace (prefixWord ++ tailWord_7317722) baseStart_7317722 baseEnd_7317722 := by
    simpa [prefixWord, tailWord_7317722, baseEnd_7317722] using wordTrace_append hprefix tailTrace_7317722
  have hstable : (prefixWord ++ tailWord_7317722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317722).length < 2 ^ (prefixWord ++ tailWord_7317722).sum := by decide
  have hdescent : baseEnd_7317722 < baseStart_7317722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317729 : List Nat := [1, 2, 3, 1, 3, 1, 4, 2, 1, 2, 3]
def baseStart_7317729 : Nat := 118140960795 + 7317729 * 2 ^ 59
def prefixEnd_7317729 : Nat := 4983230072969 + 3 ^ 40 * 7317729 * 2
def baseEnd_7317729 : Nat := 3757512276345105085333883

theorem tailTrace_7317729 : CollatzResearch.WordTrace tailWord_7317729 prefixEnd_7317729 3757512276345105085333883 := by
  unfold tailWord_7317729
  simp only [CollatzResearch.WordTrace]
  refine ⟨266899503306125076459148241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177933002204083384306098827 266899503306125076459148241)
  ·
    refine ⟨200174627479593807344361181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266899503306125076459148241 200174627479593807344361181)
    ·
      refine ⟨75065485304847677754135443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200174627479593807344361181 75065485304847677754135443)
      ·
        refine ⟨112598227957271516631203165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75065485304847677754135443 112598227957271516631203165)
        ·
          refine ⟨42224335483976818736701187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112598227957271516631203165 42224335483976818736701187)
          ·
            refine ⟨63336503225965228105051781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42224335483976818736701187 63336503225965228105051781)
            ·
              refine ⟨11875594354868480269697209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63336503225965228105051781 11875594354868480269697209)
              ·
                refine ⟨8906695766151360202272907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11875594354868480269697209 8906695766151360202272907)
                ·
                  refine ⟨13360043649227040303409361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8906695766151360202272907 13360043649227040303409361)
                  ·
                    refine ⟨10020032736920280227557021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13360043649227040303409361 10020032736920280227557021)
                    ·
                      refine ⟨3757512276345105085333883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10020032736920280227557021 3757512276345105085333883)
                      ·
                        rfl

theorem cell23_7317729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_7317729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317729 prefixEnd_7317729 := by exact prefixLift 7317729
  have htrace : WordTrace (prefixWord ++ tailWord_7317729) baseStart_7317729 baseEnd_7317729 := by
    simpa [prefixWord, tailWord_7317729, baseEnd_7317729] using wordTrace_append hprefix tailTrace_7317729
  have hstable : (prefixWord ++ tailWord_7317729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317729).length < 2 ^ (prefixWord ++ tailWord_7317729).sum := by decide
  have hdescent : baseEnd_7317729 < baseStart_7317729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317742 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_7317742 : Nat := 118140960795 + 7317742 * 2 ^ 59
def prefixEnd_7317742 : Nat := 4983230072969 + 3 ^ 40 * 7317742 * 2
def baseEnd_7317742 : Nat := 3757518951593613534471323

theorem tailTrace_7317742 : CollatzResearch.WordTrace tailWord_7317742 prefixEnd_7317742 3757518951593613534471323 := by
  unfold tailWord_7317742
  simp only [CollatzResearch.WordTrace]
  refine ⟨33362497181884747459921435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177933318303385319786247653 33362497181884747459921435)
  ·
    refine ⟨50043745772827121189882153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33362497181884747459921435 50043745772827121189882153)
    ·
      refine ⟨37532809329620340892411615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50043745772827121189882153 37532809329620340892411615)
      ·
        refine ⟨56299213994430511338617423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37532809329620340892411615 56299213994430511338617423)
        ·
          refine ⟨84448820991645767007926135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56299213994430511338617423 84448820991645767007926135)
          ·
            refine ⟨126673231487468650511889203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84448820991645767007926135 126673231487468650511889203)
            ·
              refine ⟨190009847231202975767833805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126673231487468650511889203 190009847231202975767833805)
              ·
                refine ⟨71253692711701115912937677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190009847231202975767833805 71253692711701115912937677)
                ·
                  refine ⟨26720134766887918467351629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71253692711701115912937677 26720134766887918467351629)
                  ·
                    refine ⟨10020050537582969425256861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26720134766887918467351629 10020050537582969425256861)
                    ·
                      refine ⟨3757518951593613534471323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10020050537582969425256861 3757518951593613534471323)
                      ·
                        rfl

theorem cell23_7317742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_7317742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317742 prefixEnd_7317742 := by exact prefixLift 7317742
  have htrace : WordTrace (prefixWord ++ tailWord_7317742) baseStart_7317742 baseEnd_7317742 := by
    simpa [prefixWord, tailWord_7317742, baseEnd_7317742] using wordTrace_append hprefix tailTrace_7317742
  have hstable : (prefixWord ++ tailWord_7317742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317742).length < 2 ^ (prefixWord ++ tailWord_7317742).sum := by decide
  have hdescent : baseEnd_7317742 < baseStart_7317742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317743 : List Nat := [1, 1, 2, 1, 6, 1, 3, 3, 1, 2, 2]
def baseStart_7317743 : Nat := 118140960795 + 7317743 * 2 ^ 59
def prefixEnd_7317743 : Nat := 4983230072969 + 3 ^ 40 * 7317743 * 2
def baseEnd_7317743 : Nat := 3757519465074268030558819

theorem tailTrace_7317743 : CollatzResearch.WordTrace tailWord_7317743 prefixEnd_7317743 3757519465074268030558819 := by
  unfold tailWord_7317743
  simp only [CollatzResearch.WordTrace]
  refine ⟨266900013928074356850157883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177933342618716237900105255 266900013928074356850157883)
  ·
    refine ⟨400350020892111535275236825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266900013928074356850157883 400350020892111535275236825)
    ·
      refine ⟨300262515669083651456427619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400350020892111535275236825 300262515669083651456427619)
      ·
        refine ⟨450393773503625477184641429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300262515669083651456427619 450393773503625477184641429)
        ·
          refine ⟨21112208132982444243030067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 450393773503625477184641429 21112208132982444243030067)
          ·
            refine ⟨31668312199473666364545101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21112208132982444243030067 31668312199473666364545101)
            ·
              refine ⟨11875617074802624886704413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31668312199473666364545101 11875617074802624886704413)
              ·
                refine ⟨4453356403050984332514155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11875617074802624886704413 4453356403050984332514155)
                ·
                  refine ⟨6680034604576476498771233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4453356403050984332514155 6680034604576476498771233)
                  ·
                    refine ⟨5010025953432357374078425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6680034604576476498771233 5010025953432357374078425)
                    ·
                      refine ⟨3757519465074268030558819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5010025953432357374078425 3757519465074268030558819)
                      ·
                        rfl

theorem cell23_7317743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 1, 2, 2].length) (baseStart_7317743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317743 prefixEnd_7317743 := by exact prefixLift 7317743
  have htrace : WordTrace (prefixWord ++ tailWord_7317743) baseStart_7317743 baseEnd_7317743 := by
    simpa [prefixWord, tailWord_7317743, baseEnd_7317743] using wordTrace_append hprefix tailTrace_7317743
  have hstable : (prefixWord ++ tailWord_7317743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317743).length < 2 ^ (prefixWord ++ tailWord_7317743).sum := by decide
  have hdescent : baseEnd_7317743 < baseStart_7317743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317759 : List Nat := [1, 1, 2, 2, 1, 4, 2, 4, 2, 1, 3]
def baseStart_7317759 : Nat := 118140960795 + 7317759 * 2 ^ 59
def prefixEnd_7317759 : Nat := 4983230072969 + 3 ^ 40 * 7317759 * 2
def baseEnd_7317759 : Nat := 3757527680764739967958745

theorem tailTrace_7317759 : CollatzResearch.WordTrace tailWord_7317759 prefixEnd_7317759 3757527680764739967958745 := by
  unfold tailWord_7317759
  simp only [CollatzResearch.WordTrace]
  refine ⟨266900597496016391582740331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177933731664010927721826887 266900597496016391582740331)
  ·
    refine ⟨400350896244024587374110497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266900597496016391582740331 400350896244024587374110497)
    ·
      refine ⟨300263172183018440530582873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400350896244024587374110497 300263172183018440530582873)
      ·
        refine ⟨225197379137263830397937155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300263172183018440530582873 225197379137263830397937155)
        ·
          refine ⟨337796068705895745596905733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225197379137263830397937155 337796068705895745596905733)
          ·
            refine ⟨63336762882355452299419825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337796068705895745596905733 63336762882355452299419825)
            ·
              refine ⟨47502572161766589224564869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63336762882355452299419825 47502572161766589224564869)
              ·
                refine ⟨8906732280331235479605913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47502572161766589224564869 8906732280331235479605913)
                ·
                  refine ⟨6680049210248426609704435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8906732280331235479605913 6680049210248426609704435)
                  ·
                    refine ⟨10020073815372639914556653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6680049210248426609704435 10020073815372639914556653)
                    ·
                      refine ⟨3757527680764739967958745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10020073815372639914556653 3757527680764739967958745)
                      ·
                        rfl

theorem cell23_7317759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 1, 3].length) (baseStart_7317759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317759 prefixEnd_7317759 := by exact prefixLift 7317759
  have htrace : WordTrace (prefixWord ++ tailWord_7317759) baseStart_7317759 baseEnd_7317759 := by
    simpa [prefixWord, tailWord_7317759, baseEnd_7317759] using wordTrace_append hprefix tailTrace_7317759
  have hstable : (prefixWord ++ tailWord_7317759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317759).length < 2 ^ (prefixWord ++ tailWord_7317759).sum := by decide
  have hdescent : baseEnd_7317759 < baseStart_7317759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317775 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 2, 6]
def baseStart_7317775 : Nat := 118140960795 + 7317775 * 2 ^ 59
def prefixEnd_7317775 : Nat := 4983230072969 + 3 ^ 40 * 7317775 * 2
def baseEnd_7317775 : Nat := 1252511965485070635119557

theorem tailTrace_7317775 : CollatzResearch.WordTrace tailWord_7317775 prefixEnd_7317775 1252511965485070635119557 := by
  unfold tailWord_7317775
  simp only [CollatzResearch.WordTrace]
  refine ⟨266901181063958426315322779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177934120709305617543548519 266901181063958426315322779)
  ·
    refine ⟨400351771595937639472984169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266901181063958426315322779 400351771595937639472984169)
    ·
      refine ⟨300263828696953229604738127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400351771595937639472984169 300263828696953229604738127)
      ·
        refine ⟨450395743045429844407107191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300263828696953229604738127 450395743045429844407107191)
        ·
          refine ⟨675593614568144766610660787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450395743045429844407107191 675593614568144766610660787)
          ·
            refine ⟨1013390421852217149915991181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675593614568144766610660787 1013390421852217149915991181)
            ·
              refine ⟨380021408194581431218496693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1013390421852217149915991181 380021408194581431218496693)
              ·
                refine ⟨35627007018242009176734065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 380021408194581431218496693 35627007018242009176734065)
                ·
                  refine ⟨26720255263681506882550549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35627007018242009176734065 26720255263681506882550549)
                  ·
                    refine ⟨1252511965485070635119557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26720255263681506882550549 1252511965485070635119557)
                    ·
                      rfl

theorem cell23_7317775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 6].length) (baseStart_7317775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317775 prefixEnd_7317775 := by exact prefixLift 7317775
  have htrace : WordTrace (prefixWord ++ tailWord_7317775) baseStart_7317775 baseEnd_7317775 := by
    simpa [prefixWord, tailWord_7317775, baseEnd_7317775] using wordTrace_append hprefix tailTrace_7317775
  have hstable : (prefixWord ++ tailWord_7317775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317775).length < 2 ^ (prefixWord ++ tailWord_7317775).sum := by decide
  have hdescent : baseEnd_7317775 < baseStart_7317775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317786 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2]
def baseStart_7317786 : Nat := 118140960795 + 7317786 * 2 ^ 59
def prefixEnd_7317786 : Nat := 4983230072969 + 3 ^ 40 * 7317786 * 2
def baseEnd_7317786 : Nat := 3757541544742411362321121

theorem tailTrace_7317786 : CollatzResearch.WordTrace tailWord_7317786 prefixEnd_7317786 3757541544742411362321121 := by
  unfold tailWord_7317786
  simp only [CollatzResearch.WordTrace]
  refine ⟨66725395566729643798493303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177934388177945716795982141 66725395566729643798493303)
  ·
    refine ⟨100088093350094465697739955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66725395566729643798493303 100088093350094465697739955)
    ·
      refine ⟨150132140025141698546609933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100088093350094465697739955 150132140025141698546609933)
      ·
        refine ⟨56299552509428136954978725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150132140025141698546609933 56299552509428136954978725)
        ·
          refine ⟨10556166095517775679058511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56299552509428136954978725 10556166095517775679058511)
          ·
            refine ⟨15834249143276663518587767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10556166095517775679058511 15834249143276663518587767)
            ·
              refine ⟨23751373714914995277881651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15834249143276663518587767 23751373714914995277881651)
              ·
                refine ⟨35627060572372492916822477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23751373714914995277881651 35627060572372492916822477)
                ·
                  refine ⟨13360147714639684843808429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35627060572372492916822477 13360147714639684843808429)
                  ·
                    refine ⟨5010055392989881816428161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13360147714639684843808429 5010055392989881816428161)
                    ·
                      refine ⟨3757541544742411362321121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5010055392989881816428161 3757541544742411362321121)
                      ·
                        rfl

theorem cell23_7317786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_7317786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317786 prefixEnd_7317786 := by exact prefixLift 7317786
  have htrace : WordTrace (prefixWord ++ tailWord_7317786) baseStart_7317786 baseEnd_7317786 := by
    simpa [prefixWord, tailWord_7317786, baseEnd_7317786] using wordTrace_append hprefix tailTrace_7317786
  have hstable : (prefixWord ++ tailWord_7317786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317786).length < 2 ^ (prefixWord ++ tailWord_7317786).sum := by decide
  have hdescent : baseEnd_7317786 < baseStart_7317786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317815 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 7]
def baseStart_7317815 : Nat := 118140960795 + 7317815 * 2 ^ 59
def prefixEnd_7317815 : Nat := 4983230072969 + 3 ^ 40 * 7317815 * 2
def baseEnd_7317815 : Nat := 3757556435681391748858487

theorem tailTrace_7317815 : CollatzResearch.WordTrace tailWord_7317815 prefixEnd_7317815 3757556435681391748858487 := by
  unfold tailWord_7317815
  simp only [CollatzResearch.WordTrace]
  refine ⟨266902639983813513146778899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177935093322542342097852599 266902639983813513146778899)
  ·
    refine ⟨400353959975720269720168349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266902639983813513146778899 400353959975720269720168349)
    ·
      refine ⟨150132734990895101145063131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400353959975720269720168349 150132734990895101145063131)
      ·
        refine ⟨225199102486342651717594697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150132734990895101145063131 225199102486342651717594697)
        ·
          refine ⟨168899326864756988788196023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225199102486342651717594697 168899326864756988788196023)
          ·
            refine ⟨253348990297135483182294035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168899326864756988788196023 253348990297135483182294035)
            ·
              refine ⟨380023485445703224773441053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253348990297135483182294035 380023485445703224773441053)
              ·
                refine ⟨142508807042138709290040395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380023485445703224773441053 142508807042138709290040395)
                ·
                  refine ⟨213763210563208063935060593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142508807042138709290040395 213763210563208063935060593)
                  ·
                    refine ⟨160322407922406047951295445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 213763210563208063935060593 160322407922406047951295445)
                    ·
                      refine ⟨3757556435681391748858487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160322407922406047951295445 3757556435681391748858487)
                      ·
                        rfl

theorem cell23_7317815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_7317815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317815 prefixEnd_7317815 := by exact prefixLift 7317815
  have htrace : WordTrace (prefixWord ++ tailWord_7317815) baseStart_7317815 baseEnd_7317815 := by
    simpa [prefixWord, tailWord_7317815, baseEnd_7317815] using wordTrace_append hprefix tailTrace_7317815
  have hstable : (prefixWord ++ tailWord_7317815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317815).length < 2 ^ (prefixWord ++ tailWord_7317815).sum := by decide
  have hdescent : baseEnd_7317815 < baseStart_7317815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317816 : List Nat := [2, 1, 2, 1, 3, 1, 3, 4, 2, 2, 2]
def baseStart_7317816 : Nat := 118140960795 + 7317816 * 2 ^ 59
def prefixEnd_7317816 : Nat := 4983230072969 + 3 ^ 40 * 7317816 * 2
def baseEnd_7317816 : Nat := 3757556949162046244945983

theorem tailTrace_7317816 : CollatzResearch.WordTrace tailWord_7317816 prefixEnd_7317816 3757556949162046244945983 := by
  unfold tailWord_7317816
  simp only [CollatzResearch.WordTrace]
  refine ⟨133451338228404945158782651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177935117637873260211710201 133451338228404945158782651)
  ·
    refine ⟨200177007342607417738173977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133451338228404945158782651 200177007342607417738173977)
    ·
      refine ⟨150132755506955563303630483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200177007342607417738173977 150132755506955563303630483)
      ·
        refine ⟨225199133260433344955445725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150132755506955563303630483 225199133260433344955445725)
        ·
          refine ⟨84449674972662504358292147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225199133260433344955445725 84449674972662504358292147)
          ·
            refine ⟨126674512458993756537438221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84449674972662504358292147 126674512458993756537438221)
            ·
              refine ⟨47502942172122658701539333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126674512458993756537438221 47502942172122658701539333)
              ·
                refine ⟨8906801657272998506538625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47502942172122658701539333 8906801657272998506538625)
                ·
                  refine ⟨6680101242954748879903969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8906801657272998506538625 6680101242954748879903969)
                  ·
                    refine ⟨5010075932216061659927977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6680101242954748879903969 5010075932216061659927977)
                    ·
                      refine ⟨3757556949162046244945983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5010075932216061659927977 3757556949162046244945983)
                      ·
                        rfl

theorem cell23_7317816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 2, 2, 2].length) (baseStart_7317816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317816 prefixEnd_7317816 := by exact prefixLift 7317816
  have htrace : WordTrace (prefixWord ++ tailWord_7317816) baseStart_7317816 baseEnd_7317816 := by
    simpa [prefixWord, tailWord_7317816, baseEnd_7317816] using wordTrace_append hprefix tailTrace_7317816
  have hstable : (prefixWord ++ tailWord_7317816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317816).length < 2 ^ (prefixWord ++ tailWord_7317816).sum := by decide
  have hdescent : baseEnd_7317816 < baseStart_7317816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317832 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 1, 5, 3]
def baseStart_7317832 : Nat := 118140960795 + 7317832 * 2 ^ 59
def prefixEnd_7317832 : Nat := 4983230072969 + 3 ^ 40 * 7317832 * 2
def baseEnd_7317832 : Nat := 3757565164852518182345909

theorem tailTrace_7317832 : CollatzResearch.WordTrace tailWord_7317832 prefixEnd_7317832 3757565164852518182345909 := by
  unfold tailWord_7317832
  simp only [CollatzResearch.WordTrace]
  refine ⟨133451630012375962525073875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177935506683167950033431833 133451630012375962525073875)
  ·
    refine ⟨200177445018563943787610813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133451630012375962525073875 200177445018563943787610813)
    ·
      refine ⟨75066541881961478920354055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200177445018563943787610813 75066541881961478920354055)
      ·
        refine ⟨112599812822942218380531083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75066541881961478920354055 112599812822942218380531083)
        ·
          refine ⟨168899719234413327570796625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112599812822942218380531083 168899719234413327570796625)
          ·
            refine ⟨126674789425809995678097469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168899719234413327570796625 126674789425809995678097469)
            ·
              refine ⟨47503046034678748379286551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126674789425809995678097469 47503046034678748379286551)
              ·
                refine ⟨71254569052018122568929827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47503046034678748379286551 71254569052018122568929827)
                ·
                  refine ⟨106881853578027183853394741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71254569052018122568929827 106881853578027183853394741)
                  ·
                    refine ⟨10020173772940048486255757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106881853578027183853394741 10020173772940048486255757)
                    ·
                      refine ⟨3757565164852518182345909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10020173772940048486255757 3757565164852518182345909)
                      ·
                        rfl

theorem cell23_7317832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_7317832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317832 prefixEnd_7317832 := by exact prefixLift 7317832
  have htrace : WordTrace (prefixWord ++ tailWord_7317832) baseStart_7317832 baseEnd_7317832 := by
    simpa [prefixWord, tailWord_7317832, baseEnd_7317832] using wordTrace_append hprefix tailTrace_7317832
  have hstable : (prefixWord ++ tailWord_7317832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317832).length < 2 ^ (prefixWord ++ tailWord_7317832).sum := by decide
  have hdescent : baseEnd_7317832 < baseStart_7317832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317854 : List Nat := [4, 4, 2, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_7317854 : Nat := 118140960795 + 7317854 * 2 ^ 59
def prefixEnd_7317854 : Nat := 4983230072969 + 3 ^ 40 * 7317854 * 2
def baseEnd_7317854 : Nat := 3757576461426917096270809

theorem tailTrace_7317854 : CollatzResearch.WordTrace tailWord_7317854 prefixEnd_7317854 3757576461426917096270809 := by
  unfold tailWord_7317854
  simp only [CollatzResearch.WordTrace]
  refine ⟨33363007803834027850931077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177936041620448148538299077 33363007803834027850931077)
  ·
    refine ⟨6255563963218880222049577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33363007803834027850931077 6255563963218880222049577)
    ·
      refine ⟨4691672972414160166537183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6255563963218880222049577 4691672972414160166537183)
      ·
        refine ⟨7037509458621240249805775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4691672972414160166537183 7037509458621240249805775)
        ·
          refine ⟨10556264187931860374708663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7037509458621240249805775 10556264187931860374708663)
          ·
            refine ⟨15834396281897790562062995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10556264187931860374708663 15834396281897790562062995)
            ·
              refine ⟨23751594422846685843094493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15834396281897790562062995 23751594422846685843094493)
              ·
                refine ⟨8906847908567507191160435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23751594422846685843094493 8906847908567507191160435)
                ·
                  refine ⟨13360271862851260786740653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8906847908567507191160435 13360271862851260786740653)
                  ·
                    refine ⟨5010101948569222795027745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13360271862851260786740653 5010101948569222795027745)
                    ·
                      refine ⟨3757576461426917096270809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5010101948569222795027745 3757576461426917096270809)
                      ·
                        rfl

theorem cell23_7317854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_7317854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317854 prefixEnd_7317854 := by exact prefixLift 7317854
  have htrace : WordTrace (prefixWord ++ tailWord_7317854) baseStart_7317854 baseEnd_7317854 := by
    simpa [prefixWord, tailWord_7317854, baseEnd_7317854] using wordTrace_append hprefix tailTrace_7317854
  have hstable : (prefixWord ++ tailWord_7317854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317854).length < 2 ^ (prefixWord ++ tailWord_7317854).sum := by decide
  have hdescent : baseEnd_7317854 < baseStart_7317854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317856 : List Nat := [2, 1, 1, 3, 5, 1, 2, 3, 5]
def baseStart_7317856 : Nat := 118140960795 + 7317856 * 2 ^ 59
def prefixEnd_7317856 : Nat := 4983230072969 + 3 ^ 40 * 7317856 * 2
def baseEnd_7317856 : Nat := 417508609820914009827311

theorem tailTrace_7317856 : CollatzResearch.WordTrace tailWord_7317856 prefixEnd_7317856 417508609820914009827311 := by
  unfold tailWord_7317856
  simp only [CollatzResearch.WordTrace]
  refine ⟨133452067688332488574510711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177936090251109984766014281 133452067688332488574510711)
  ·
    refine ⟨200178101532498732861766067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133452067688332488574510711 200178101532498732861766067)
    ·
      refine ⟨300267152298748099292649101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200178101532498732861766067 300267152298748099292649101)
      ·
        refine ⟨112600182112030537234743413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300267152298748099292649101 112600182112030537234743413)
        ·
          refine ⟨10556267073002862865757195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112600182112030537234743413 10556267073002862865757195)
          ·
            refine ⟨15834400609504294298635793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10556267073002862865757195 15834400609504294298635793)
            ·
              refine ⟨11875800457128220723976845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15834400609504294298635793 11875800457128220723976845)
              ·
                refine ⟨4453425171423082771491317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11875800457128220723976845 4453425171423082771491317)
                ·
                  refine ⟨417508609820914009827311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4453425171423082771491317 417508609820914009827311)
                  ·
                    rfl

theorem cell23_7317856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 5].length) (baseStart_7317856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317856 prefixEnd_7317856 := by exact prefixLift 7317856
  have htrace : WordTrace (prefixWord ++ tailWord_7317856) baseStart_7317856 baseEnd_7317856 := by
    simpa [prefixWord, tailWord_7317856, baseEnd_7317856] using wordTrace_append hprefix tailTrace_7317856
  have hstable : (prefixWord ++ tailWord_7317856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317856).length < 2 ^ (prefixWord ++ tailWord_7317856).sum := by decide
  have hdescent : baseEnd_7317856 < baseStart_7317856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317889 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_7317889 : Nat := 118140960795 + 7317889 * 2 ^ 59
def prefixEnd_7317889 : Nat := 4983230072969 + 3 ^ 40 * 7317889 * 2
def baseEnd_7317889 : Nat := 3757594433249824459333147

theorem tailTrace_7317889 : CollatzResearch.WordTrace tailWord_7317889 prefixEnd_7317889 3757594433249824459333147 := by
  unfold tailWord_7317889
  simp only [CollatzResearch.WordTrace]
  refine ⟨266905338985545423784972721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177936892657030282523315147 266905338985545423784972721)
  ·
    refine ⟨200179004239159067838729541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266905338985545423784972721 200179004239159067838729541)
    ·
      refine ⟨37533563294842325219761789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200179004239159067838729541 37533563294842325219761789)
      ·
        refine ⟨14075086235565871957410671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37533563294842325219761789 14075086235565871957410671)
        ·
          refine ⟨21112629353348807936116007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14075086235565871957410671 21112629353348807936116007)
          ·
            refine ⟨31668944030023211904174011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21112629353348807936116007 31668944030023211904174011)
            ·
              refine ⟨47503416045034817856261017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31668944030023211904174011 47503416045034817856261017)
              ·
                refine ⟨35627562033776113392195763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47503416045034817856261017 35627562033776113392195763)
                ·
                  refine ⟨53441343050664170088293645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35627562033776113392195763 53441343050664170088293645)
                  ·
                    refine ⟨20040503643999063783110117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53441343050664170088293645 20040503643999063783110117)
                    ·
                      refine ⟨3757594433249824459333147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20040503643999063783110117 3757594433249824459333147)
                      ·
                        rfl

theorem cell23_7317889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_7317889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317889 prefixEnd_7317889 := by exact prefixLift 7317889
  have htrace : WordTrace (prefixWord ++ tailWord_7317889) baseStart_7317889 baseEnd_7317889 := by
    simpa [prefixWord, tailWord_7317889, baseEnd_7317889] using wordTrace_append hprefix tailTrace_7317889
  have hstable : (prefixWord ++ tailWord_7317889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317889).length < 2 ^ (prefixWord ++ tailWord_7317889).sum := by decide
  have hdescent : baseEnd_7317889 < baseStart_7317889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317899 : List Nat := [1, 1, 1, 1, 4, 4, 2, 2, 3, 4]
def baseStart_7317899 : Nat := 118140960795 + 7317899 * 2 ^ 59
def prefixEnd_7317899 : Nat := 4983230072969 + 3 ^ 40 * 7317899 * 2
def baseEnd_7317899 : Nat := 1252533189352123140069367

theorem tailTrace_7317899 : CollatzResearch.WordTrace tailWord_7317899 prefixEnd_7317899 1252533189352123140069367 := by
  unfold tailWord_7317899
  simp only [CollatzResearch.WordTrace]
  refine ⟨266905703715509195492836751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177937135810339463661891167 266905703715509195492836751)
  ·
    refine ⟨400358555573263793239255127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266905703715509195492836751 400358555573263793239255127)
    ·
      refine ⟨600537833359895689858882691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400358555573263793239255127 600537833359895689858882691)
      ·
        refine ⟨900806750039843534788324037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600537833359895689858882691 900806750039843534788324037)
        ·
          refine ⟨168901265632470662772810757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 900806750039843534788324037 168901265632470662772810757)
          ·
            refine ⟨31668987306088249269902017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168901265632470662772810757 31668987306088249269902017)
            ·
              refine ⟨23751740479566186952426513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31668987306088249269902017 23751740479566186952426513)
              ·
                refine ⟨17813805359674640214319885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23751740479566186952426513 17813805359674640214319885)
                ·
                  refine ⟨6680177009877990080369957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17813805359674640214319885 6680177009877990080369957)
                  ·
                    refine ⟨1252533189352123140069367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6680177009877990080369957 1252533189352123140069367)
                    ·
                      rfl

theorem cell23_7317899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 4].length) (baseStart_7317899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317899 prefixEnd_7317899 := by exact prefixLift 7317899
  have htrace : WordTrace (prefixWord ++ tailWord_7317899) baseStart_7317899 baseEnd_7317899 := by
    simpa [prefixWord, tailWord_7317899, baseEnd_7317899] using wordTrace_append hprefix tailTrace_7317899
  have hstable : (prefixWord ++ tailWord_7317899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317899).length < 2 ^ (prefixWord ++ tailWord_7317899).sum := by decide
  have hdescent : baseEnd_7317899 < baseStart_7317899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317909 : List Nat := [1, 3, 2, 1, 1, 2, 1, 5, 2, 2, 3]
def baseStart_7317909 : Nat := 118140960795 + 7317909 * 2 ^ 59
def prefixEnd_7317909 : Nat := 4983230072969 + 3 ^ 40 * 7317909 * 2
def baseEnd_7317909 : Nat := 3757604702862914381083055

theorem tailTrace_7317909 : CollatzResearch.WordTrace tailWord_7317909 prefixEnd_7317909 3757604702862914381083055 := by
  unfold tailWord_7317909
  simp only [CollatzResearch.WordTrace]
  refine ⟨266906068445472967200700781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177937378963648644800467187 266906068445472967200700781)
  ·
    refine ⟨100089775667052362700262793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266906068445472967200700781 100089775667052362700262793)
    ·
      refine ⟨75067331750289272025197095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100089775667052362700262793 75067331750289272025197095)
      ·
        refine ⟨112600997625433908037795643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75067331750289272025197095 112600997625433908037795643)
        ·
          refine ⟨168901496438150862056693465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112600997625433908037795643 168901496438150862056693465)
          ·
            refine ⟨126676122328613146542520099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168901496438150862056693465 126676122328613146542520099)
            ·
              refine ⟨190014183492919719813780149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126676122328613146542520099 190014183492919719813780149)
              ·
                refine ⟨17813829702461223732541889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190014183492919719813780149 17813829702461223732541889)
                ·
                  refine ⟨13360372276845917799406417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17813829702461223732541889 13360372276845917799406417)
                  ·
                    refine ⟨10020279207634438349554813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13360372276845917799406417 10020279207634438349554813)
                    ·
                      refine ⟨3757604702862914381083055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10020279207634438349554813 3757604702862914381083055)
                      ·
                        rfl

theorem cell23_7317909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_7317909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317909 prefixEnd_7317909 := by exact prefixLift 7317909
  have htrace : WordTrace (prefixWord ++ tailWord_7317909) baseStart_7317909 baseEnd_7317909 := by
    simpa [prefixWord, tailWord_7317909, baseEnd_7317909] using wordTrace_append hprefix tailTrace_7317909
  have hstable : (prefixWord ++ tailWord_7317909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317909).length < 2 ^ (prefixWord ++ tailWord_7317909).sum := by decide
  have hdescent : baseEnd_7317909 < baseStart_7317909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317959 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 3, 5]
def baseStart_7317959 : Nat := 118140960795 + 7317959 * 2 ^ 59
def prefixEnd_7317959 : Nat := 4983230072969 + 3 ^ 40 * 7317959 * 2
def baseEnd_7317959 : Nat := 1252543458965213061819275

theorem tailTrace_7317959 : CollatzResearch.WordTrace tailWord_7317959 prefixEnd_7317959 1252543458965213061819275 := by
  unfold tailWord_7317959
  simp only [CollatzResearch.WordTrace]
  refine ⟨266907892095291825740020931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177938594730194550493347287 266907892095291825740020931)
  ·
    refine ⟨400361838142937738610031397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266907892095291825740020931 400361838142937738610031397)
    ·
      refine ⟨75067844651800825989380887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 400361838142937738610031397 75067844651800825989380887)
      ·
        refine ⟨112601766977701238984071331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75067844651800825989380887 112601766977701238984071331)
        ·
          refine ⟨168902650466551858476106997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112601766977701238984071331 168902650466551858476106997)
          ·
            refine ⟨15834623481239236732135031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168902650466551858476106997 15834623481239236732135031)
            ·
              refine ⟨23751935221858855098202547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15834623481239236732135031 23751935221858855098202547)
              ·
                refine ⟨35627902832788282647303821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23751935221858855098202547 35627902832788282647303821)
                ·
                  refine ⟨13360463562295605992738933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35627902832788282647303821 13360463562295605992738933)
                  ·
                    refine ⟨1252543458965213061819275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13360463562295605992738933 1252543458965213061819275)
                    ·
                      rfl

theorem cell23_7317959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_7317959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317959 prefixEnd_7317959 := by exact prefixLift 7317959
  have htrace : WordTrace (prefixWord ++ tailWord_7317959) baseStart_7317959 baseEnd_7317959 := by
    simpa [prefixWord, tailWord_7317959, baseEnd_7317959] using wordTrace_append hprefix tailTrace_7317959
  have hstable : (prefixWord ++ tailWord_7317959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317959).length < 2 ^ (prefixWord ++ tailWord_7317959).sum := by decide
  have hdescent : baseEnd_7317959 < baseStart_7317959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318006 : List Nat := [5, 1, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_7318006 : Nat := 118140960795 + 7318006 * 2 ^ 59
def prefixEnd_7318006 : Nat := 4983230072969 + 3 ^ 40 * 7318006 * 2
def baseEnd_7318006 : Nat := 1252551503495466833856703

theorem tailTrace_7318006 : CollatzResearch.WordTrace tailWord_7318006 prefixEnd_7318006 1252551503495466833856703 := by
  unfold tailWord_7318006
  simp only [CollatzResearch.WordTrace]
  refine ⟨16681850395382597047936367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177939737550747701844654581 16681850395382597047936367)
  ·
    refine ⟨25022775593073895571904551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16681850395382597047936367 25022775593073895571904551)
    ·
      refine ⟨37534163389610843357856827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25022775593073895571904551 37534163389610843357856827)
      ·
        refine ⟨56301245084416265036785241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37534163389610843357856827 56301245084416265036785241)
        ·
          refine ⟨42225933813312198777588931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56301245084416265036785241 42225933813312198777588931)
          ·
            refine ⟨63338900719968298166383397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42225933813312198777588931 63338900719968298166383397)
            ·
              refine ⟨11876043884994055906196887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63338900719968298166383397 11876043884994055906196887)
              ·
                refine ⟨17814065827491083859295331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11876043884994055906196887 17814065827491083859295331)
                ·
                  refine ⟨26721098741236625788942997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17814065827491083859295331 26721098741236625788942997)
                  ·
                    refine ⟨1252551503495466833856703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26721098741236625788942997 1252551503495466833856703)
                    ·
                      rfl

theorem cell23_7318006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_7318006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318006 prefixEnd_7318006 := by exact prefixLift 7318006
  have htrace : WordTrace (prefixWord ++ tailWord_7318006) baseStart_7318006 baseEnd_7318006 := by
    simpa [prefixWord, tailWord_7318006, baseEnd_7318006] using wordTrace_append hprefix tailTrace_7318006
  have hstable : (prefixWord ++ tailWord_7318006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318006).length < 2 ^ (prefixWord ++ tailWord_7318006).sum := by decide
  have hdescent : baseEnd_7318006 < baseStart_7318006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318009 : List Nat := [1, 2, 1, 3, 1, 2, 3, 3, 1, 2, 4]
def baseStart_7318009 : Nat := 118140960795 + 7318009 * 2 ^ 59
def prefixEnd_7318009 : Nat := 4983230072969 + 3 ^ 40 * 7318009 * 2
def baseEnd_7318009 : Nat := 3757656050928363989832595

theorem tailTrace_7318009 : CollatzResearch.WordTrace tailWord_7318009 prefixEnd_7318009 3757656050928363989832595 := by
  unfold tailWord_7318009
  simp only [CollatzResearch.WordTrace]
  refine ⟨266909715745110684279341081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177939810496740456186227387 266909715745110684279341081)
  ·
    refine ⟨200182286808833013209505811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266909715745110684279341081 200182286808833013209505811)
    ·
      refine ⟨300273430213249519814258717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200182286808833013209505811 300273430213249519814258717)
      ·
        refine ⟨112602536329968569930347019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300273430213249519814258717 112602536329968569930347019)
        ·
          refine ⟨168903804494952854895520529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112602536329968569930347019 168903804494952854895520529)
          ·
            refine ⟨126677853371214641171640397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168903804494952854895520529 126677853371214641171640397)
            ·
              refine ⟨47504195014205490439365149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126677853371214641171640397 47504195014205490439365149)
              ·
                refine ⟨17814073130327058914761931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47504195014205490439365149 17814073130327058914761931)
                ·
                  refine ⟨26721109695490588372142897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17814073130327058914761931 26721109695490588372142897)
                  ·
                    refine ⟨20040832271617941279107173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26721109695490588372142897 20040832271617941279107173)
                    ·
                      refine ⟨3757656050928363989832595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20040832271617941279107173 3757656050928363989832595)
                      ·
                        rfl

theorem cell23_7318009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_7318009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318009 prefixEnd_7318009 := by exact prefixLift 7318009
  have htrace : WordTrace (prefixWord ++ tailWord_7318009) baseStart_7318009 baseEnd_7318009 := by
    simpa [prefixWord, tailWord_7318009, baseEnd_7318009] using wordTrace_append hprefix tailTrace_7318009
  have hstable : (prefixWord ++ tailWord_7318009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318009).length < 2 ^ (prefixWord ++ tailWord_7318009).sum := by decide
  have hdescent : baseEnd_7318009 < baseStart_7318009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318013 : List Nat := [1, 4, 1, 1, 1, 3, 3, 2, 3, 2, 2]
def baseStart_7318013 : Nat := 118140960795 + 7318013 * 2 ^ 59
def prefixEnd_7318013 : Nat := 4983230072969 + 3 ^ 40 * 7318013 * 2
def baseEnd_7318013 : Nat := 3757658104850981974182577

theorem tailTrace_7318013 : CollatzResearch.WordTrace tailWord_7318013 prefixEnd_7318013 3757658104850981974182577 := by
  unfold tailWord_7318013
  simp only [CollatzResearch.WordTrace]
  refine ⟨266909861637096192962486693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177939907758064128641657795 266909861637096192962486693)
  ·
    refine ⟨50045599056955536180466255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266909861637096192962486693 50045599056955536180466255)
    ·
      refine ⟨75068398585433304270699383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50045599056955536180466255 75068398585433304270699383)
      ·
        refine ⟨112602597878149956406049075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75068398585433304270699383 112602597878149956406049075)
        ·
          refine ⟨168903896817224934609073613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112602597878149956406049075 168903896817224934609073613)
          ·
            refine ⟨63338961306459350478402605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168903896817224934609073613 63338961306459350478402605)
            ·
              refine ⟨23752110489922256429400977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63338961306459350478402605 23752110489922256429400977)
              ·
                refine ⟨17814082867441692322050733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23752110489922256429400977 17814082867441692322050733)
                ·
                  refine ⟨6680281075290634620769025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17814082867441692322050733 6680281075290634620769025)
                  ·
                    refine ⟨5010210806467975965576769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6680281075290634620769025 5010210806467975965576769)
                    ·
                      refine ⟨3757658104850981974182577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5010210806467975965576769 3757658104850981974182577)
                      ·
                        rfl

theorem cell23_7318013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_7318013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318013 prefixEnd_7318013 := by exact prefixLift 7318013
  have htrace : WordTrace (prefixWord ++ tailWord_7318013) baseStart_7318013 baseEnd_7318013 := by
    simpa [prefixWord, tailWord_7318013, baseEnd_7318013] using wordTrace_append hprefix tailTrace_7318013
  have hstable : (prefixWord ++ tailWord_7318013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318013).length < 2 ^ (prefixWord ++ tailWord_7318013).sum := by decide
  have hdescent : baseEnd_7318013 < baseStart_7318013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318019 : List Nat := [1, 1, 1, 3, 2, 1, 7, 7]
def baseStart_7318019 : Nat := 118140960795 + 7318019 * 2 ^ 59
def prefixEnd_7318019 : Nat := 4983230072969 + 3 ^ 40 * 7318019 * 2
def baseEnd_7318019 : Nat := 139172636508700331507687

theorem tailTrace_7318019 : CollatzResearch.WordTrace tailWord_7318019 prefixEnd_7318019 139172636508700331507687 := by
  unfold tailWord_7318019
  simp only [CollatzResearch.WordTrace]
  refine ⟨266910080475074455987205111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177940053650049637324803407 266910080475074455987205111)
  ·
    refine ⟨400365120712611683980807667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266910080475074455987205111 400365120712611683980807667)
    ·
      refine ⟨600547681068917525971211501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400365120712611683980807667 600547681068917525971211501)
      ·
        refine ⟨225205380400844072239204313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 600547681068917525971211501 225205380400844072239204313)
        ·
          refine ⟨168904035300633054179403235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225205380400844072239204313 168904035300633054179403235)
          ·
            refine ⟨253356052950949581269104853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168904035300633054179403235 253356052950949581269104853)
            ·
              refine ⟨5938032491037880810994645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 253356052950949581269104853 5938032491037880810994645)
              ·
                refine ⟨139172636508700331507687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5938032491037880810994645 139172636508700331507687)
                ·
                  rfl

theorem cell23_7318019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 7].length) (baseStart_7318019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318019 prefixEnd_7318019 := by exact prefixLift 7318019
  have htrace : WordTrace (prefixWord ++ tailWord_7318019) baseStart_7318019 baseEnd_7318019 := by
    simpa [prefixWord, tailWord_7318019, baseEnd_7318019] using wordTrace_append hprefix tailTrace_7318019
  have hstable : (prefixWord ++ tailWord_7318019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318019).length < 2 ^ (prefixWord ++ tailWord_7318019).sum := by decide
  have hdescent : baseEnd_7318019 < baseStart_7318019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318030 : List Nat := [4, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4]
def baseStart_7318030 : Nat := 118140960795 + 7318030 * 2 ^ 59
def prefixEnd_7318030 : Nat := 4983230072969 + 3 ^ 40 * 7318030 * 2
def baseEnd_7318030 : Nat := 3757666834022108407669999

theorem tailTrace_7318030 : CollatzResearch.WordTrace tailWord_7318030 prefixEnd_7318030 3757666834022108407669999 := by
  unfold tailWord_7318030
  simp only [CollatzResearch.WordTrace]
  refine ⟨33363810209754325608231943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177940321118689736577237029 33363810209754325608231943)
  ·
    refine ⟨50045715314631488412347915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33363810209754325608231943 50045715314631488412347915)
    ·
      refine ⟨75068572971947232618521873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50045715314631488412347915 75068572971947232618521873)
      ·
        refine ⟨56301429728960424463891405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75068572971947232618521873 56301429728960424463891405)
        ·
          refine ⟨21113036148360159173959277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56301429728960424463891405 21113036148360159173959277)
          ·
            refine ⟨7917388555635059690234729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21113036148360159173959277 7917388555635059690234729)
            ·
              refine ⟨5938041416726294767676047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7917388555635059690234729 5938041416726294767676047)
              ·
                refine ⟨8907062125089442151514071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5938041416726294767676047 8907062125089442151514071)
                ·
                  refine ⟨13360593187634163227271107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8907062125089442151514071 13360593187634163227271107)
                  ·
                    refine ⟨20040889781451244840906661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13360593187634163227271107 20040889781451244840906661)
                    ·
                      refine ⟨3757666834022108407669999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20040889781451244840906661 3757666834022108407669999)
                      ·
                        rfl

theorem cell23_7318030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_7318030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318030 prefixEnd_7318030 := by exact prefixLift 7318030
  have htrace : WordTrace (prefixWord ++ tailWord_7318030) baseStart_7318030 baseEnd_7318030 := by
    simpa [prefixWord, tailWord_7318030, baseEnd_7318030] using wordTrace_append hprefix tailTrace_7318030
  have hstable : (prefixWord ++ tailWord_7318030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318030).length < 2 ^ (prefixWord ++ tailWord_7318030).sum := by decide
  have hdescent : baseEnd_7318030 < baseStart_7318030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318036 : List Nat := [2, 4, 3, 1, 1, 2, 10]
def baseStart_7318036 : Nat := 118140960795 + 7318036 * 2 ^ 59
def prefixEnd_7318036 : Nat := 4983230072969 + 3 ^ 40 * 7318036 * 2
def baseEnd_7318036 : Nat := 46390986603778214619691

theorem tailTrace_7318036 : CollatzResearch.WordTrace tailWord_7318036 prefixEnd_7318036 46390986603778214619691 := by
  unfold tailWord_7318036
  simp only [CollatzResearch.WordTrace]
  refine ⟨133455350258006433945286981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177940467010675245260382641 133455350258006433945286981)
  ·
    refine ⟨25022878173376206364741309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133455350258006433945286981 25022878173376206364741309)
    ·
      refine ⟨9383579315016077386777991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25022878173376206364741309 9383579315016077386777991)
      ·
        refine ⟨14075368972524116080166987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9383579315016077386777991 14075368972524116080166987)
        ·
          refine ⟨21113053458786174120250481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14075368972524116080166987 21113053458786174120250481)
          ·
            refine ⟨15834790094089630590187861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21113053458786174120250481 15834790094089630590187861)
            ·
              refine ⟨46390986603778214619691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15834790094089630590187861 46390986603778214619691)
              ·
                rfl

theorem cell23_7318036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 10].length) (baseStart_7318036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318036 prefixEnd_7318036 := by exact prefixLift 7318036
  have htrace : WordTrace (prefixWord ++ tailWord_7318036) baseStart_7318036 baseEnd_7318036 := by
    simpa [prefixWord, tailWord_7318036, baseEnd_7318036] using wordTrace_append hprefix tailTrace_7318036
  have hstable : (prefixWord ++ tailWord_7318036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318036).length < 2 ^ (prefixWord ++ tailWord_7318036).sum := by decide
  have hdescent : baseEnd_7318036 < baseStart_7318036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318089 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 3, 6, 3]
def baseStart_7318089 : Nat := 118140960795 + 7318089 * 2 ^ 59
def prefixEnd_7318089 : Nat := 4983230072969 + 3 ^ 40 * 7318089 * 2
def baseEnd_7318089 : Nat := 3757697129380723676832227

theorem tailTrace_7318089 : CollatzResearch.WordTrace tailWord_7318089 prefixEnd_7318089 3757697129380723676832227 := by
  unfold tailWord_7318089
  simp only [CollatzResearch.WordTrace]
  refine ⟨266912633584820857942253321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177941755723213905294835547 266912633584820857942253321)
  ·
    refine ⟨200184475188615643456689991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266912633584820857942253321 200184475188615643456689991)
    ·
      refine ⟨300276712782923465185034987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200184475188615643456689991 300276712782923465185034987)
      ·
        refine ⟨450415069174385197777552481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300276712782923465185034987 450415069174385197777552481)
        ·
          refine ⟨337811301880788898333164361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450415069174385197777552481 337811301880788898333164361)
          ·
            refine ⟨253358476410591673749873271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337811301880788898333164361 253358476410591673749873271)
            ·
              refine ⟨380037714615887510624809907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253358476410591673749873271 380037714615887510624809907)
              ·
                refine ⟨570056571923831265937214861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380037714615887510624809907 570056571923831265937214861)
                ·
                  refine ⟨213771214471436724726455573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570056571923831265937214861 213771214471436724726455573)
                  ·
                    refine ⟨10020525678348596471552605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 213771214471436724726455573 10020525678348596471552605)
                    ·
                      refine ⟨3757697129380723676832227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10020525678348596471552605 3757697129380723676832227)
                      ·
                        rfl

theorem cell23_7318089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 6, 3].length) (baseStart_7318089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318089 prefixEnd_7318089 := by exact prefixLift 7318089
  have htrace : WordTrace (prefixWord ++ tailWord_7318089) baseStart_7318089 baseEnd_7318089 := by
    simpa [prefixWord, tailWord_7318089, baseEnd_7318089] using wordTrace_append hprefix tailTrace_7318089
  have hstable : (prefixWord ++ tailWord_7318089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318089).length < 2 ^ (prefixWord ++ tailWord_7318089).sum := by decide
  have hdescent : baseEnd_7318089 < baseStart_7318089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318103 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 4, 2, 2]
def baseStart_7318103 : Nat := 118140960795 + 7318103 * 2 ^ 59
def prefixEnd_7318103 : Nat := 4983230072969 + 3 ^ 40 * 7318103 * 2
def baseEnd_7318103 : Nat := 3757704318109886622057163

theorem tailTrace_7318103 : CollatzResearch.WordTrace tailWord_7318103 prefixEnd_7318103 3757704318109886622057163 := by
  unfold tailWord_7318103
  simp only [CollatzResearch.WordTrace]
  refine ⟨266913144206770138333262963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177942096137846758888841975 266913144206770138333262963)
  ·
    refine ⟨400369716310155207499894445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266913144206770138333262963 400369716310155207499894445)
    ·
      refine ⟨150138643616308202812460417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400369716310155207499894445 150138643616308202812460417)
      ·
        refine ⟨112603982712231152109345313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150138643616308202812460417 112603982712231152109345313)
        ·
          refine ⟨84452987034173364082008985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112603982712231152109345313 84452987034173364082008985)
          ·
            refine ⟨63339740275630023061506739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84452987034173364082008985 63339740275630023061506739)
            ·
              refine ⟨95009610413445034592260109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63339740275630023061506739 95009610413445034592260109)
              ·
                refine ⟨35628603905041887972097541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95009610413445034592260109 35628603905041887972097541)
                ·
                  refine ⟨6680363232195353994768289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35628603905041887972097541 6680363232195353994768289)
                  ·
                    refine ⟨5010272424146515496076217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6680363232195353994768289 5010272424146515496076217)
                    ·
                      refine ⟨3757704318109886622057163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5010272424146515496076217 3757704318109886622057163)
                      ·
                        rfl

theorem cell23_7318103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_7318103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318103 prefixEnd_7318103 := by exact prefixLift 7318103
  have htrace : WordTrace (prefixWord ++ tailWord_7318103) baseStart_7318103 baseEnd_7318103 := by
    simpa [prefixWord, tailWord_7318103, baseEnd_7318103] using wordTrace_append hprefix tailTrace_7318103
  have hstable : (prefixWord ++ tailWord_7318103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318103).length < 2 ^ (prefixWord ++ tailWord_7318103).sum := by decide
  have hdescent : baseEnd_7318103 < baseStart_7318103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318170 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3]
def baseStart_7318170 : Nat := 118140960795 + 7318170 * 2 ^ 59
def prefixEnd_7318170 : Nat := 4983230072969 + 3 ^ 40 * 7318170 * 2
def baseEnd_7318170 : Nat := 3757738721313737859919355

theorem tailTrace_7318170 : CollatzResearch.WordTrace tailWord_7318170 prefixEnd_7318170 3757738721313737859919355 := by
  unfold tailWord_7318170
  simp only [CollatzResearch.WordTrace]
  refine ⟨66728896974381852193987991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177943725265018272517301309 66728896974381852193987991)
  ·
    refine ⟨100093345461572778290981987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66728896974381852193987991 100093345461572778290981987)
    ·
      refine ⟨150140018192359167436472981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100093345461572778290981987 150140018192359167436472981)
      ·
        refine ⟨7037813352766835973584671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 150140018192359167436472981 7037813352766835973584671)
        ·
          refine ⟨10556720029150253960377007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7037813352766835973584671 10556720029150253960377007)
          ·
            refine ⟨15835080043725380940565511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10556720029150253960377007 15835080043725380940565511)
            ·
              refine ⟨23752620065588071410848267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15835080043725380940565511 23752620065588071410848267)
              ·
                refine ⟨35628930098382107116272401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23752620065588071410848267 35628930098382107116272401)
                ·
                  refine ⟨26721697573786580337204301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35628930098382107116272401 26721697573786580337204301)
                  ·
                    refine ⟨10020636590169967626451613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26721697573786580337204301 10020636590169967626451613)
                    ·
                      refine ⟨3757738721313737859919355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10020636590169967626451613 3757738721313737859919355)
                      ·
                        rfl

theorem cell23_7318170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_7318170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318170 prefixEnd_7318170 := by exact prefixLift 7318170
  have htrace : WordTrace (prefixWord ++ tailWord_7318170) baseStart_7318170 baseEnd_7318170 := by
    simpa [prefixWord, tailWord_7318170, baseEnd_7318170] using wordTrace_append hprefix tailTrace_7318170
  have hstable : (prefixWord ++ tailWord_7318170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318170).length < 2 ^ (prefixWord ++ tailWord_7318170).sum := by decide
  have hdescent : baseEnd_7318170 < baseStart_7318170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318190 : List Nat := [4, 1, 4, 1, 1, 1, 3, 1, 2, 5]
def baseStart_7318190 : Nat := 118140960795 + 7318190 * 2 ^ 59
def prefixEnd_7318190 : Nat := 4983230072969 + 3 ^ 40 * 7318190 * 2
def baseEnd_7318190 : Nat := 1252582996975609260556421

theorem tailTrace_7318190 : CollatzResearch.WordTrace tailWord_7318190 prefixEnd_7318190 1252582996975609260556421 := by
  unfold tailWord_7318190
  simp only [CollatzResearch.WordTrace]
  refine ⟨33364539669681869023960003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177944211571636634794453349 33364539669681869023960003)
  ·
    refine ⟨50046809504522803535940005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33364539669681869023960003 50046809504522803535940005)
    ·
      refine ⟨9383776782098025662988751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50046809504522803535940005 9383776782098025662988751)
      ·
        refine ⟨14075665173147038494483127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9383776782098025662988751 14075665173147038494483127)
        ·
          refine ⟨21113497759720557741724691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14075665173147038494483127 21113497759720557741724691)
          ·
            refine ⟨31670246639580836612587037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21113497759720557741724691 31670246639580836612587037)
            ·
              refine ⟨11876342489842813729720139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31670246639580836612587037 11876342489842813729720139)
              ·
                refine ⟨17814513734764220594580209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11876342489842813729720139 17814513734764220594580209)
                ·
                  refine ⟨13360885301073165445935157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17814513734764220594580209 13360885301073165445935157)
                  ·
                    refine ⟨1252582996975609260556421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13360885301073165445935157 1252582996975609260556421)
                    ·
                      rfl

theorem cell23_7318190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_7318190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318190 prefixEnd_7318190 := by exact prefixLift 7318190
  have htrace : WordTrace (prefixWord ++ tailWord_7318190) baseStart_7318190 baseEnd_7318190 := by
    simpa [prefixWord, tailWord_7318190, baseEnd_7318190] using wordTrace_append hprefix tailTrace_7318190
  have hstable : (prefixWord ++ tailWord_7318190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318190).length < 2 ^ (prefixWord ++ tailWord_7318190).sum := by decide
  have hdescent : baseEnd_7318190 < baseStart_7318190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318206 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_7318206 : Nat := 118140960795 + 7318206 * 2 ^ 59
def prefixEnd_7318206 : Nat := 4983230072969 + 3 ^ 40 * 7318206 * 2
def baseEnd_7318206 : Nat := 3757757206617299719069189

theorem tailTrace_7318206 : CollatzResearch.WordTrace tailWord_7318206 prefixEnd_7318206 3757757206617299719069189 := by
  unfold tailWord_7318206
  simp only [CollatzResearch.WordTrace]
  refine ⟨33364612615674623365532809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177944600616931324616174981 33364612615674623365532809)
  ·
    refine ⟨25023459461755967524149607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33364612615674623365532809 25023459461755967524149607)
    ·
      refine ⟨37535189192633951286224411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25023459461755967524149607 37535189192633951286224411)
      ·
        refine ⟨56302783788950926929336617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37535189192633951286224411 56302783788950926929336617)
        ·
          refine ⟨42227087841713195197002463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56302783788950926929336617 42227087841713195197002463)
          ·
            refine ⟨63340631762569792795503695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42227087841713195197002463 63340631762569792795503695)
            ·
              refine ⟨95010947643854689193255543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63340631762569792795503695 95010947643854689193255543)
              ·
                refine ⟨142516421465782033789883315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95010947643854689193255543 142516421465782033789883315)
                ·
                  refine ⟨213774632198673050684824973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142516421465782033789883315 213774632198673050684824973)
                  ·
                    refine ⟨80165487074502394006809365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213774632198673050684824973 80165487074502394006809365)
                    ·
                      refine ⟨3757757206617299719069189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80165487074502394006809365 3757757206617299719069189)
                      ·
                        rfl

theorem cell23_7318206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_7318206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318206 prefixEnd_7318206 := by exact prefixLift 7318206
  have htrace : WordTrace (prefixWord ++ tailWord_7318206) baseStart_7318206 baseEnd_7318206 := by
    simpa [prefixWord, tailWord_7318206, baseEnd_7318206] using wordTrace_append hprefix tailTrace_7318206
  have hstable : (prefixWord ++ tailWord_7318206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318206).length < 2 ^ (prefixWord ++ tailWord_7318206).sum := by decide
  have hdescent : baseEnd_7318206 < baseStart_7318206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318216 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 8]
def baseStart_7318216 : Nat := 118140960795 + 7318216 * 2 ^ 59
def prefixEnd_7318216 : Nat := 4983230072969 + 3 ^ 40 * 7318216 * 2
def baseEnd_7318216 : Nat := 417529149047093853327127

theorem tailTrace_7318216 : CollatzResearch.WordTrace tailWord_7318216 prefixEnd_7318216 417529149047093853327127 := by
  unfold tailWord_7318216
  simp only [CollatzResearch.WordTrace]
  refine ⟨133458632827680379316063251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177944843770240505754751001 133458632827680379316063251)
  ·
    refine ⟨200187949241520568974094877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133458632827680379316063251 200187949241520568974094877)
    ·
      refine ⟨75070480965570213365285579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200187949241520568974094877 75070480965570213365285579)
      ·
        refine ⟨112605721448355320047928369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75070480965570213365285579 112605721448355320047928369)
        ·
          refine ⟨84454291086266490035946277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112605721448355320047928369 84454291086266490035946277)
          ·
            refine ⟨15835179578674966881739927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84454291086266490035946277 15835179578674966881739927)
            ·
              refine ⟨23752769368012450322609891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15835179578674966881739927 23752769368012450322609891)
              ·
                refine ⟨35629154052018675483914837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23752769368012450322609891 35629154052018675483914837)
                ·
                  refine ⟨417529149047093853327127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35629154052018675483914837 417529149047093853327127)
                  ·
                    rfl

theorem cell23_7318216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 8].length) (baseStart_7318216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318216 prefixEnd_7318216 := by exact prefixLift 7318216
  have htrace : WordTrace (prefixWord ++ tailWord_7318216) baseStart_7318216 baseEnd_7318216 := by
    simpa [prefixWord, tailWord_7318216, baseEnd_7318216] using wordTrace_append hprefix tailTrace_7318216
  have hstable : (prefixWord ++ tailWord_7318216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318216).length < 2 ^ (prefixWord ++ tailWord_7318216).sum := by decide
  have hdescent : baseEnd_7318216 < baseStart_7318216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318220 : List Nat := [2, 2, 1, 5, 1, 2, 2, 1, 3, 4]
def baseStart_7318220 : Nat := 118140960795 + 7318220 * 2 ^ 59
def prefixEnd_7318220 : Nat := 4983230072969 + 3 ^ 40 * 7318220 * 2
def baseEnd_7318220 : Nat := 1252588131782154221431375

theorem tailTrace_7318220 : CollatzResearch.WordTrace tailWord_7318220 prefixEnd_7318220 1252588131782154221431375 := by
  unfold tailWord_7318220
  simp only [CollatzResearch.WordTrace]
  refine ⟨133458705773673133657636057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177944941031564178210181409 133458705773673133657636057)
  ·
    refine ⟨100094029330254850243227043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133458705773673133657636057 100094029330254850243227043)
    ·
      refine ⟨150141043995382275364840565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100094029330254850243227043 150141043995382275364840565)
      ·
        refine ⟨14075722874567088315453803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150141043995382275364840565 14075722874567088315453803)
        ·
          refine ⟨21113584311850632473180705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14075722874567088315453803 21113584311850632473180705)
          ·
            refine ⟨15835188233887974354885529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21113584311850632473180705 15835188233887974354885529)
            ·
              refine ⟨11876391175415980766164147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15835188233887974354885529 11876391175415980766164147)
              ·
                refine ⟨17814586763123971149246221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11876391175415980766164147 17814586763123971149246221)
                ·
                  refine ⟨6680470036171489180967333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17814586763123971149246221 6680470036171489180967333)
                  ·
                    refine ⟨1252588131782154221431375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6680470036171489180967333 1252588131782154221431375)
                    ·
                      rfl

theorem cell23_7318220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_7318220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318220 prefixEnd_7318220 := by exact prefixLift 7318220
  have htrace : WordTrace (prefixWord ++ tailWord_7318220) baseStart_7318220 baseEnd_7318220 := by
    simpa [prefixWord, tailWord_7318220, baseEnd_7318220] using wordTrace_append hprefix tailTrace_7318220
  have hstable : (prefixWord ++ tailWord_7318220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318220).length < 2 ^ (prefixWord ++ tailWord_7318220).sum := by decide
  have hdescent : baseEnd_7318220 < baseStart_7318220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318233 : List Nat := [1, 2, 1, 2, 3, 2, 5, 1, 6]
def baseStart_7318233 : Nat := 118140960795 + 7318233 * 2 ^ 59
def prefixEnd_7318233 : Nat := 4983230072969 + 3 ^ 40 * 7318233 * 2
def baseEnd_7318233 : Nat := 417530118954996790381285

theorem tailTrace_7318233 : CollatzResearch.WordTrace tailWord_7318233 prefixEnd_7318233 417530118954996790381285 := by
  unfold tailWord_7318233
  simp only [CollatzResearch.WordTrace]
  refine ⟨266917885696299170535495353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177945257130866113690330235 266917885696299170535495353)
  ·
    refine ⟨200188414272224377901621515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266917885696299170535495353 200188414272224377901621515)
    ·
      refine ⟨300282621408336566852432273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200188414272224377901621515 300282621408336566852432273)
      ·
        refine ⟨225211966056252425139324205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300282621408336566852432273 225211966056252425139324205)
        ·
          refine ⟨84454487271094659427246577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225211966056252425139324205 84454487271094659427246577)
          ·
            refine ⟨63340865453320994570434933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84454487271094659427246577 63340865453320994570434933)
            ·
              refine ⟨5938206136248843240978275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63340865453320994570434933 5938206136248843240978275)
              ·
                refine ⟨8907309204373264861467413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5938206136248843240978275 8907309204373264861467413)
                ·
                  refine ⟨417530118954996790381285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8907309204373264861467413 417530118954996790381285)
                  ·
                    rfl

theorem cell23_7318233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 6].length) (baseStart_7318233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318233 prefixEnd_7318233 := by exact prefixLift 7318233
  have htrace : WordTrace (prefixWord ++ tailWord_7318233) baseStart_7318233 baseEnd_7318233 := by
    simpa [prefixWord, tailWord_7318233, baseEnd_7318233] using wordTrace_append hprefix tailTrace_7318233
  have hstable : (prefixWord ++ tailWord_7318233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318233).length < 2 ^ (prefixWord ++ tailWord_7318233).sum := by decide
  have hdescent : baseEnd_7318233 < baseStart_7318233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318300 : List Nat := [2, 2, 3, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_7318300 : Nat := 118140960795 + 7318300 * 2 ^ 59
def prefixEnd_7318300 : Nat := 4983230072969 + 3 ^ 40 * 7318300 * 2
def baseEnd_7318300 : Nat := 3757805473798822351293757

theorem tailTrace_7318300 : CollatzResearch.WordTrace tailWord_7318300 prefixEnd_7318300 3757805473798822351293757 := by
  unfold tailWord_7318300
  simp only [CollatzResearch.WordTrace]
  refine ⟨133460164693528220489092177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177946886258037627318789569 133460164693528220489092177)
  ·
    refine ⟨100095123520146165366819133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133460164693528220489092177 100095123520146165366819133)
    ·
      refine ⟨37535671320054812012557175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100095123520146165366819133 37535671320054812012557175)
      ·
        refine ⟨56303506980082218018835763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37535671320054812012557175 56303506980082218018835763)
        ·
          refine ⟨84455260470123327028253645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56303506980082218018835763 84455260470123327028253645)
          ·
            refine ⟨31670722676296247635595117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84455260470123327028253645 31670722676296247635595117)
            ·
              refine ⟨11876521003611092863348169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31670722676296247635595117 11876521003611092863348169)
              ·
                refine ⟨8907390752708319647511127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11876521003611092863348169 8907390752708319647511127)
                ·
                  refine ⟨13361086129062479471266691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8907390752708319647511127 13361086129062479471266691)
                  ·
                    refine ⟨20041629193593719206900037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13361086129062479471266691 20041629193593719206900037)
                    ·
                      refine ⟨3757805473798822351293757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20041629193593719206900037 3757805473798822351293757)
                      ·
                        rfl

theorem cell23_7318300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_7318300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318300 prefixEnd_7318300 := by exact prefixLift 7318300
  have htrace : WordTrace (prefixWord ++ tailWord_7318300) baseStart_7318300 baseEnd_7318300 := by
    simpa [prefixWord, tailWord_7318300, baseEnd_7318300] using wordTrace_append hprefix tailTrace_7318300
  have hstable : (prefixWord ++ tailWord_7318300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318300).length < 2 ^ (prefixWord ++ tailWord_7318300).sum := by decide
  have hdescent : baseEnd_7318300 < baseStart_7318300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318314 : List Nat := [3, 1, 4, 3, 1, 1, 3, 1, 1, 5]
def baseStart_7318314 : Nat := 118140960795 + 7318314 * 2 ^ 59
def prefixEnd_7318314 : Nat := 4983230072969 + 3 ^ 40 * 7318314 * 2
def baseEnd_7318314 : Nat := 1252604220842661765506231

theorem tailTrace_7318314 : CollatzResearch.WordTrace tailWord_7318314 prefixEnd_7318314 1252604220842661765506231 := by
  unfold tailWord_7318314
  simp only [CollatzResearch.WordTrace]
  refine ⟨66730210002251430342298499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177947226672670480912795997 66730210002251430342298499)
  ·
    refine ⟨100095315003377145513447749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66730210002251430342298499 100095315003377145513447749)
    ·
      refine ⟨18767871563133214783771453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100095315003377145513447749 18767871563133214783771453)
      ·
        refine ⟨7037951836174955543914295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18767871563133214783771453 7037951836174955543914295)
        ·
          refine ⟨10556927754262433315871443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7037951836174955543914295 10556927754262433315871443)
          ·
            refine ⟨15835391631393649973807165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10556927754262433315871443 15835391631393649973807165)
            ·
              refine ⟨5938271861772618740177687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15835391631393649973807165 5938271861772618740177687)
              ·
                refine ⟨8907407792658928110266531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5938271861772618740177687 8907407792658928110266531)
                ·
                  refine ⟨13361111688988392165399797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8907407792658928110266531 13361111688988392165399797)
                  ·
                    refine ⟨1252604220842661765506231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13361111688988392165399797 1252604220842661765506231)
                    ·
                      rfl

theorem cell23_7318314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_7318314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318314 prefixEnd_7318314 := by exact prefixLift 7318314
  have htrace : WordTrace (prefixWord ++ tailWord_7318314) baseStart_7318314 baseEnd_7318314 := by
    simpa [prefixWord, tailWord_7318314, baseEnd_7318314] using wordTrace_append hprefix tailTrace_7318314
  have hstable : (prefixWord ++ tailWord_7318314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318314).length < 2 ^ (prefixWord ++ tailWord_7318314).sum := by decide
  have hdescent : baseEnd_7318314 < baseStart_7318314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318403 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 4]
def baseStart_7318403 : Nat := 118140960795 + 7318403 * 2 ^ 59
def prefixEnd_7318403 : Nat := 4983230072969 + 3 ^ 40 * 7318403 * 2
def baseEnd_7318403 : Nat := 3757858362306235448305783

theorem tailTrace_7318403 : CollatzResearch.WordTrace tailWord_7318403 prefixEnd_7318403 3757858362306235448305783 := by
  unfold tailWord_7318403
  simp only [CollatzResearch.WordTrace]
  refine ⟨266924086105683289569183863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177949390737122193046122575 266924086105683289569183863)
  ·
    refine ⟨400386129158524934353775795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266924086105683289569183863 400386129158524934353775795)
    ·
      refine ⟨600579193737787401530663693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400386129158524934353775795 600579193737787401530663693)
      ·
        refine ⟨225217197651670275573998885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 600579193737787401530663693 225217197651670275573998885)
        ·
          refine ⟨42228224559688176670124791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225217197651670275573998885 42228224559688176670124791)
          ·
            refine ⟨63342336839532265005187187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42228224559688176670124791 63342336839532265005187187)
            ·
              refine ⟨95013505259298397507780781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63342336839532265005187187 95013505259298397507780781)
              ·
                refine ⟨35630064472236899065417793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95013505259298397507780781 35630064472236899065417793)
                ·
                  refine ⟨26722548354177674299063345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35630064472236899065417793 26722548354177674299063345)
                  ·
                    refine ⟨20041911265633255724297509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26722548354177674299063345 20041911265633255724297509)
                    ·
                      refine ⟨3757858362306235448305783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20041911265633255724297509 3757858362306235448305783)
                      ·
                        rfl

theorem cell23_7318403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_7318403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318403 prefixEnd_7318403 := by exact prefixLift 7318403
  have htrace : WordTrace (prefixWord ++ tailWord_7318403) baseStart_7318403 baseEnd_7318403 := by
    simpa [prefixWord, tailWord_7318403, baseEnd_7318403] using wordTrace_append hprefix tailTrace_7318403
  have hstable : (prefixWord ++ tailWord_7318403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318403).length < 2 ^ (prefixWord ++ tailWord_7318403).sum := by decide
  have hdescent : baseEnd_7318403 < baseStart_7318403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318407 : List Nat := [1, 1, 4, 2, 3, 1, 3, 1, 1, 4, 2]
def baseStart_7318407 : Nat := 118140960795 + 7318407 * 2 ^ 59
def prefixEnd_7318407 : Nat := 4983230072969 + 3 ^ 40 * 7318407 * 2
def baseEnd_7318407 : Nat := 3757860416228853432655765

theorem tailTrace_7318407 : CollatzResearch.WordTrace tailWord_7318407 prefixEnd_7318407 3757860416228853432655765 := by
  unfold tailWord_7318407
  simp only [CollatzResearch.WordTrace]
  refine ⟨266924231997668798252329475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177949487998445865501552983 266924231997668798252329475)
  ·
    refine ⟨400386347996503197378494213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266924231997668798252329475 400386347996503197378494213)
    ·
      refine ⟨75072440249344349508467665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 400386347996503197378494213 75072440249344349508467665)
      ·
        refine ⟨56304330187008262131350749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75072440249344349508467665 56304330187008262131350749)
        ·
          refine ⟨21114123820128098299256531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56304330187008262131350749 21114123820128098299256531)
          ·
            refine ⟨31671185730192147448884797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21114123820128098299256531 31671185730192147448884797)
            ·
              refine ⟨11876694648822055293331799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31671185730192147448884797 11876694648822055293331799)
              ·
                refine ⟨17815041973233082939997699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11876694648822055293331799 17815041973233082939997699)
                ·
                  refine ⟨26722562959849624409996549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17815041973233082939997699 26722562959849624409996549)
                  ·
                    refine ⟨5010480554971804576874353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26722562959849624409996549 5010480554971804576874353)
                    ·
                      refine ⟨3757860416228853432655765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5010480554971804576874353 3757860416228853432655765)
                      ·
                        rfl

theorem cell23_7318407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_7318407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318407 prefixEnd_7318407 := by exact prefixLift 7318407
  have htrace : WordTrace (prefixWord ++ tailWord_7318407) baseStart_7318407 baseEnd_7318407 := by
    simpa [prefixWord, tailWord_7318407, baseEnd_7318407] using wordTrace_append hprefix tailTrace_7318407
  have hstable : (prefixWord ++ tailWord_7318407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318407).length < 2 ^ (prefixWord ++ tailWord_7318407).sum := by decide
  have hdescent : baseEnd_7318407 < baseStart_7318407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318443 : List Nat := [1, 1, 1, 1, 2, 1, 1, 8, 2, 5]
def baseStart_7318443 : Nat := 118140960795 + 7318443 * 2 ^ 59
def prefixEnd_7318443 : Nat := 4983230072969 + 3 ^ 40 * 7318443 * 2
def baseEnd_7318443 : Nat := 1252626300510805097268533

theorem tailTrace_7318443 : CollatzResearch.WordTrace tailWord_7318443 prefixEnd_7318443 1252626300510805097268533 := by
  unfold tailWord_7318443
  simp only [CollatzResearch.WordTrace]
  refine ⟨266925545025538376400639983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177950363350358917600426655 266925545025538376400639983)
  ·
    refine ⟨400388317538307564600959975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266925545025538376400639983 400388317538307564600959975)
    ·
      refine ⟨600582476307461346901439963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400388317538307564600959975 600582476307461346901439963)
      ·
        refine ⟨900873714461192020352159945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600582476307461346901439963 900873714461192020352159945)
        ·
          refine ⟨675655285845894015264119959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 900873714461192020352159945 675655285845894015264119959)
          ·
            refine ⟨1013482928768841022896179939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675655285845894015264119959 1013482928768841022896179939)
            ·
              refine ⟨1520224393153261534344269909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013482928768841022896179939 1520224393153261534344269909)
              ·
                refine ⟨17815129607264783605596913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1520224393153261534344269909 17815129607264783605596913)
                ·
                  refine ⟨13361347205448587704197685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17815129607264783605596913 13361347205448587704197685)
                  ·
                    refine ⟨1252626300510805097268533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13361347205448587704197685 1252626300510805097268533)
                    ·
                      rfl

theorem cell23_7318443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 5].length) (baseStart_7318443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318443 prefixEnd_7318443 := by exact prefixLift 7318443
  have htrace : WordTrace (prefixWord ++ tailWord_7318443) baseStart_7318443 baseEnd_7318443 := by
    simpa [prefixWord, tailWord_7318443, baseEnd_7318443] using wordTrace_append hprefix tailTrace_7318443
  have hstable : (prefixWord ++ tailWord_7318443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318443).length < 2 ^ (prefixWord ++ tailWord_7318443).sum := by decide
  have hdescent : baseEnd_7318443 < baseStart_7318443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318463 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 4]
def baseStart_7318463 : Nat := 118140960795 + 7318463 * 2 ^ 59
def prefixEnd_7318463 : Nat := 4983230072969 + 3 ^ 40 * 7318463 * 2
def baseEnd_7318463 : Nat := 3757889171145505213555507

theorem tailTrace_7318463 : CollatzResearch.WordTrace tailWord_7318463 prefixEnd_7318463 3757889171145505213555507 := by
  unfold tailWord_7318463
  simp only [CollatzResearch.WordTrace]
  refine ⟨266926274485465919816368043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177950849656977279877578695 266926274485465919816368043)
  ·
    refine ⟨400389411728198879724552065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266926274485465919816368043 400389411728198879724552065)
    ·
      refine ⟨300292058796149159793414049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400389411728198879724552065 300292058796149159793414049)
      ·
        refine ⟨225219044097111869845060537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300292058796149159793414049 225219044097111869845060537)
        ·
          refine ⟨168914283072833902383795403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225219044097111869845060537 168914283072833902383795403)
          ·
            refine ⟨253371424609250853575693105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168914283072833902383795403 253371424609250853575693105)
            ·
              refine ⟨190028568456938140181769829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253371424609250853575693105 190028568456938140181769829)
              ·
                refine ⟨35630356585675901284081843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190028568456938140181769829 35630356585675901284081843)
                ·
                  refine ⟨53445534878513851926122765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35630356585675901284081843 53445534878513851926122765)
                  ·
                    refine ⟨20042075579442694472296037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53445534878513851926122765 20042075579442694472296037)
                    ·
                      refine ⟨3757889171145505213555507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20042075579442694472296037 3757889171145505213555507)
                      ·
                        rfl

theorem cell23_7318463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_7318463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318463 prefixEnd_7318463 := by exact prefixLift 7318463
  have htrace : WordTrace (prefixWord ++ tailWord_7318463) baseStart_7318463 baseEnd_7318463 := by
    simpa [prefixWord, tailWord_7318463, baseEnd_7318463] using wordTrace_append hprefix tailTrace_7318463
  have hstable : (prefixWord ++ tailWord_7318463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318463).length < 2 ^ (prefixWord ++ tailWord_7318463).sum := by decide
  have hdescent : baseEnd_7318463 < baseStart_7318463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318480 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 4, 4, 2]
def baseStart_7318480 : Nat := 118140960795 + 7318480 * 2 ^ 59
def prefixEnd_7318480 : Nat := 4983230072969 + 3 ^ 40 * 7318480 * 2
def baseEnd_7318480 : Nat := 3757897900316631647042929

theorem tailTrace_7318480 : CollatzResearch.WordTrace tailWord_7318480 prefixEnd_7318480 3757897900316631647042929 := by
  unfold tailWord_7318480
  simp only [CollatzResearch.WordTrace]
  refine ⟨133463447263202165859868447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177951263017602887813157929 133463447263202165859868447)
  ·
    refine ⟨200195170894803248789802671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133463447263202165859868447 200195170894803248789802671)
    ·
      refine ⟨300292756342204873184704007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200195170894803248789802671 300292756342204873184704007)
      ·
        refine ⟨450439134513307309777056011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300292756342204873184704007 450439134513307309777056011)
        ·
          refine ⟨675658701769960964665584017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450439134513307309777056011 675658701769960964665584017)
          ·
            refine ⟨506744026327470723499188013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 675658701769960964665584017 506744026327470723499188013)
            ·
              refine ⟨190029009872801521312195505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506744026327470723499188013 190029009872801521312195505)
              ·
                refine ⟨142521757404601140984146629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190029009872801521312195505 142521757404601140984146629)
                ·
                  refine ⟨26722829513362713934527493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142521757404601140984146629 26722829513362713934527493)
                  ·
                    refine ⟨5010530533755508862723905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26722829513362713934527493 5010530533755508862723905)
                    ·
                      refine ⟨3757897900316631647042929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5010530533755508862723905 3757897900316631647042929)
                      ·
                        rfl

theorem cell23_7318480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 4, 4, 2].length) (baseStart_7318480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318480 prefixEnd_7318480 := by exact prefixLift 7318480
  have htrace : WordTrace (prefixWord ++ tailWord_7318480) baseStart_7318480 baseEnd_7318480 := by
    simpa [prefixWord, tailWord_7318480, baseEnd_7318480] using wordTrace_append hprefix tailTrace_7318480
  have hstable : (prefixWord ++ tailWord_7318480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318480).length < 2 ^ (prefixWord ++ tailWord_7318480).sum := by decide
  have hdescent : baseEnd_7318480 < baseStart_7318480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318500 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 4, 2, 3]
def baseStart_7318500 : Nat := 118140960795 + 7318500 * 2 ^ 59
def prefixEnd_7318500 : Nat := 4983230072969 + 3 ^ 40 * 7318500 * 2
def baseEnd_7318500 : Nat := 3757908169929721568792837

theorem tailTrace_7318500 : CollatzResearch.WordTrace tailWord_7318500 prefixEnd_7318500 3757908169929721568792837 := by
  unfold tailWord_7318500
  simp only [CollatzResearch.WordTrace]
  refine ⟨133463811993165937567732477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177951749324221250090309969 133463811993165937567732477)
  ·
    refine ⟨50048929497437226587899679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133463811993165937567732477 50048929497437226587899679)
    ·
      refine ⟨75073394246155839881849519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50048929497437226587899679 75073394246155839881849519)
      ·
        refine ⟨112610091369233759822774279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75073394246155839881849519 112610091369233759822774279)
        ·
          refine ⟨168915137053850639734161419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112610091369233759822774279 168915137053850639734161419)
          ·
            refine ⟨253372705580775959601242129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168915137053850639734161419 253372705580775959601242129)
            ·
              refine ⟨190029529185581969700931597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253372705580775959601242129 190029529185581969700931597)
              ·
                refine ⟨71261073444593238637849349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190029529185581969700931597 71261073444593238637849349)
                ·
                  refine ⟨13361451270861232244596753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71261073444593238637849349 13361451270861232244596753)
                  ·
                    refine ⟨10021088453145924183447565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13361451270861232244596753 10021088453145924183447565)
                    ·
                      refine ⟨3757908169929721568792837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10021088453145924183447565 3757908169929721568792837)
                      ·
                        rfl

theorem cell23_7318500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_7318500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318500 prefixEnd_7318500 := by exact prefixLift 7318500
  have htrace : WordTrace (prefixWord ++ tailWord_7318500) baseStart_7318500 baseEnd_7318500 := by
    simpa [prefixWord, tailWord_7318500, baseEnd_7318500] using wordTrace_append hprefix tailTrace_7318500
  have hstable : (prefixWord ++ tailWord_7318500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318500).length < 2 ^ (prefixWord ++ tailWord_7318500).sum := by decide
  have hdescent : baseEnd_7318500 < baseStart_7318500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318564 : List Nat := [2, 3, 1, 4, 1, 1, 1, 3, 3, 1, 3]
def baseStart_7318564 : Nat := 118140960795 + 7318564 * 2 ^ 59
def prefixEnd_7318564 : Nat := 4983230072969 + 3 ^ 40 * 7318564 * 2
def baseEnd_7318564 : Nat := 3757941032691609318392543

theorem tailTrace_7318564 : CollatzResearch.WordTrace tailWord_7318564 prefixEnd_7318564 3757941032691609318392543 := by
  unfold tailWord_7318564
  simp only [CollatzResearch.WordTrace]
  refine ⟨133464979129050007032897373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177953305505400009377196497 133464979129050007032897373)
  ·
    refine ⟨50049367173393752637336515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133464979129050007032897373 50049367173393752637336515)
    ·
      refine ⟨75074050760090628956004773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50049367173393752637336515 75074050760090628956004773)
      ·
        refine ⟨14076384517516992929250895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75074050760090628956004773 14076384517516992929250895)
        ·
          refine ⟨21114576776275489393876343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14076384517516992929250895 21114576776275489393876343)
          ·
            refine ⟨31671865164413234090814515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21114576776275489393876343 31671865164413234090814515)
            ·
              refine ⟨47507797746619851136221773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31671865164413234090814515 47507797746619851136221773)
              ·
                refine ⟨17815424154982444176083165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47507797746619851136221773 17815424154982444176083165)
                ·
                  refine ⟨6680784058118416566031187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17815424154982444176083165 6680784058118416566031187)
                  ·
                    refine ⟨10021176087177624849046781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6680784058118416566031187 10021176087177624849046781)
                    ·
                      refine ⟨3757941032691609318392543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10021176087177624849046781 3757941032691609318392543)
                      ·
                        rfl

theorem cell23_7318564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_7318564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318564 prefixEnd_7318564 := by exact prefixLift 7318564
  have htrace : WordTrace (prefixWord ++ tailWord_7318564) baseStart_7318564 baseEnd_7318564 := by
    simpa [prefixWord, tailWord_7318564, baseEnd_7318564] using wordTrace_append hprefix tailTrace_7318564
  have hstable : (prefixWord ++ tailWord_7318564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318564).length < 2 ^ (prefixWord ++ tailWord_7318564).sum := by decide
  have hdescent : baseEnd_7318564 < baseStart_7318564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318600 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_7318600 : Nat := 118140960795 + 7318600 * 2 ^ 59
def prefixEnd_7318600 : Nat := 4983230072969 + 3 ^ 40 * 7318600 * 2
def baseEnd_7318600 : Nat := 3757959517995171177542377

theorem tailTrace_7318600 : CollatzResearch.WordTrace tailWord_7318600 prefixEnd_7318600 3757959517995171177542377 := by
  unfold tailWord_7318600
  simp only [CollatzResearch.WordTrace]
  refine ⟨133465635642984796107052627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177954180857313061476070169 133465635642984796107052627)
  ·
    refine ⟨200198453464477194160578941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133465635642984796107052627 200198453464477194160578941)
    ·
      refine ⟨75074420049178947810217103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200198453464477194160578941 75074420049178947810217103)
      ·
        refine ⟨112611630073768421715325655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75074420049178947810217103 112611630073768421715325655)
        ·
          refine ⟨168917445110652632572988483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112611630073768421715325655 168917445110652632572988483)
          ·
            refine ⟨253376167665978948859482725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168917445110652632572988483 253376167665978948859482725)
            ·
              refine ⟨47508031437371052911153011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253376167665978948859482725 47508031437371052911153011)
              ·
                refine ⟨71262047156056579366729517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47508031437371052911153011 71262047156056579366729517)
                ·
                  refine ⟨26723267683521217262523569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71262047156056579366729517 26723267683521217262523569)
                  ·
                    refine ⟨20042450762640912946892677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26723267683521217262523569 20042450762640912946892677)
                    ·
                      refine ⟨3757959517995171177542377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20042450762640912946892677 3757959517995171177542377)
                      ·
                        rfl

theorem cell23_7318600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_7318600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318600 prefixEnd_7318600 := by exact prefixLift 7318600
  have htrace : WordTrace (prefixWord ++ tailWord_7318600) baseStart_7318600 baseEnd_7318600 := by
    simpa [prefixWord, tailWord_7318600, baseEnd_7318600] using wordTrace_append hprefix tailTrace_7318600
  have hstable : (prefixWord ++ tailWord_7318600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318600).length < 2 ^ (prefixWord ++ tailWord_7318600).sum := by decide
  have hdescent : baseEnd_7318600 < baseStart_7318600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318610 : List Nat := [3, 2, 2, 1, 3, 1, 11]
def baseStart_7318610 : Nat := 118140960795 + 7318610 * 2 ^ 59
def prefixEnd_7318610 : Nat := 4983230072969 + 3 ^ 40 * 7318610 * 2
def baseEnd_7318610 : Nat := 46394625343231063437251

theorem tailTrace_7318610 : CollatzResearch.WordTrace tailWord_7318610 prefixEnd_7318610 46394625343231063437251 := by
  unfold tailWord_7318610
  simp only [CollatzResearch.WordTrace]
  refine ⟨66732909003983340980492321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177954424010622242614646189 66732909003983340980492321)
  ·
    refine ⟨50049681752987505735369241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66732909003983340980492321 50049681752987505735369241)
    ·
      refine ⟨37537261314740629301526931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50049681752987505735369241 37537261314740629301526931)
      ·
        refine ⟨56305891972110943952290397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37537261314740629301526931 56305891972110943952290397)
        ·
          refine ⟨21114709489541603982108899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56305891972110943952290397 21114709489541603982108899)
          ·
            refine ⟨31672064234312405973163349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21114709489541603982108899 31672064234312405973163349)
            ·
              refine ⟨46394625343231063437251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31672064234312405973163349 46394625343231063437251)
              ·
                rfl

theorem cell23_7318610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 11].length) (baseStart_7318610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318610 prefixEnd_7318610 := by exact prefixLift 7318610
  have htrace : WordTrace (prefixWord ++ tailWord_7318610) baseStart_7318610 baseEnd_7318610 := by
    simpa [prefixWord, tailWord_7318610, baseEnd_7318610] using wordTrace_append hprefix tailTrace_7318610
  have hstable : (prefixWord ++ tailWord_7318610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318610).length < 2 ^ (prefixWord ++ tailWord_7318610).sum := by decide
  have hdescent : baseEnd_7318610 < baseStart_7318610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318631 : List Nat := [1, 1, 5, 1, 1, 5, 2, 1, 2, 4]
def baseStart_7318631 : Nat := 118140960795 + 7318631 * 2 ^ 59
def prefixEnd_7318631 : Nat := 4983230072969 + 3 ^ 40 * 7318631 * 2
def baseEnd_7318631 : Nat := 1252658478631820185418245

theorem tailTrace_7318631 : CollatzResearch.WordTrace tailWord_7318631 prefixEnd_7318631 1252658478631820185418245 := by
  unfold tailWord_7318631
  simp only [CollatzResearch.WordTrace]
  refine ⟨266932401948857284508483747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177954934632571523005655831 266932401948857284508483747)
  ·
    refine ⟨400398602923285926762725621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266932401948857284508483747 400398602923285926762725621)
    ·
      refine ⟨37537369024058055634005527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 400398602923285926762725621 37537369024058055634005527)
      ·
        refine ⟨56306053536087083451008291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37537369024058055634005527 56306053536087083451008291)
        ·
          refine ⟨84459080304130625176512437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56306053536087083451008291 84459080304130625176512437)
          ·
            refine ⟨7918038778512246110298041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84459080304130625176512437 7918038778512246110298041)
            ·
              refine ⟨5938529083884184582723531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7918038778512246110298041 5938529083884184582723531)
              ·
                refine ⟨8907793625826276874085297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5938529083884184582723531 8907793625826276874085297)
                ·
                  refine ⟨6680845219369707655563973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8907793625826276874085297 6680845219369707655563973)
                  ·
                    refine ⟨1252658478631820185418245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6680845219369707655563973 1252658478631820185418245)
                    ·
                      rfl

theorem cell23_7318631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_7318631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318631 prefixEnd_7318631 := by exact prefixLift 7318631
  have htrace : WordTrace (prefixWord ++ tailWord_7318631) baseStart_7318631 baseEnd_7318631 := by
    simpa [prefixWord, tailWord_7318631, baseEnd_7318631] using wordTrace_append hprefix tailTrace_7318631
  have hstable : (prefixWord ++ tailWord_7318631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318631).length < 2 ^ (prefixWord ++ tailWord_7318631).sum := by decide
  have hdescent : baseEnd_7318631 < baseStart_7318631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318722 : List Nat := [3, 5, 1, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_7318722 : Nat := 118140960795 + 7318722 * 2 ^ 59
def prefixEnd_7318722 : Nat := 4983230072969 + 3 ^ 40 * 7318722 * 2
def baseEnd_7318722 : Nat := 3758022162635019700216817

theorem tailTrace_7318722 : CollatzResearch.WordTrace tailWord_7318722 prefixEnd_7318722 3758022162635019700216817 := by
  unfold tailWord_7318722
  simp only [CollatzResearch.WordTrace]
  refine ⟨66733930247881901762511605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177957147327685071366697613 66733930247881901762511605)
  ·
    refine ⟨6256305960738928290235463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66733930247881901762511605 6256305960738928290235463)
    ·
      refine ⟨9384458941108392435353195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6256305960738928290235463 9384458941108392435353195)
      ·
        refine ⟨14076688411662588653029793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9384458941108392435353195 14076688411662588653029793)
        ·
          refine ⟨10557516308746941489772345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14076688411662588653029793 10557516308746941489772345)
          ·
            refine ⟨7918137231560206117329259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10557516308746941489772345 7918137231560206117329259)
            ·
              refine ⟨11877205847340309175993889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7918137231560206117329259 11877205847340309175993889)
              ·
                refine ⟨8907904385505231881995417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11877205847340309175993889 8907904385505231881995417)
                ·
                  refine ⟨6680928289128923911496563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8907904385505231881995417 6680928289128923911496563)
                  ·
                    refine ⟨10021392433693385867244845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6680928289128923911496563 10021392433693385867244845)
                    ·
                      refine ⟨3758022162635019700216817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10021392433693385867244845 3758022162635019700216817)
                      ·
                        rfl

theorem cell23_7318722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_7318722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318722 prefixEnd_7318722 := by exact prefixLift 7318722
  have htrace : WordTrace (prefixWord ++ tailWord_7318722) baseStart_7318722 baseEnd_7318722 := by
    simpa [prefixWord, tailWord_7318722, baseEnd_7318722] using wordTrace_append hprefix tailTrace_7318722
  have hstable : (prefixWord ++ tailWord_7318722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318722).length < 2 ^ (prefixWord ++ tailWord_7318722).sum := by decide
  have hdescent : baseEnd_7318722 < baseStart_7318722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318734 : List Nat := [4, 1, 1, 1, 5, 1, 2, 1, 7]
def baseStart_7318734 : Nat := 118140960795 + 7318734 * 2 ^ 59
def prefixEnd_7318734 : Nat := 4983230072969 + 3 ^ 40 * 7318734 * 2
def baseEnd_7318734 : Nat := 417558702711430405918529

theorem tailTrace_7318734 : CollatzResearch.WordTrace tailWord_7318734 prefixEnd_7318734 417558702711430405918529 := by
  unfold tailWord_7318734
  simp only [CollatzResearch.WordTrace]
  refine ⟨33367019833435516637435407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177957439111656088732988837 33367019833435516637435407)
  ·
    refine ⟨50050529750153274956153111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33367019833435516637435407 50050529750153274956153111)
    ·
      refine ⟨75075794625229912434229667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50050529750153274956153111 75075794625229912434229667)
      ·
        refine ⟨112613691937844868651344501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75075794625229912434229667 112613691937844868651344501)
        ·
          refine ⟨10557533619172956436063547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112613691937844868651344501 10557533619172956436063547)
          ·
            refine ⟨15836300428759434654095321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10557533619172956436063547 15836300428759434654095321)
            ·
              refine ⟨11877225321569575990571491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15836300428759434654095321 11877225321569575990571491)
              ·
                refine ⟨17815837982354363985857237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11877225321569575990571491 17815837982354363985857237)
                ·
                  refine ⟨417558702711430405918529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17815837982354363985857237 417558702711430405918529)
                  ·
                    rfl

theorem cell23_7318734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_7318734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318734 prefixEnd_7318734 := by exact prefixLift 7318734
  have htrace : WordTrace (prefixWord ++ tailWord_7318734) baseStart_7318734 baseEnd_7318734 := by
    simpa [prefixWord, tailWord_7318734, baseEnd_7318734] using wordTrace_append hprefix tailTrace_7318734
  have hstable : (prefixWord ++ tailWord_7318734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318734).length < 2 ^ (prefixWord ++ tailWord_7318734).sum := by decide
  have hdescent : baseEnd_7318734 < baseStart_7318734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318821 : List Nat := [1, 3, 1, 2, 4, 2, 2, 1, 2, 2, 3]
def baseStart_7318821 : Nat := 118140960795 + 7318821 * 2 ^ 59
def prefixEnd_7318821 : Nat := 4983230072969 + 3 ^ 40 * 7318821 * 2
def baseEnd_7318821 : Nat := 3758072997219814812878861

theorem tailTrace_7318821 : CollatzResearch.WordTrace tailWord_7318821 prefixEnd_7318821 3758072997219814812878861 := by
  unfold tailWord_7318821
  simp only [CollatzResearch.WordTrace]
  refine ⟨266939331818168946957900317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177959554545445964638600211 266939331818168946957900317)
  ·
    refine ⟨100102249431813355109212619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266939331818168946957900317 100102249431813355109212619)
    ·
      refine ⟨150153374147720032663818929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100102249431813355109212619 150153374147720032663818929)
      ·
        refine ⟨112615030610790024497864197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150153374147720032663818929 112615030610790024497864197)
        ·
          refine ⟨21115318239523129593349537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112615030610790024497864197 21115318239523129593349537)
          ·
            refine ⟨15836488679642347195012153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21115318239523129593349537 15836488679642347195012153)
            ·
              refine ⟨11877366509731760396259115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15836488679642347195012153 11877366509731760396259115)
              ·
                refine ⟨17816049764597640594388673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11877366509731760396259115 17816049764597640594388673)
                ·
                  refine ⟨13362037323448230445791505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17816049764597640594388673 13362037323448230445791505)
                  ·
                    refine ⟨10021527992586172834343629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13362037323448230445791505 10021527992586172834343629)
                    ·
                      refine ⟨3758072997219814812878861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10021527992586172834343629 3758072997219814812878861)
                      ·
                        rfl

theorem cell23_7318821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_7318821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318821 prefixEnd_7318821 := by exact prefixLift 7318821
  have htrace : WordTrace (prefixWord ++ tailWord_7318821) baseStart_7318821 baseEnd_7318821 := by
    simpa [prefixWord, tailWord_7318821, baseEnd_7318821] using wordTrace_append hprefix tailTrace_7318821
  have hstable : (prefixWord ++ tailWord_7318821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318821).length < 2 ^ (prefixWord ++ tailWord_7318821).sum := by decide
  have hdescent : baseEnd_7318821 < baseStart_7318821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318841 : List Nat := [1, 2, 1, 6, 2, 1, 2, 2, 6]
def baseStart_7318841 : Nat := 118140960795 + 7318841 * 2 ^ 59
def prefixEnd_7318841 : Nat := 4983230072969 + 3 ^ 40 * 7318841 * 2
def baseEnd_7318841 : Nat := 417564807425878303847641

theorem tailTrace_7318841 : CollatzResearch.WordTrace tailWord_7318841 prefixEnd_7318841 417564807425878303847641 := by
  unfold tailWord_7318841
  simp only [CollatzResearch.WordTrace]
  refine ⟨266940061278096490373628377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177960040852064326915752251 266940061278096490373628377)
  ·
    refine ⟨200205045958572367780221283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266940061278096490373628377 200205045958572367780221283)
    ·
      refine ⟨300307568937858551670331925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200205045958572367780221283 300307568937858551670331925)
      ·
        refine ⟨14076917293962119609546809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 300307568937858551670331925 14076917293962119609546809)
        ·
          refine ⟨10557687970471589707160107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14076917293962119609546809 10557687970471589707160107)
          ·
            refine ⟨15836531955707384560740161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10557687970471589707160107 15836531955707384560740161)
            ·
              refine ⟨11877398966780538420555121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15836531955707384560740161 11877398966780538420555121)
              ·
                refine ⟨8908049225085403815416341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11877398966780538420555121 8908049225085403815416341)
                ·
                  refine ⟨417564807425878303847641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8908049225085403815416341 417564807425878303847641)
                  ·
                    rfl

theorem cell23_7318841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 6].length) (baseStart_7318841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318841 prefixEnd_7318841 := by exact prefixLift 7318841
  have htrace : WordTrace (prefixWord ++ tailWord_7318841) baseStart_7318841 baseEnd_7318841 := by
    simpa [prefixWord, tailWord_7318841, baseEnd_7318841] using wordTrace_append hprefix tailTrace_7318841
  have hstable : (prefixWord ++ tailWord_7318841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318841).length < 2 ^ (prefixWord ++ tailWord_7318841).sum := by decide
  have hdescent : baseEnd_7318841 < baseStart_7318841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318845 : List Nat := [1, 4, 1, 5, 1, 1, 1, 4, 1, 4]
def baseStart_7318845 : Nat := 118140960795 + 7318845 * 2 ^ 59
def prefixEnd_7318845 : Nat := 4983230072969 + 3 ^ 40 * 7318845 * 2
def baseEnd_7318845 : Nat := 1252695106918507572992917

theorem tailTrace_7318845 : CollatzResearch.WordTrace tailWord_7318845 prefixEnd_7318845 1252695106918507572992917 := by
  unfold tailWord_7318845
  simp only [CollatzResearch.WordTrace]
  refine ⟨266940207170081999056773989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177960138113387999371182659 266940207170081999056773989)
  ·
    refine ⟨50051288844390374823145123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266940207170081999056773989 50051288844390374823145123)
    ·
      refine ⟨75076933266585562234717685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50051288844390374823145123 75076933266585562234717685)
      ·
        refine ⟨7038462493742396459504783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75076933266585562234717685 7038462493742396459504783)
        ·
          refine ⟨10557693740613594689257175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7038462493742396459504783 10557693740613594689257175)
          ·
            refine ⟨15836540610920392033885763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10557693740613594689257175 15836540610920392033885763)
            ·
              refine ⟨23754810916380588050828645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15836540610920392033885763 23754810916380588050828645)
              ·
                refine ⟨4454027046821360259530371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23754810916380588050828645 4454027046821360259530371)
                ·
                  refine ⟨6681040570232040389295557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4454027046821360259530371 6681040570232040389295557)
                  ·
                    refine ⟨1252695106918507572992917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6681040570232040389295557 1252695106918507572992917)
                    ·
                      rfl

theorem cell23_7318845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_7318845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318845 prefixEnd_7318845 := by exact prefixLift 7318845
  have htrace : WordTrace (prefixWord ++ tailWord_7318845) baseStart_7318845 baseEnd_7318845 := by
    simpa [prefixWord, tailWord_7318845, baseEnd_7318845] using wordTrace_append hprefix tailTrace_7318845
  have hstable : (prefixWord ++ tailWord_7318845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318845).length < 2 ^ (prefixWord ++ tailWord_7318845).sum := by decide
  have hdescent : baseEnd_7318845 < baseStart_7318845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318874 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4]
def baseStart_7318874 : Nat := 118140960795 + 7318874 * 2 ^ 59
def prefixEnd_7318874 : Nat := 4983230072969 + 3 ^ 40 * 7318874 * 2
def baseEnd_7318874 : Nat := 3758100211694503105516117

theorem tailTrace_7318874 : CollatzResearch.WordTrace tailWord_7318874 prefixEnd_7318874 3758100211694503105516117 := by
  unfold tailWord_7318874
  simp only [CollatzResearch.WordTrace]
  refine ⟨66735316221744234252394919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177960843257984624673053117 66735316221744234252394919)
  ·
    refine ⟨100102974332616351378592379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66735316221744234252394919 100102974332616351378592379)
    ·
      refine ⟨150154461498924527067888569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100102974332616351378592379 150154461498924527067888569)
      ·
        refine ⟨112615846124193395300916427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150154461498924527067888569 112615846124193395300916427)
        ·
          refine ⟨168923769186290092951374641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112615846124193395300916427 168923769186290092951374641)
          ·
            refine ⟨126692826889717569713530981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168923769186290092951374641 126692826889717569713530981)
            ·
              refine ⟨23754905041822044321287059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126692826889717569713530981 23754905041822044321287059)
              ·
                refine ⟨35632357562733066481930589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23754905041822044321287059 35632357562733066481930589)
                ·
                  refine ⟨13362134086024899930723971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35632357562733066481930589 13362134086024899930723971)
                  ·
                    refine ⟨20043201129037349896085957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13362134086024899930723971 20043201129037349896085957)
                    ·
                      refine ⟨3758100211694503105516117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20043201129037349896085957 3758100211694503105516117)
                      ·
                        rfl

theorem cell23_7318874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_7318874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318874 prefixEnd_7318874 := by exact prefixLift 7318874
  have htrace : WordTrace (prefixWord ++ tailWord_7318874) baseStart_7318874 baseEnd_7318874 := by
    simpa [prefixWord, tailWord_7318874, baseEnd_7318874] using wordTrace_append hprefix tailTrace_7318874
  have hstable : (prefixWord ++ tailWord_7318874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318874).length < 2 ^ (prefixWord ++ tailWord_7318874).sum := by decide
  have hdescent : baseEnd_7318874 < baseStart_7318874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318884 : List Nat := [2, 3, 1, 1, 3, 2, 2, 2, 1, 6]
def baseStart_7318884 : Nat := 118140960795 + 7318884 * 2 ^ 59
def prefixEnd_7318884 : Nat := 4983230072969 + 3 ^ 40 * 7318884 * 2
def baseEnd_7318884 : Nat := 1252701782167016022130357

theorem tailTrace_7318884 : CollatzResearch.WordTrace tailWord_7318884 prefixEnd_7318884 1252701782167016022130357 := by
  unfold tailWord_7318884
  simp only [CollatzResearch.WordTrace]
  refine ⟨133470814808470354358721853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177961086411293805811629137 133470814808470354358721853)
  ·
    refine ⟨50051555553176382884520695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133470814808470354358721853 50051555553176382884520695)
    ·
      refine ⟨75077333329764574326781043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50051555553176382884520695 75077333329764574326781043)
      ·
        refine ⟨112615999994646861490171565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75077333329764574326781043 112615999994646861490171565)
        ·
          refine ⟨42230999997992573058814337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112615999994646861490171565 42230999997992573058814337)
          ·
            refine ⟨31673249998494429794110753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42230999997992573058814337 31673249998494429794110753)
            ·
              refine ⟨23754937498870822345583065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31673249998494429794110753 23754937498870822345583065)
              ·
                refine ⟨17816203124153116759187299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23754937498870822345583065 17816203124153116759187299)
                ·
                  refine ⟨26724304686229675138780949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17816203124153116759187299 26724304686229675138780949)
                  ·
                    refine ⟨1252701782167016022130357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26724304686229675138780949 1252701782167016022130357)
                    ·
                      rfl

theorem cell23_7318884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_7318884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318884 prefixEnd_7318884 := by exact prefixLift 7318884
  have htrace : WordTrace (prefixWord ++ tailWord_7318884) baseStart_7318884 baseEnd_7318884 := by
    simpa [prefixWord, tailWord_7318884, baseEnd_7318884] using wordTrace_append hprefix tailTrace_7318884
  have hstable : (prefixWord ++ tailWord_7318884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318884).length < 2 ^ (prefixWord ++ tailWord_7318884).sum := by decide
  have hdescent : baseEnd_7318884 < baseStart_7318884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318908 : List Nat := [2, 2, 2, 1, 1, 1, 6, 1, 3, 2, 2]
def baseStart_7318908 : Nat := 118140960795 + 7318908 * 2 ^ 59
def prefixEnd_7318908 : Nat := 4983230072969 + 3 ^ 40 * 7318908 * 2
def baseEnd_7318908 : Nat := 3758117670036755972490961

theorem tailTrace_7318908 : CollatzResearch.WordTrace tailWord_7318908 prefixEnd_7318908 3758117670036755972490961 := by
  unfold tailWord_7318908
  simp only [CollatzResearch.WordTrace]
  refine ⟨133471252484426880408158689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177961669979235840544211585 133471252484426880408158689)
  ·
    refine ⟨100103439363320160306119017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133471252484426880408158689 100103439363320160306119017)
    ·
      refine ⟨75077579522490120229589263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100103439363320160306119017 75077579522490120229589263)
      ·
        refine ⟨112616369283735180344383895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75077579522490120229589263 112616369283735180344383895)
        ·
          refine ⟨168924553925602770516575843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112616369283735180344383895 168924553925602770516575843)
          ·
            refine ⟨253386830888404155774863765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168924553925602770516575843 253386830888404155774863765)
            ·
              refine ⟨11877507697893944801946739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 253386830888404155774863765 11877507697893944801946739)
              ·
                refine ⟨17816261546840917202920109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11877507697893944801946739 17816261546840917202920109)
                ·
                  refine ⟨6681098080065343951095041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17816261546840917202920109 6681098080065343951095041)
                  ·
                    refine ⟨5010823560049007963321281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6681098080065343951095041 5010823560049007963321281)
                    ·
                      refine ⟨3758117670036755972490961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5010823560049007963321281 3758117670036755972490961)
                      ·
                        rfl

theorem cell23_7318908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_7318908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318908 prefixEnd_7318908 := by exact prefixLift 7318908
  have htrace : WordTrace (prefixWord ++ tailWord_7318908) baseStart_7318908 baseEnd_7318908 := by
    simpa [prefixWord, tailWord_7318908, baseEnd_7318908] using wordTrace_append hprefix tailTrace_7318908
  have hstable : (prefixWord ++ tailWord_7318908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318908).length < 2 ^ (prefixWord ++ tailWord_7318908).sum := by decide
  have hdescent : baseEnd_7318908 < baseStart_7318908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318974 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_7318974 : Nat := 118140960795 + 7318974 * 2 ^ 59
def prefixEnd_7318974 : Nat := 4983230072969 + 3 ^ 40 * 7318974 * 2
def baseEnd_7318974 : Nat := 1252717186586650904755219

theorem tailTrace_7318974 : CollatzResearch.WordTrace tailWord_7318974 prefixEnd_7318974 1252717186586650904755219 := by
  unfold tailWord_7318974
  simp only [CollatzResearch.WordTrace]
  refine ⟨33368114023326831761027497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177963274791076436058813317 33368114023326831761027497)
  ·
    refine ⟨25026085517495123820770623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33368114023326831761027497 25026085517495123820770623)
    ·
      refine ⟨37539128276242685731155935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25026085517495123820770623 37539128276242685731155935)
      ·
        refine ⟨56308692414364028596733903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37539128276242685731155935 56308692414364028596733903)
        ·
          refine ⟨84463038621546042895100855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56308692414364028596733903 84463038621546042895100855)
          ·
            refine ⟨126694557932319064342651283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84463038621546042895100855 126694557932319064342651283)
            ·
              refine ⟨190041836898478596513976925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126694557932319064342651283 190041836898478596513976925)
              ·
                refine ⟨71265688836929473692741347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190041836898478596513976925 71265688836929473692741347)
                ·
                  refine ⟨106898533255394210539112021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71265688836929473692741347 106898533255394210539112021)
                  ·
                    refine ⟨1252717186586650904755219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106898533255394210539112021 1252717186586650904755219)
                    ·
                      rfl

theorem cell23_7318974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_7318974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318974 prefixEnd_7318974 := by exact prefixLift 7318974
  have htrace : WordTrace (prefixWord ++ tailWord_7318974) baseStart_7318974 baseEnd_7318974 := by
    simpa [prefixWord, tailWord_7318974, baseEnd_7318974] using wordTrace_append hprefix tailTrace_7318974
  have hstable : (prefixWord ++ tailWord_7318974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318974).length < 2 ^ (prefixWord ++ tailWord_7318974).sum := by decide
  have hdescent : baseEnd_7318974 < baseStart_7318974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7318984 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_7318984 : Nat := 118140960795 + 7318984 * 2 ^ 59
def prefixEnd_7318984 : Nat := 4983230072969 + 3 ^ 40 * 7318984 * 2
def baseEnd_7318984 : Nat := 3758156694566497675140611

theorem tailTrace_7318984 : CollatzResearch.WordTrace tailWord_7318984 prefixEnd_7318984 3758156694566497675140611 := by
  unfold tailWord_7318984
  simp only [CollatzResearch.WordTrace]
  refine ⟨133472638458289212898042003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177963517944385617197389337 133472638458289212898042003)
  ·
    refine ⟨200208957687433819347063005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133472638458289212898042003 200208957687433819347063005)
    ·
      refine ⟨75078359132787682255148627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200208957687433819347063005 75078359132787682255148627)
      ·
        refine ⟨112617538699181523382722941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75078359132787682255148627 112617538699181523382722941)
        ·
          refine ⟨42231577012193071268521103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112617538699181523382722941 42231577012193071268521103)
          ·
            refine ⟨63347365518289606902781655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42231577012193071268521103 63347365518289606902781655)
            ·
              refine ⟨95021048277434410354172483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63347365518289606902781655 95021048277434410354172483)
              ·
                refine ⟨142531572416151615531258725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95021048277434410354172483 142531572416151615531258725)
                ·
                  refine ⟨26724669828028427912111011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142531572416151615531258725 26724669828028427912111011)
                  ·
                    refine ⟨40087004742042641868166517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26724669828028427912111011 40087004742042641868166517)
                    ·
                      refine ⟨3758156694566497675140611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40087004742042641868166517 3758156694566497675140611)
                      ·
                        rfl

theorem cell23_7318984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_7318984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7318984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7318984 prefixEnd_7318984 := by exact prefixLift 7318984
  have htrace : WordTrace (prefixWord ++ tailWord_7318984) baseStart_7318984 baseEnd_7318984 := by
    simpa [prefixWord, tailWord_7318984, baseEnd_7318984] using wordTrace_append hprefix tailTrace_7318984
  have hstable : (prefixWord ++ tailWord_7318984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7318984).length < 2 ^ (prefixWord ++ tailWord_7318984).sum := by decide
  have hdescent : baseEnd_7318984 < baseStart_7318984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7318984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319015 : List Nat := [1, 1, 5, 2, 1, 2, 1, 4, 2, 2, 2]
def baseStart_7319015 : Nat := 118140960795 + 7319015 * 2 ^ 59
def prefixEnd_7319015 : Nat := 4983230072969 + 3 ^ 40 * 7319015 * 2
def baseEnd_7319015 : Nat := 3758172612466787053852969

theorem tailTrace_7319015 : CollatzResearch.WordTrace tailWord_7319015 prefixEnd_7319015 3758172612466787053852969 := by
  unfold tailWord_7319015
  simp only [CollatzResearch.WordTrace]
  refine ⟨266946407579466118090462499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177964271719644078726974999 266946407579466118090462499)
  ·
    refine ⟨400419611369199177135693749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266946407579466118090462499 400419611369199177135693749)
    ·
      refine ⟨37539338565862422856471289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 400419611369199177135693749 37539338565862422856471289)
      ·
        refine ⟨28154503924396817142353467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37539338565862422856471289 28154503924396817142353467)
        ·
          refine ⟨42231755886595225713530201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28154503924396817142353467 42231755886595225713530201)
          ·
            refine ⟨31673816914946419285147651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42231755886595225713530201 31673816914946419285147651)
            ·
              refine ⟨47510725372419628927721477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31673816914946419285147651 47510725372419628927721477)
              ·
                refine ⟨8908261007328680423947777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47510725372419628927721477 8908261007328680423947777)
                ·
                  refine ⟨6681195755496510317960833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8908261007328680423947777 6681195755496510317960833)
                  ·
                    refine ⟨5010896816622382738470625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6681195755496510317960833 5010896816622382738470625)
                    ·
                      refine ⟨3758172612466787053852969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5010896816622382738470625 3758172612466787053852969)
                      ·
                        rfl

theorem cell23_7319015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_7319015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319015 prefixEnd_7319015 := by exact prefixLift 7319015
  have htrace : WordTrace (prefixWord ++ tailWord_7319015) baseStart_7319015 baseEnd_7319015 := by
    simpa [prefixWord, tailWord_7319015, baseEnd_7319015] using wordTrace_append hprefix tailTrace_7319015
  have hstable : (prefixWord ++ tailWord_7319015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319015).length < 2 ^ (prefixWord ++ tailWord_7319015).sum := by decide
  have hdescent : baseEnd_7319015 < baseStart_7319015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319034 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 1, 7]
def baseStart_7319034 : Nat := 118140960795 + 7319034 * 2 ^ 59
def prefixEnd_7319034 : Nat := 4983230072969 + 3 ^ 40 * 7319034 * 2
def baseEnd_7319034 : Nat := 1252727456199740826505127

theorem tailTrace_7319034 : CollatzResearch.WordTrace tailWord_7319034 prefixEnd_7319034 1252727456199740826505127 := by
  unfold tailWord_7319034
  simp only [CollatzResearch.WordTrace]
  refine ⟨66736775141599321083851039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177964733710931522890269437 66736775141599321083851039)
  ·
    refine ⟨100105162712398981625776559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66736775141599321083851039 100105162712398981625776559)
    ·
      refine ⟨150157744068598472438664839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100105162712398981625776559 150157744068598472438664839)
      ·
        refine ⟨225236616102897708657997259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150157744068598472438664839 225236616102897708657997259)
        ·
          refine ⟨337854924154346562986995889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225236616102897708657997259 337854924154346562986995889)
          ·
            refine ⟨253391193115759922240246917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337854924154346562986995889 253391193115759922240246917)
            ·
              refine ⟨47510848709204985420046297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253391193115759922240246917 47510848709204985420046297)
              ·
                refine ⟨35633136531903739065034723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47510848709204985420046297 35633136531903739065034723)
                ·
                  refine ⟨53449704797855608597552085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35633136531903739065034723 53449704797855608597552085)
                  ·
                    refine ⟨1252727456199740826505127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53449704797855608597552085 1252727456199740826505127)
                    ·
                      rfl

theorem cell23_7319034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_7319034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319034 prefixEnd_7319034 := by exact prefixLift 7319034
  have htrace : WordTrace (prefixWord ++ tailWord_7319034) baseStart_7319034 baseEnd_7319034 := by
    simpa [prefixWord, tailWord_7319034, baseEnd_7319034] using wordTrace_append hprefix tailTrace_7319034
  have hstable : (prefixWord ++ tailWord_7319034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319034).length < 2 ^ (prefixWord ++ tailWord_7319034).sum := by decide
  have hdescent : baseEnd_7319034 < baseStart_7319034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319051 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 1, 7]
def baseStart_7319051 : Nat := 118140960795 + 7319051 * 2 ^ 59
def prefixEnd_7319051 : Nat := 4983230072969 + 3 ^ 40 * 7319051 * 2
def baseEnd_7319051 : Nat := 1252730365923449637667601

theorem tailTrace_7319051 : CollatzResearch.WordTrace tailWord_7319051 prefixEnd_7319051 1252730365923449637667601 := by
  unfold tailWord_7319051
  simp only [CollatzResearch.WordTrace]
  refine ⟨266947720607335696238773007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177965147071557130825848671 266947720607335696238773007)
  ·
    refine ⟨400421580911003544358159511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266947720607335696238773007 400421580911003544358159511)
    ·
      refine ⟨600632371366505316537239267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400421580911003544358159511 600632371366505316537239267)
      ·
        refine ⟨900948557049757974805858901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600632371366505316537239267 900948557049757974805858901)
        ·
          refine ⟨10557990902926851267256159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 900948557049757974805858901 10557990902926851267256159)
          ·
            refine ⟨15836986354390276900884239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10557990902926851267256159 15836986354390276900884239)
            ·
              refine ⟨23755479531585415351326359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15836986354390276900884239 23755479531585415351326359)
              ·
                refine ⟨35633219297378123026989539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23755479531585415351326359 35633219297378123026989539)
                ·
                  refine ⟨53449828946067184540484309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35633219297378123026989539 53449828946067184540484309)
                  ·
                    refine ⟨1252730365923449637667601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53449828946067184540484309 1252730365923449637667601)
                    ·
                      rfl

theorem cell23_7319051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 7].length) (baseStart_7319051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319051 prefixEnd_7319051 := by exact prefixLift 7319051
  have htrace : WordTrace (prefixWord ++ tailWord_7319051) baseStart_7319051 baseEnd_7319051 := by
    simpa [prefixWord, tailWord_7319051, baseEnd_7319051] using wordTrace_append hprefix tailTrace_7319051
  have hstable : (prefixWord ++ tailWord_7319051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319051).length < 2 ^ (prefixWord ++ tailWord_7319051).sum := by decide
  have hdescent : baseEnd_7319051 < baseStart_7319051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319053 : List Nat := [1, 7, 1, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_7319053 : Nat := 118140960795 + 7319053 * 2 ^ 59
def prefixEnd_7319053 : Nat := 4983230072969 + 3 ^ 40 * 7319053 * 2
def baseEnd_7319053 : Nat := 3758192124731657905177795

theorem tailTrace_7319053 : CollatzResearch.WordTrace tailWord_7319053 prefixEnd_7319053 3758192124731657905177795 := by
  unfold tailWord_7319053
  simp only [CollatzResearch.WordTrace]
  refine ⟨266947793553328450580345813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177965195702218967053563875 266947793553328450580345813)
  ·
    refine ⟨6256588911406135560476855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 266947793553328450580345813 6256588911406135560476855)
    ·
      refine ⟨9384883367109203340715283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6256588911406135560476855 9384883367109203340715283)
      ·
        refine ⟨14077325050663805011072925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9384883367109203340715283 14077325050663805011072925)
        ·
          refine ⟨5278996893998926879152347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14077325050663805011072925 5278996893998926879152347)
          ·
            refine ⟨7918495340998390318728521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5278996893998926879152347 7918495340998390318728521)
            ·
              refine ⟨5938871505748792739046391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7918495340998390318728521 5938871505748792739046391)
              ·
                refine ⟨8908307258623189108569587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5938871505748792739046391 8908307258623189108569587)
                ·
                  refine ⟨13362460887934783662854381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8908307258623189108569587 13362460887934783662854381)
                  ·
                    refine ⟨5010922832975543873570393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13362460887934783662854381 5010922832975543873570393)
                    ·
                      refine ⟨3758192124731657905177795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5010922832975543873570393 3758192124731657905177795)
                      ·
                        rfl

theorem cell23_7319053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_7319053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319053 prefixEnd_7319053 := by exact prefixLift 7319053
  have htrace : WordTrace (prefixWord ++ tailWord_7319053) baseStart_7319053 baseEnd_7319053 := by
    simpa [prefixWord, tailWord_7319053, baseEnd_7319053] using wordTrace_append hprefix tailTrace_7319053
  have hstable : (prefixWord ++ tailWord_7319053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319053).length < 2 ^ (prefixWord ++ tailWord_7319053).sum := by decide
  have hdescent : baseEnd_7319053 < baseStart_7319053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319071 : List Nat := [1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 4]
def baseStart_7319071 : Nat := 118140960795 + 7319071 * 2 ^ 59
def prefixEnd_7319071 : Nat := 4983230072969 + 3 ^ 40 * 7319071 * 2
def baseEnd_7319071 : Nat := 3758201367383438834752711

theorem tailTrace_7319071 : CollatzResearch.WordTrace tailWord_7319071 prefixEnd_7319071 3758201367383438834752711 := by
  unfold tailWord_7319071
  simp only [CollatzResearch.WordTrace]
  refine ⟨266948450067263239654501067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177965633378175493103000711 266948450067263239654501067)
  ·
    refine ⟨400422675100894859481751601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266948450067263239654501067 400422675100894859481751601)
    ·
      refine ⟨300317006325671144611313701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400422675100894859481751601 300317006325671144611313701)
      ·
        refine ⟨56309438686063339614621319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300317006325671144611313701 56309438686063339614621319)
        ·
          refine ⟨84464158029095009421931979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56309438686063339614621319 84464158029095009421931979)
          ·
            refine ⟨126696237043642514132897969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84464158029095009421931979 126696237043642514132897969)
            ·
              refine ⟨95022177782731885599673477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126696237043642514132897969 95022177782731885599673477)
              ·
                refine ⟨17816658334262228549938777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95022177782731885599673477 17816658334262228549938777)
                ·
                  refine ⟨13362493750696671412454083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17816658334262228549938777 13362493750696671412454083)
                  ·
                    refine ⟨20043740626045007118681125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13362493750696671412454083 20043740626045007118681125)
                    ·
                      refine ⟨3758201367383438834752711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20043740626045007118681125 3758201367383438834752711)
                      ·
                        rfl

theorem cell23_7319071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_7319071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319071 prefixEnd_7319071 := by exact prefixLift 7319071
  have htrace : WordTrace (prefixWord ++ tailWord_7319071) baseStart_7319071 baseEnd_7319071 := by
    simpa [prefixWord, tailWord_7319071, baseEnd_7319071] using wordTrace_append hprefix tailTrace_7319071
  have hstable : (prefixWord ++ tailWord_7319071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319071).length < 2 ^ (prefixWord ++ tailWord_7319071).sum := by decide
  have hdescent : baseEnd_7319071 < baseStart_7319071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319091 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 3]
def baseStart_7319091 : Nat := 118140960795 + 7319091 * 2 ^ 59
def prefixEnd_7319091 : Nat := 4983230072969 + 3 ^ 40 * 7319091 * 2
def baseEnd_7319091 : Nat := 3758211636996528756502619

theorem tailTrace_7319091 : CollatzResearch.WordTrace tailWord_7319091 prefixEnd_7319091 3758211636996528756502619 := by
  unfold tailWord_7319091
  simp only [CollatzResearch.WordTrace]
  refine ⟨266949179527190783070229127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177966119684793855380152751 266949179527190783070229127)
  ·
    refine ⟨400423769290786174605343691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266949179527190783070229127 400423769290786174605343691)
    ·
      refine ⟨600635653936179261908015537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400423769290786174605343691 600635653936179261908015537)
      ·
        refine ⟨450476740452134446431011653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600635653936179261908015537 450476740452134446431011653)
        ·
          refine ⟨84464388834775208705814685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 450476740452134446431011653 84464388834775208705814685)
          ·
            refine ⟨31674145813040703264680507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84464388834775208705814685 31674145813040703264680507)
            ·
              refine ⟨47511218719561054897020761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31674145813040703264680507 47511218719561054897020761)
              ·
                refine ⟨35633414039670791172765571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47511218719561054897020761 35633414039670791172765571)
                ·
                  refine ⟨53450121059506186759148357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35633414039670791172765571 53450121059506186759148357)
                  ·
                    refine ⟨10021897698657410017340317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53450121059506186759148357 10021897698657410017340317)
                    ·
                      refine ⟨3758211636996528756502619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10021897698657410017340317 3758211636996528756502619)
                      ·
                        rfl

theorem cell23_7319091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 3].length) (baseStart_7319091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319091 prefixEnd_7319091 := by exact prefixLift 7319091
  have htrace : WordTrace (prefixWord ++ tailWord_7319091) baseStart_7319091 baseEnd_7319091 := by
    simpa [prefixWord, tailWord_7319091, baseEnd_7319091] using wordTrace_append hprefix tailTrace_7319091
  have hstable : (prefixWord ++ tailWord_7319091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319091).length < 2 ^ (prefixWord ++ tailWord_7319091).sum := by decide
  have hdescent : baseEnd_7319091 < baseStart_7319091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319148 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 6, 3, 2]
def baseStart_7319148 : Nat := 118140960795 + 7319148 * 2 ^ 59
def prefixEnd_7319148 : Nat := 4983230072969 + 3 ^ 40 * 7319148 * 2
def baseEnd_7319148 : Nat := 3758240905393835033489857

theorem tailTrace_7319148 : CollatzResearch.WordTrace tailWord_7319148 prefixEnd_7319148 3758240905393835033489857 := by
  unfold tailWord_7319148
  simp only [CollatzResearch.WordTrace]
  refine ⟨133475629243992140902527049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177967505658656187870036065 133475629243992140902527049)
  ·
    refine ⟨100106721932994105676895287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133475629243992140902527049 100106721932994105676895287)
    ·
      refine ⟨150160082899491158515342931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100106721932994105676895287 150160082899491158515342931)
      ·
        refine ⟨225240124349236737773014397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150160082899491158515342931 225240124349236737773014397)
        ·
          refine ⟨84465046630963776664880399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225240124349236737773014397 84465046630963776664880399)
          ·
            refine ⟨126697569946445664997320599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84465046630963776664880399 126697569946445664997320599)
            ·
              refine ⟨190046354919668497495980899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126697569946445664997320599 190046354919668497495980899)
              ·
                refine ⟨285069532379502746243971349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190046354919668497495980899 285069532379502746243971349)
                ·
                  refine ⟨13362634330289191230186157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 285069532379502746243971349 13362634330289191230186157)
                  ·
                    refine ⟨5010987873858446711319809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13362634330289191230186157 5010987873858446711319809)
                    ·
                      refine ⟨3758240905393835033489857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5010987873858446711319809 3758240905393835033489857)
                      ·
                        rfl

theorem cell23_7319148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 3, 2].length) (baseStart_7319148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319148 prefixEnd_7319148 := by exact prefixLift 7319148
  have htrace : WordTrace (prefixWord ++ tailWord_7319148) baseStart_7319148 baseEnd_7319148 := by
    simpa [prefixWord, tailWord_7319148, baseEnd_7319148] using wordTrace_append hprefix tailTrace_7319148
  have hstable : (prefixWord ++ tailWord_7319148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319148).length < 2 ^ (prefixWord ++ tailWord_7319148).sum := by decide
  have hdescent : baseEnd_7319148 < baseStart_7319148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319165 : List Nat := [1, 4, 1, 1, 4, 1, 1, 3, 2, 3, 2]
def baseStart_7319165 : Nat := 118140960795 + 7319165 * 2 ^ 59
def prefixEnd_7319165 : Nat := 4983230072969 + 3 ^ 40 * 7319165 * 2
def baseEnd_7319165 : Nat := 3758249634564961466977279

theorem tailTrace_7319165 : CollatzResearch.WordTrace tailWord_7319165 prefixEnd_7319165 3758249634564961466977279 := by
  unfold tailWord_7319165
  simp only [CollatzResearch.WordTrace]
  refine ⟨266951878528922693708422949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177967919019281795805615299 266951878528922693708422949)
  ·
    refine ⟨50053477224173005070329303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266951878528922693708422949 50053477224173005070329303)
    ·
      refine ⟨75080215836259507605493955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50053477224173005070329303 75080215836259507605493955)
      ·
        refine ⟨112620323754389261408240933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75080215836259507605493955 112620323754389261408240933)
        ·
          refine ⟨21116310703947986514045175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112620323754389261408240933 21116310703947986514045175)
          ·
            refine ⟨31674466055921979771067763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21116310703947986514045175 31674466055921979771067763)
            ·
              refine ⟨47511699083882969656601645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31674466055921979771067763 47511699083882969656601645)
              ·
                refine ⟨17816887156456113621225617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47511699083882969656601645 17816887156456113621225617)
                ·
                  refine ⟨13362665367342085215919213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17816887156456113621225617 13362665367342085215919213)
                  ·
                    refine ⟨5010999512753281955969705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13362665367342085215919213 5010999512753281955969705)
                    ·
                      refine ⟨3758249634564961466977279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5010999512753281955969705 3758249634564961466977279)
                      ·
                        rfl

theorem cell23_7319165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_7319165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319165 prefixEnd_7319165 := by exact prefixLift 7319165
  have htrace : WordTrace (prefixWord ++ tailWord_7319165) baseStart_7319165 baseEnd_7319165 := by
    simpa [prefixWord, tailWord_7319165, baseEnd_7319165] using wordTrace_append hprefix tailTrace_7319165
  have hstable : (prefixWord ++ tailWord_7319165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319165).length < 2 ^ (prefixWord ++ tailWord_7319165).sum := by decide
  have hdescent : baseEnd_7319165 < baseStart_7319165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319175 : List Nat := [1, 1, 4, 2, 1, 4, 3, 1, 1, 5]
def baseStart_7319175 : Nat := 118140960795 + 7319175 * 2 ^ 59
def prefixEnd_7319175 : Nat := 4983230072969 + 3 ^ 40 * 7319175 * 2
def baseEnd_7319175 : Nat := 1252751589790502142617411

theorem tailTrace_7319175 : CollatzResearch.WordTrace tailWord_7319175 prefixEnd_7319175 1252751589790502142617411 := by
  unfold tailWord_7319175
  simp only [CollatzResearch.WordTrace]
  refine ⟨266952243258886465416286979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177968162172590976944191319 266952243258886465416286979)
  ·
    refine ⟨400428364888329698124430469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266952243258886465416286979 400428364888329698124430469)
    ·
      refine ⟨75080318416561818398330713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 400428364888329698124430469 75080318416561818398330713)
      ·
        refine ⟨56310238812421363798748035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75080318416561818398330713 56310238812421363798748035)
        ·
          refine ⟨84465358218632045698122053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56310238812421363798748035 84465358218632045698122053)
          ·
            refine ⟨15837254665993508568397885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84465358218632045698122053 15837254665993508568397885)
            ·
              refine ⟨5938970499747565713149207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15837254665993508568397885 5938970499747565713149207)
              ·
                refine ⟨8908455749621348569723811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5938970499747565713149207 8908455749621348569723811)
                ·
                  refine ⟨13362683624432022854585717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8908455749621348569723811 13362683624432022854585717)
                  ·
                    refine ⟨1252751589790502142617411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13362683624432022854585717 1252751589790502142617411)
                    ·
                      rfl

theorem cell23_7319175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_7319175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319175 prefixEnd_7319175 := by exact prefixLift 7319175
  have htrace : WordTrace (prefixWord ++ tailWord_7319175) baseStart_7319175 baseEnd_7319175 := by
    simpa [prefixWord, tailWord_7319175, baseEnd_7319175] using wordTrace_append hprefix tailTrace_7319175
  have hstable : (prefixWord ++ tailWord_7319175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319175).length < 2 ^ (prefixWord ++ tailWord_7319175).sum := by decide
  have hdescent : baseEnd_7319175 < baseStart_7319175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319229 : List Nat := [1, 4, 1, 2, 1, 2, 4, 3, 1, 2, 2]
def baseStart_7319229 : Nat := 118140960795 + 7319229 * 2 ^ 59
def prefixEnd_7319229 : Nat := 4983230072969 + 3 ^ 40 * 7319229 * 2
def baseEnd_7319229 : Nat := 3758282497326849216576985

theorem tailTrace_7319229 : CollatzResearch.WordTrace tailWord_7319229 prefixEnd_7319229 3758282497326849216576985 := by
  unfold tailWord_7319229
  simp only [CollatzResearch.WordTrace]
  refine ⟨266954212800690832638752741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177969475200460555092501827 266954212800690832638752741)
  ·
    refine ⟨50053914900129531119766139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266954212800690832638752741 50053914900129531119766139)
    ·
      refine ⟨75080872350194296679649209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50053914900129531119766139 75080872350194296679649209)
      ·
        refine ⟨56310654262645722509736907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75080872350194296679649209 56310654262645722509736907)
        ·
          refine ⟨84465981393968583764605361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56310654262645722509736907 84465981393968583764605361)
          ·
            refine ⟨63349486045476437823454021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84465981393968583764605361 63349486045476437823454021)
            ·
              refine ⟨11878028633526832091897629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63349486045476437823454021 11878028633526832091897629)
              ·
                refine ⟨4454260737572562034461611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11878028633526832091897629 4454260737572562034461611)
                ·
                  refine ⟨6681391106358843051692417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4454260737572562034461611 6681391106358843051692417)
                  ·
                    refine ⟨5011043329769132288769313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6681391106358843051692417 5011043329769132288769313)
                    ·
                      refine ⟨3758282497326849216576985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5011043329769132288769313 3758282497326849216576985)
                      ·
                        rfl

theorem cell23_7319229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_7319229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319229 prefixEnd_7319229 := by exact prefixLift 7319229
  have htrace : WordTrace (prefixWord ++ tailWord_7319229) baseStart_7319229 baseEnd_7319229 := by
    simpa [prefixWord, tailWord_7319229, baseEnd_7319229] using wordTrace_append hprefix tailTrace_7319229
  have hstable : (prefixWord ++ tailWord_7319229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319229).length < 2 ^ (prefixWord ++ tailWord_7319229).sum := by decide
  have hdescent : baseEnd_7319229 < baseStart_7319229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319251 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 4]
def baseStart_7319251 : Nat := 118140960795 + 7319251 * 2 ^ 59
def prefixEnd_7319251 : Nat := 4983230072969 + 3 ^ 40 * 7319251 * 2
def baseEnd_7319251 : Nat := 3758293793901248130501883

theorem tailTrace_7319251 : CollatzResearch.WordTrace tailWord_7319251 prefixEnd_7319251 3758293793901248130501883 := by
  unfold tailWord_7319251
  simp only [CollatzResearch.WordTrace]
  refine ⟨266955015206611130396053607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177970010137740753597369071 266955015206611130396053607)
  ·
    refine ⟨400432522809916695594080411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266955015206611130396053607 400432522809916695594080411)
    ·
      refine ⟨600648784214875043391120617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400432522809916695594080411 600648784214875043391120617)
      ·
        refine ⟨450486588161156282543340463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600648784214875043391120617 450486588161156282543340463)
        ·
          refine ⟨675729882241734423815010695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450486588161156282543340463 675729882241734423815010695)
          ·
            refine ⟨1013594823362601635722516043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675729882241734423815010695 1013594823362601635722516043)
            ·
              refine ⟨1520392235043902453583774065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013594823362601635722516043 1520392235043902453583774065)
              ·
                refine ⟨1140294176282926840187830549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1520392235043902453583774065 1140294176282926840187830549)
                ·
                  refine ⟨53451289513262195633804557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1140294176282926840187830549 53451289513262195633804557)
                  ·
                    refine ⟨20044233567473323362676709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53451289513262195633804557 20044233567473323362676709)
                    ·
                      refine ⟨3758293793901248130501883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20044233567473323362676709 3758293793901248130501883)
                      ·
                        rfl

theorem cell23_7319251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_7319251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319251 prefixEnd_7319251 := by exact prefixLift 7319251
  have htrace : WordTrace (prefixWord ++ tailWord_7319251) baseStart_7319251 baseEnd_7319251 := by
    simpa [prefixWord, tailWord_7319251, baseEnd_7319251] using wordTrace_append hprefix tailTrace_7319251
  have hstable : (prefixWord ++ tailWord_7319251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319251).length < 2 ^ (prefixWord ++ tailWord_7319251).sum := by decide
  have hdescent : baseEnd_7319251 < baseStart_7319251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319272 : List Nat := [2, 1, 4, 1, 3, 1, 1, 4, 1, 3, 2]
def baseStart_7319272 : Nat := 118140960795 + 7319272 * 2 ^ 59
def prefixEnd_7319272 : Nat := 4983230072969 + 3 ^ 40 * 7319272 * 2
def baseEnd_7319272 : Nat := 3758304576994992548339287

theorem tailTrace_7319272 : CollatzResearch.WordTrace tailWord_7319272 prefixEnd_7319272 3758304576994992548339287 := by
  unfold tailWord_7319272
  simp only [CollatzResearch.WordTrace]
  refine ⟨133477890569767525491284035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177970520759690033988378713 133477890569767525491284035)
  ·
    refine ⟨200216835854651288236926053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133477890569767525491284035 200216835854651288236926053)
    ·
      refine ⟨37540656722747116544423635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200216835854651288236926053 37540656722747116544423635)
      ·
        refine ⟨56310985084120674816635453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37540656722747116544423635 56310985084120674816635453)
        ·
          refine ⟨21116619406545253056238295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56310985084120674816635453 21116619406545253056238295)
          ·
            refine ⟨31674929109817879584357443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21116619406545253056238295 31674929109817879584357443)
            ·
              refine ⟨47512393664726819376536165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31674929109817879584357443 47512393664726819376536165)
              ·
                refine ⟨8908573812136278633100531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47512393664726819376536165 8908573812136278633100531)
                ·
                  refine ⟨13362860718204417949650797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8908573812136278633100531 13362860718204417949650797)
                  ·
                    refine ⟨5011072769326656731119049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13362860718204417949650797 5011072769326656731119049)
                    ·
                      refine ⟨3758304576994992548339287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5011072769326656731119049 3758304576994992548339287)
                      ·
                        rfl

theorem cell23_7319272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_7319272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319272 prefixEnd_7319272 := by exact prefixLift 7319272
  have htrace : WordTrace (prefixWord ++ tailWord_7319272) baseStart_7319272 baseEnd_7319272 := by
    simpa [prefixWord, tailWord_7319272, baseEnd_7319272] using wordTrace_append hprefix tailTrace_7319272
  have hstable : (prefixWord ++ tailWord_7319272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319272).length < 2 ^ (prefixWord ++ tailWord_7319272).sum := by decide
  have hdescent : baseEnd_7319272 < baseStart_7319272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319308 : List Nat := [2, 2, 1, 2, 2, 1, 5, 1, 7]
def baseStart_7319308 : Nat := 118140960795 + 7319308 * 2 ^ 59
def prefixEnd_7319308 : Nat := 4983230072969 + 3 ^ 40 * 7319308 * 2
def baseEnd_7319308 : Nat := 417591451366506045276569

theorem tailTrace_7319308 : CollatzResearch.WordTrace tailWord_7319308 prefixEnd_7319308 417591451366506045276569 := by
  unfold tailWord_7319308
  simp only [CollatzResearch.WordTrace]
  refine ⟨133478547083702314565439289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177971396111603086087252385 133478547083702314565439289)
  ·
    refine ⟨100108910312776735924079467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133478547083702314565439289 100108910312776735924079467)
    ·
      refine ⟨150163365469165103886119201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100108910312776735924079467 150163365469165103886119201)
      ·
        refine ⟨112622524101873827914589401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150163365469165103886119201 112622524101873827914589401)
        ·
          refine ⟨84466893076405370935942051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112622524101873827914589401 84466893076405370935942051)
          ·
            refine ⟨126700339614608056403913077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84466893076405370935942051 126700339614608056403913077)
            ·
              refine ⟨11878156838869505287866851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126700339614608056403913077 11878156838869505287866851)
              ·
                refine ⟨17817235258304257931800277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11878156838869505287866851 17817235258304257931800277)
                ·
                  refine ⟨417591451366506045276569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17817235258304257931800277 417591451366506045276569)
                  ·
                    rfl

theorem cell23_7319308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 7].length) (baseStart_7319308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319308 prefixEnd_7319308 := by exact prefixLift 7319308
  have htrace : WordTrace (prefixWord ++ tailWord_7319308) baseStart_7319308 baseEnd_7319308 := by
    simpa [prefixWord, tailWord_7319308, baseEnd_7319308] using wordTrace_append hprefix tailTrace_7319308
  have hstable : (prefixWord ++ tailWord_7319308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319308).length < 2 ^ (prefixWord ++ tailWord_7319308).sum := by decide
  have hdescent : baseEnd_7319308 < baseStart_7319308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319311 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 8]
def baseStart_7319311 : Nat := 118140960795 + 7319311 * 2 ^ 59
def prefixEnd_7319311 : Nat := 4983230072969 + 3 ^ 40 * 7319311 * 2
def baseEnd_7319311 : Nat := 3758324602740517895751607

theorem tailTrace_7319311 : CollatzResearch.WordTrace tailWord_7319311 prefixEnd_7319311 3758324602740517895751607 := by
  unfold tailWord_7319311
  simp only [CollatzResearch.WordTrace]
  refine ⟨266957203586393760643237787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177971469057595840428825191 266957203586393760643237787)
  ·
    refine ⟨400435805379590640964856681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266957203586393760643237787 400435805379590640964856681)
    ·
      refine ⟨300326854034692980723642511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400435805379590640964856681 300326854034692980723642511)
      ·
        refine ⟨450490281052039471085463767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300326854034692980723642511 450490281052039471085463767)
        ·
          refine ⟨675735421578059206628195651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450490281052039471085463767 675735421578059206628195651)
          ·
            refine ⟨1013603132367088809942293477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675735421578059206628195651 1013603132367088809942293477)
            ·
              refine ⟨190050587318829151864180027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1013603132367088809942293477 190050587318829151864180027)
              ·
                refine ⟨285075880978243727796270041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190050587318829151864180027 285075880978243727796270041)
                ·
                  refine ⟨213806910733682795847202531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285075880978243727796270041 213806910733682795847202531)
                  ·
                    refine ⟨320710366100524193770803797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 213806910733682795847202531 320710366100524193770803797)
                    ·
                      refine ⟨3758324602740517895751607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 320710366100524193770803797 3758324602740517895751607)
                      ·
                        rfl

theorem cell23_7319311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_7319311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319311 prefixEnd_7319311 := by exact prefixLift 7319311
  have htrace : WordTrace (prefixWord ++ tailWord_7319311) baseStart_7319311 baseEnd_7319311 := by
    simpa [prefixWord, tailWord_7319311, baseEnd_7319311] using wordTrace_append hprefix tailTrace_7319311
  have hstable : (prefixWord ++ tailWord_7319311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319311).length < 2 ^ (prefixWord ++ tailWord_7319311).sum := by decide
  have hdescent : baseEnd_7319311 < baseStart_7319311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319319 : List Nat := [1, 1, 3, 4, 2, 2, 1, 3, 2, 2, 2]
def baseStart_7319319 : Nat := 118140960795 + 7319319 * 2 ^ 59
def prefixEnd_7319319 : Nat := 4983230072969 + 3 ^ 40 * 7319319 * 2
def baseEnd_7319319 : Nat := 3758328710585753864451571

theorem tailTrace_7319319 : CollatzResearch.WordTrace tailWord_7319319 prefixEnd_7319319 3758328710585753864451571 := by
  unfold tailWord_7319319
  simp only [CollatzResearch.WordTrace]
  refine ⟨266957495370364778009529011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177971663580243185339686007 266957495370364778009529011)
  ·
    refine ⟨400436243055547167014293517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266957495370364778009529011 400436243055547167014293517)
    ·
      refine ⟨150163591145830187630360069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400436243055547167014293517 150163591145830187630360069)
      ·
        refine ⟨28155673339843160180692513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150163591145830187630360069 28155673339843160180692513)
        ·
          refine ⟨21116755004882370135519385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28155673339843160180692513 21116755004882370135519385)
          ·
            refine ⟨15837566253661777601639539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21116755004882370135519385 15837566253661777601639539)
            ·
              refine ⟨23756349380492666402459309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15837566253661777601639539 23756349380492666402459309)
              ·
                refine ⟨8908631017684749900922241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23756349380492666402459309 8908631017684749900922241)
                ·
                  refine ⟨6681473263263562425691681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8908631017684749900922241 6681473263263562425691681)
                  ·
                    refine ⟨5011104947447671819268761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6681473263263562425691681 5011104947447671819268761)
                    ·
                      refine ⟨3758328710585753864451571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5011104947447671819268761 3758328710585753864451571)
                      ·
                        rfl

theorem cell23_7319319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_7319319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319319 prefixEnd_7319319 := by exact prefixLift 7319319
  have htrace : WordTrace (prefixWord ++ tailWord_7319319) baseStart_7319319 baseEnd_7319319 := by
    simpa [prefixWord, tailWord_7319319, baseEnd_7319319] using wordTrace_append hprefix tailTrace_7319319
  have hstable : (prefixWord ++ tailWord_7319319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319319).length < 2 ^ (prefixWord ++ tailWord_7319319).sum := by decide
  have hdescent : baseEnd_7319319 < baseStart_7319319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319359 : List Nat := [1, 1, 2, 2, 6, 2, 2, 2, 5]
def baseStart_7319359 : Nat := 118140960795 + 7319359 * 2 ^ 59
def prefixEnd_7319359 : Nat := 4983230072969 + 3 ^ 40 * 7319359 * 2
def baseEnd_7319359 : Nat := 417594361090214856439043

theorem tailTrace_7319359 : CollatzResearch.WordTrace tailWord_7319359 prefixEnd_7319359 417594361090214856439043 := by
  unfold tailWord_7319359
  simp only [CollatzResearch.WordTrace]
  refine ⟨266958954290219864840985131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177972636193479909893990087 266958954290219864840985131)
  ·
    refine ⟨400438431435329797261477697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266958954290219864840985131 400438431435329797261477697)
    ·
      refine ⟨300328823576497347946108273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400438431435329797261477697 300328823576497347946108273)
      ·
        refine ⟨225246617682373010959581205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300328823576497347946108273 225246617682373010959581205)
        ·
          refine ⟨10558435203861234888730369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 225246617682373010959581205 10558435203861234888730369)
          ·
            refine ⟨7918826402895926166547777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10558435203861234888730369 7918826402895926166547777)
            ·
              refine ⟨5939119802171944624910833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7918826402895926166547777 5939119802171944624910833)
              ·
                refine ⟨4454339851628958468683125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5939119802171944624910833 4454339851628958468683125)
                ·
                  refine ⟨417594361090214856439043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4454339851628958468683125 417594361090214856439043)
                  ·
                    rfl

theorem cell23_7319359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 5].length) (baseStart_7319359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319359 prefixEnd_7319359 := by exact prefixLift 7319359
  have htrace : WordTrace (prefixWord ++ tailWord_7319359) baseStart_7319359 baseEnd_7319359 := by
    simpa [prefixWord, tailWord_7319359, baseEnd_7319359] using wordTrace_append hprefix tailTrace_7319359
  have hstable : (prefixWord ++ tailWord_7319359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319359).length < 2 ^ (prefixWord ++ tailWord_7319359).sum := by decide
  have hdescent : baseEnd_7319359 < baseStart_7319359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319385 : List Nat := [1, 2, 1, 2, 2, 3, 3, 2, 3, 4]
def baseStart_7319385 : Nat := 118140960795 + 7319385 * 2 ^ 59
def prefixEnd_7319385 : Nat := 4983230072969 + 3 ^ 40 * 7319385 * 2
def baseEnd_7319385 : Nat := 1252787533436316868742089

theorem tailTrace_7319385 : CollatzResearch.WordTrace tailWord_7319385 prefixEnd_7319385 1252787533436316868742089 := by
  unfold tailWord_7319385
  simp only [CollatzResearch.WordTrace]
  refine ⟨266959902588125671281431609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177973268392083780854287739 266959902588125671281431609)
  ·
    refine ⟨200219926941094253461073707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266959902588125671281431609 200219926941094253461073707)
    ·
      refine ⟨300329890411641380191610561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200219926941094253461073707 300329890411641380191610561)
      ·
        refine ⟨225247417808731035143707921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300329890411641380191610561 225247417808731035143707921)
        ·
          refine ⟨168935563356548276357780941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225247417808731035143707921 168935563356548276357780941)
          ·
            refine ⟨63350836258705603634167853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168935563356548276357780941 63350836258705603634167853)
            ·
              refine ⟨23756563597014601362812945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63350836258705603634167853 23756563597014601362812945)
              ·
                refine ⟨17817422697760951022109709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23756563597014601362812945 17817422697760951022109709)
                ·
                  refine ⟨6681533511660356633291141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17817422697760951022109709 6681533511660356633291141)
                  ·
                    refine ⟨1252787533436316868742089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6681533511660356633291141 1252787533436316868742089)
                    ·
                      rfl

theorem cell23_7319385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 4].length) (baseStart_7319385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319385 prefixEnd_7319385 := by exact prefixLift 7319385
  have htrace : WordTrace (prefixWord ++ tailWord_7319385) baseStart_7319385 baseEnd_7319385 := by
    simpa [prefixWord, tailWord_7319385, baseEnd_7319385] using wordTrace_append hprefix tailTrace_7319385
  have hstable : (prefixWord ++ tailWord_7319385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319385).length < 2 ^ (prefixWord ++ tailWord_7319385).sum := by decide
  have hdescent : baseEnd_7319385 < baseStart_7319385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319392 : List Nat := [2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 4]
def baseStart_7319392 : Nat := 118140960795 + 7319392 * 2 ^ 59
def prefixEnd_7319392 : Nat := 4983230072969 + 3 ^ 40 * 7319392 * 2
def baseEnd_7319392 : Nat := 3758366194673532078838735

theorem tailTrace_7319392 : CollatzResearch.WordTrace tailWord_7319392 prefixEnd_7319392 3758366194673532078838735 := by
  unfold tailWord_7319392
  simp only [CollatzResearch.WordTrace]
  refine ⟨133480078949550155738468215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177973438599400207651290953 133480078949550155738468215)
  ·
    refine ⟨200220118424325233607702323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133480078949550155738468215 200220118424325233607702323)
    ·
      refine ⟨300330177636487850411553485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200220118424325233607702323 300330177636487850411553485)
      ·
        refine ⟨112623816613682943904332557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300330177636487850411553485 112623816613682943904332557)
        ·
          refine ⟨42233931230131103964124709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112623816613682943904332557 42233931230131103964124709)
          ·
            refine ⟨7918862105649581993273383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42233931230131103964124709 7918862105649581993273383)
            ·
              refine ⟨11878293158474372989910075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7918862105649581993273383 11878293158474372989910075)
              ·
                refine ⟨17817439737711559484865113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11878293158474372989910075 17817439737711559484865113)
                ·
                  refine ⟨13363079803283669613648835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17817439737711559484865113 13363079803283669613648835)
                  ·
                    refine ⟨20044619704925504420473253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13363079803283669613648835 20044619704925504420473253)
                    ·
                      refine ⟨3758366194673532078838735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20044619704925504420473253 3758366194673532078838735)
                      ·
                        rfl

theorem cell23_7319392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_7319392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319392 prefixEnd_7319392 := by exact prefixLift 7319392
  have htrace : WordTrace (prefixWord ++ tailWord_7319392) baseStart_7319392 baseEnd_7319392 := by
    simpa [prefixWord, tailWord_7319392, baseEnd_7319392] using wordTrace_append hprefix tailTrace_7319392
  have hstable : (prefixWord ++ tailWord_7319392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319392).length < 2 ^ (prefixWord ++ tailWord_7319392).sum := by decide
  have hdescent : baseEnd_7319392 < baseStart_7319392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319418 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6]
def baseStart_7319418 : Nat := 118140960795 + 7319418 * 2 ^ 59
def prefixEnd_7319418 : Nat := 4983230072969 + 3 ^ 40 * 7319418 * 2
def baseEnd_7319418 : Nat := 3758379545170548977113615

theorem tailTrace_7319418 : CollatzResearch.WordTrace tailWord_7319418 prefixEnd_7319418 3758379545170548977113615 := by
  unfold tailWord_7319418
  simp only [CollatzResearch.WordTrace]
  refine ⟨66740276549251529479345727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177974070798004078611588605 66740276549251529479345727)
  ·
    refine ⟨100110414823877294219018591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66740276549251529479345727 100110414823877294219018591)
    ·
      refine ⟨150165622235815941328527887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100110414823877294219018591 150165622235815941328527887)
      ·
        refine ⟨225248433353723911992791831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150165622235815941328527887 225248433353723911992791831)
        ·
          refine ⟨337872650030585867989187747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225248433353723911992791831 337872650030585867989187747)
          ·
            refine ⟨506808975045878801983781621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337872650030585867989187747 506808975045878801983781621)
            ·
              refine ⟨47513341410551137685979527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 506808975045878801983781621 47513341410551137685979527)
              ·
                refine ⟨71270012115826706528969291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47513341410551137685979527 71270012115826706528969291)
                ·
                  refine ⟨106905018173740059793453937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71270012115826706528969291 106905018173740059793453937)
                  ·
                    refine ⟨80178763630305044845090453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106905018173740059793453937 80178763630305044845090453)
                    ·
                      refine ⟨3758379545170548977113615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80178763630305044845090453 3758379545170548977113615)
                      ·
                        rfl

theorem cell23_7319418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_7319418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319418 prefixEnd_7319418 := by exact prefixLift 7319418
  have htrace : WordTrace (prefixWord ++ tailWord_7319418) baseStart_7319418 baseEnd_7319418 := by
    simpa [prefixWord, tailWord_7319418, baseEnd_7319418] using wordTrace_append hprefix tailTrace_7319418
  have hstable : (prefixWord ++ tailWord_7319418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319418).length < 2 ^ (prefixWord ++ tailWord_7319418).sum := by decide
  have hdescent : baseEnd_7319418 < baseStart_7319418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319470 : List Nat := [4, 1, 5, 1, 2, 1, 1, 1, 3, 4]
def baseStart_7319470 : Nat := 118140960795 + 7319470 * 2 ^ 59
def prefixEnd_7319470 : Nat := 4983230072969 + 3 ^ 40 * 7319470 * 2
def baseEnd_7319470 : Nat := 1252802082054860924554459

theorem tailTrace_7319470 : CollatzResearch.WordTrace tailWord_7319470 prefixEnd_7319470 1252802082054860924554459 := by
  unfold tailWord_7319470
  simp only [CollatzResearch.WordTrace]
  refine ⟨33370375349102216349784483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177975335195211820532183909 33370375349102216349784483)
  ·
    refine ⟨50055563023653324524676725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33370375349102216349784483 50055563023653324524676725)
    ·
      refine ⟨4692709033467499174188443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50055563023653324524676725 4692709033467499174188443)
      ·
        refine ⟨7039063550201248761282665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4692709033467499174188443 7039063550201248761282665)
        ·
          refine ⟨5279297662650936570961999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7039063550201248761282665 5279297662650936570961999)
          ·
            refine ⟨7918946493976404856442999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5279297662650936570961999 7918946493976404856442999)
            ·
              refine ⟨11878419740964607284664499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7918946493976404856442999 11878419740964607284664499)
              ·
                refine ⟨17817629611446910926996749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11878419740964607284664499 17817629611446910926996749)
                ·
                  refine ⟨6681611104292591597623781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17817629611446910926996749 6681611104292591597623781)
                  ·
                    refine ⟨1252802082054860924554459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6681611104292591597623781 1252802082054860924554459)
                    ·
                      rfl

theorem cell23_7319470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_7319470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319470 prefixEnd_7319470 := by exact prefixLift 7319470
  have htrace : WordTrace (prefixWord ++ tailWord_7319470) baseStart_7319470 baseEnd_7319470 := by
    simpa [prefixWord, tailWord_7319470, baseEnd_7319470] using wordTrace_append hprefix tailTrace_7319470
  have hstable : (prefixWord ++ tailWord_7319470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319470).length < 2 ^ (prefixWord ++ tailWord_7319470).sum := by decide
  have hdescent : baseEnd_7319470 < baseStart_7319470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319475 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 4, 4]
def baseStart_7319475 : Nat := 118140960795 + 7319475 * 2 ^ 59
def prefixEnd_7319475 : Nat := 4983230072969 + 3 ^ 40 * 7319475 * 2
def baseEnd_7319475 : Nat := 1252802937855951751366951

theorem tailTrace_7319475 : CollatzResearch.WordTrace tailWord_7319475 prefixEnd_7319475 1252802937855951751366951 := by
  unfold tailWord_7319475
  simp only [CollatzResearch.WordTrace]
  refine ⟨266963185157799616652207879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177975456771866411101471919 266963185157799616652207879)
  ·
    refine ⟨400444777736699424978311819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266963185157799616652207879 400444777736699424978311819)
    ·
      refine ⟨600667166605049137467467729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400444777736699424978311819 600667166605049137467467729)
      ·
        refine ⟨450500374953786853100600797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600667166605049137467467729 450500374953786853100600797)
        ·
          refine ⟨168937640607670069912725299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 450500374953786853100600797 168937640607670069912725299)
          ·
            refine ⟨253406460911505104869087949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168937640607670069912725299 253406460911505104869087949)
            ·
              refine ⟨95027422841814414325907981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253406460911505104869087949 95027422841814414325907981)
              ·
                refine ⟨35635283565680405372215493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95027422841814414325907981 35635283565680405372215493)
                ·
                  refine ⟨6681615668565076007290405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35635283565680405372215493 6681615668565076007290405)
                  ·
                    refine ⟨1252802937855951751366951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6681615668565076007290405 1252802937855951751366951)
                    ·
                      rfl

theorem cell23_7319475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 4].length) (baseStart_7319475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319475 prefixEnd_7319475 := by exact prefixLift 7319475
  have htrace : WordTrace (prefixWord ++ tailWord_7319475) baseStart_7319475 baseEnd_7319475 := by
    simpa [prefixWord, tailWord_7319475, baseEnd_7319475] using wordTrace_append hprefix tailTrace_7319475
  have hstable : (prefixWord ++ tailWord_7319475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319475).length < 2 ^ (prefixWord ++ tailWord_7319475).sum := by decide
  have hdescent : baseEnd_7319475 < baseStart_7319475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319495 : List Nat := [1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_7319495 : Nat := 118140960795 + 7319495 * 2 ^ 59
def prefixEnd_7319495 : Nat := 4983230072969 + 3 ^ 40 * 7319495 * 2
def baseEnd_7319495 : Nat := 3758419083180945175850761

theorem tailTrace_7319495 : CollatzResearch.WordTrace tailWord_7319495 prefixEnd_7319495 3758419083180945175850761 := by
  unfold tailWord_7319495
  simp only [CollatzResearch.WordTrace]
  refine ⟨266963914617727160067935939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177975943078484773378623959 266963914617727160067935939)
  ·
    refine ⟨400445871926590740101903909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266963914617727160067935939 400445871926590740101903909)
    ·
      refine ⟨75083600986235763769106983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 400445871926590740101903909 75083600986235763769106983)
      ·
        refine ⟨112625401479353645653660475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75083600986235763769106983 112625401479353645653660475)
        ·
          refine ⟨168938102219030468480490713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112625401479353645653660475 168938102219030468480490713)
          ·
            refine ⟨126703576664272851360368035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168938102219030468480490713 126703576664272851360368035)
            ·
              refine ⟨190055364996409277040552053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126703576664272851360368035 190055364996409277040552053)
              ·
                refine ⟨17817690468413369722551755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190055364996409277040552053 17817690468413369722551755)
                ·
                  refine ⟨26726535702620054583827633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17817690468413369722551755 26726535702620054583827633)
                  ·
                    refine ⟨20044901776965040937870725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26726535702620054583827633 20044901776965040937870725)
                    ·
                      refine ⟨3758419083180945175850761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20044901776965040937870725 3758419083180945175850761)
                      ·
                        rfl

theorem cell23_7319495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_7319495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319495 prefixEnd_7319495 := by exact prefixLift 7319495
  have htrace : WordTrace (prefixWord ++ tailWord_7319495) baseStart_7319495 baseEnd_7319495 := by
    simpa [prefixWord, tailWord_7319495, baseEnd_7319495] using wordTrace_append hprefix tailTrace_7319495
  have hstable : (prefixWord ++ tailWord_7319495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319495).length < 2 ^ (prefixWord ++ tailWord_7319495).sum := by decide
  have hdescent : baseEnd_7319495 < baseStart_7319495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319502 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3]
def baseStart_7319502 : Nat := 118140960795 + 7319502 * 2 ^ 59
def prefixEnd_7319502 : Nat := 4983230072969 + 3 ^ 40 * 7319502 * 2
def baseEnd_7319502 : Nat := 3758422677545526648463229

theorem tailTrace_7319502 : CollatzResearch.WordTrace tailWord_7319502 prefixEnd_7319502 3758422677545526648463229 := by
  unfold tailWord_7319502
  simp only [CollatzResearch.WordTrace]
  refine ⟨33370521241087725032930095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177976113285801200175627173 33370521241087725032930095)
  ·
    refine ⟨50055781861631587549395143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33370521241087725032930095 50055781861631587549395143)
    ·
      refine ⟨75083672792447381324092715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50055781861631587549395143 75083672792447381324092715)
      ·
        refine ⟨112625509188671071986139073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75083672792447381324092715 112625509188671071986139073)
        ·
          refine ⟨84469131891503303989604305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112625509188671071986139073 84469131891503303989604305)
          ·
            refine ⟨63351848918627477992203229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84469131891503303989604305 63351848918627477992203229)
            ·
              refine ⟨23756943344485304247076211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63351848918627477992203229 23756943344485304247076211)
              ·
                refine ⟨35635415016727956370614317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23756943344485304247076211 35635415016727956370614317)
                ·
                  refine ⟨13363280631272983638980369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35635415016727956370614317 13363280631272983638980369)
                  ·
                    refine ⟨10022460473454737729235277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13363280631272983638980369 10022460473454737729235277)
                    ·
                      refine ⟨3758422677545526648463229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10022460473454737729235277 3758422677545526648463229)
                      ·
                        rfl

theorem cell23_7319502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_7319502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319502 prefixEnd_7319502 := by exact prefixLift 7319502
  have htrace : WordTrace (prefixWord ++ tailWord_7319502) baseStart_7319502 baseEnd_7319502 := by
    simpa [prefixWord, tailWord_7319502, baseEnd_7319502] using wordTrace_append hprefix tailTrace_7319502
  have hstable : (prefixWord ++ tailWord_7319502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319502).length < 2 ^ (prefixWord ++ tailWord_7319502).sum := by decide
  have hdescent : baseEnd_7319502 < baseStart_7319502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319522 : List Nat := [3, 3, 3, 1, 2, 11]
def baseStart_7319522 : Nat := 118140960795 + 7319522 * 2 ^ 59
def prefixEnd_7319522 : Nat := 4983230072969 + 3 ^ 40 * 7319522 * 2
def baseEnd_7319522 : Nat := 15466802251681549671659

theorem tailTrace_7319522 : CollatzResearch.WordTrace tailWord_7319522 prefixEnd_7319522 15466802251681549671659 := by
  unfold tailWord_7319522
  simp only [CollatzResearch.WordTrace]
  refine ⟨66741224847157335919792205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177976599592419562452779213 66741224847157335919792205)
  ·
    refine ⟨25027959317684000969922077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66741224847157335919792205 25027959317684000969922077)
    ·
      refine ⟨9385484744131500363720779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25027959317684000969922077 9385484744131500363720779)
      ·
        refine ⟨14078227116197250545581169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9385484744131500363720779 14078227116197250545581169)
        ·
          refine ⟨10558670337147937909185877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14078227116197250545581169 10558670337147937909185877)
          ·
            refine ⟨15466802251681549671659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10558670337147937909185877 15466802251681549671659)
            ·
              rfl

theorem cell23_7319522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 11].length) (baseStart_7319522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319522 prefixEnd_7319522 := by exact prefixLift 7319522
  have htrace : WordTrace (prefixWord ++ tailWord_7319522) baseStart_7319522 baseEnd_7319522 := by
    simpa [prefixWord, tailWord_7319522, baseEnd_7319522] using wordTrace_append hprefix tailTrace_7319522
  have hstable : (prefixWord ++ tailWord_7319522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319522).length < 2 ^ (prefixWord ++ tailWord_7319522).sum := by decide
  have hdescent : baseEnd_7319522 < baseStart_7319522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319532 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 3]
def baseStart_7319532 : Nat := 118140960795 + 7319532 * 2 ^ 59
def prefixEnd_7319532 : Nat := 4983230072969 + 3 ^ 40 * 7319532 * 2
def baseEnd_7319532 : Nat := 3758438081965161531088091

theorem tailTrace_7319532 : CollatzResearch.WordTrace tailWord_7319532 prefixEnd_7319532 3758438081965161531088091 := by
  unfold tailWord_7319532
  simp only [CollatzResearch.WordTrace]
  refine ⟨133482632059296557693516425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177976842745728743591355233 133482632059296557693516425)
  ·
    refine ⟨100111974044472418270137319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133482632059296557693516425 100111974044472418270137319)
    ·
      refine ⟨150167961066708627405205979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100111974044472418270137319 150167961066708627405205979)
      ·
        refine ⟨225251941600062941107808969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150167961066708627405205979 225251941600062941107808969)
        ·
          refine ⟨168938956200047205830856727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225251941600062941107808969 168938956200047205830856727)
          ·
            refine ⟨253408434300070808746285091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168938956200047205830856727 253408434300070808746285091)
            ·
              refine ⟨380112651450106213119427637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253408434300070808746285091 380112651450106213119427637)
              ·
                refine ⟨35635561073447457479946341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 380112651450106213119427637 35635561073447457479946341)
                ·
                  refine ⟨6681667701271398277489939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35635561073447457479946341 6681667701271398277489939)
                  ·
                    refine ⟨10022501551907097416234909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6681667701271398277489939 10022501551907097416234909)
                    ·
                      refine ⟨3758438081965161531088091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10022501551907097416234909 3758438081965161531088091)
                      ·
                        rfl

theorem cell23_7319532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 3].length) (baseStart_7319532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319532 prefixEnd_7319532 := by exact prefixLift 7319532
  have htrace : WordTrace (prefixWord ++ tailWord_7319532) baseStart_7319532 baseEnd_7319532 := by
    simpa [prefixWord, tailWord_7319532, baseEnd_7319532] using wordTrace_append hprefix tailTrace_7319532
  have hstable : (prefixWord ++ tailWord_7319532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319532).length < 2 ^ (prefixWord ++ tailWord_7319532).sum := by decide
  have hdescent : baseEnd_7319532 < baseStart_7319532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319549 : List Nat := [1, 4, 1, 1, 1, 2, 4, 3, 2, 1, 3]
def baseStart_7319549 : Nat := 118140960795 + 7319549 * 2 ^ 59
def prefixEnd_7319549 : Nat := 4983230072969 + 3 ^ 40 * 7319549 * 2
def baseEnd_7319549 : Nat := 3758446811136287964575513

theorem tailTrace_7319549 : CollatzResearch.WordTrace tailWord_7319549 prefixEnd_7319549 3758446811136287964575513 := by
  unfold tailWord_7319549
  simp only [CollatzResearch.WordTrace]
  refine ⟨266965884159531527290401701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177977256106354351526934467 266965884159531527290401701)
  ·
    refine ⟨50056103279912161366950319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266965884159531527290401701 50056103279912161366950319)
    ·
      refine ⟨75084154919868242050425479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50056103279912161366950319 75084154919868242050425479)
      ·
        refine ⟨112626232379802363075638219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75084154919868242050425479 112626232379802363075638219)
        ·
          refine ⟨168939348569703544613457329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112626232379802363075638219 168939348569703544613457329)
          ·
            refine ⟨126704511427277658460092997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168939348569703544613457329 126704511427277658460092997)
            ·
              refine ⟨23757095892614560961267437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126704511427277658460092997 23757095892614560961267437)
              ·
                refine ⟨8908910959730460360475289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23757095892614560961267437 8908910959730460360475289)
                ·
                  refine ⟨6681683219797845270356467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8908910959730460360475289 6681683219797845270356467)
                  ·
                    refine ⟨10022524829696767905534701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6681683219797845270356467 10022524829696767905534701)
                    ·
                      refine ⟨3758446811136287964575513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10022524829696767905534701 3758446811136287964575513)
                      ·
                        rfl

theorem cell23_7319549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_7319549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319549 prefixEnd_7319549 := by exact prefixLift 7319549
  have htrace : WordTrace (prefixWord ++ tailWord_7319549) baseStart_7319549 baseEnd_7319549 := by
    simpa [prefixWord, tailWord_7319549, baseEnd_7319549] using wordTrace_append hprefix tailTrace_7319549
  have hstable : (prefixWord ++ tailWord_7319549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319549).length < 2 ^ (prefixWord ++ tailWord_7319549).sum := by decide
  have hdescent : baseEnd_7319549 < baseStart_7319549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319559 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 3, 3, 2]
def baseStart_7319559 : Nat := 118140960795 + 7319559 * 2 ^ 59
def prefixEnd_7319559 : Nat := 4983230072969 + 3 ^ 40 * 7319559 * 2
def baseEnd_7319559 : Nat := 3758451945942832925450467

theorem tailTrace_7319559 : CollatzResearch.WordTrace tailWord_7319559 prefixEnd_7319559 3758451945942832925450467 := by
  unfold tailWord_7319559
  simp only [CollatzResearch.WordTrace]
  refine ⟨266966248889495298998265731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177977499259663532665510487 266966248889495298998265731)
  ·
    refine ⟨400449373334242948497398597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266966248889495298998265731 400449373334242948497398597)
    ·
      refine ⟨75084257500170552843262237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 400449373334242948497398597 75084257500170552843262237)
      ·
        refine ⟨28156596562563957316223339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75084257500170552843262237 28156596562563957316223339)
        ·
          refine ⟨42234894843845935974335009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28156596562563957316223339 42234894843845935974335009)
          ·
            refine ⟨31676171132884451980751257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42234894843845935974335009 31676171132884451980751257)
            ·
              refine ⟨23757128349663338985563443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31676171132884451980751257 23757128349663338985563443)
              ·
                refine ⟨35635692524495008478345165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23757128349663338985563443 35635692524495008478345165)
                ·
                  refine ⟨13363384696685628179379437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35635692524495008478345165 13363384696685628179379437)
                  ·
                    refine ⟨5011269261257110567267289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13363384696685628179379437 5011269261257110567267289)
                    ·
                      refine ⟨3758451945942832925450467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5011269261257110567267289 3758451945942832925450467)
                      ·
                        rfl

theorem cell23_7319559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_7319559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319559 prefixEnd_7319559 := by exact prefixLift 7319559
  have htrace : WordTrace (prefixWord ++ tailWord_7319559) baseStart_7319559 baseEnd_7319559 := by
    simpa [prefixWord, tailWord_7319559, baseEnd_7319559] using wordTrace_append hprefix tailTrace_7319559
  have hstable : (prefixWord ++ tailWord_7319559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319559).length < 2 ^ (prefixWord ++ tailWord_7319559).sum := by decide
  have hdescent : baseEnd_7319559 < baseStart_7319559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319602 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_7319602 : Nat := 118140960795 + 7319602 * 2 ^ 59
def prefixEnd_7319602 : Nat := 4983230072969 + 3 ^ 40 * 7319602 * 2
def baseEnd_7319602 : Nat := 3758474025610976257212769

theorem tailTrace_7319602 : CollatzResearch.WordTrace tailWord_7319602 prefixEnd_7319602 3758474025610976257212769 := by
  unfold tailWord_7319602
  simp only [CollatzResearch.WordTrace]
  refine ⟨66741954307084879335520265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177978544818893011561387373 66741954307084879335520265)
  ·
    refine ⟨50056465730313659501640199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66741954307084879335520265 50056465730313659501640199)
    ·
      refine ⟨75084698595470489252460299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50056465730313659501640199 75084698595470489252460299)
      ·
        refine ⟨112627047893205733878690449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75084698595470489252460299 112627047893205733878690449)
        ·
          refine ⟨84470285919904300409017837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112627047893205733878690449 84470285919904300409017837)
          ·
            refine ⟨31676357219964112653381689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84470285919904300409017837 31676357219964112653381689)
            ·
              refine ⟨23757267914973084490036267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31676357219964112653381689 23757267914973084490036267)
              ·
                refine ⟨35635901872459626735054401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23757267914973084490036267 35635901872459626735054401)
                ·
                  refine ⟨26726926404344720051290801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35635901872459626735054401 26726926404344720051290801)
                  ·
                    refine ⟨20045194803258540038468101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26726926404344720051290801 20045194803258540038468101)
                    ·
                      refine ⟨3758474025610976257212769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20045194803258540038468101 3758474025610976257212769)
                      ·
                        rfl

theorem cell23_7319602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_7319602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319602 prefixEnd_7319602 := by exact prefixLift 7319602
  have htrace : WordTrace (prefixWord ++ tailWord_7319602) baseStart_7319602 baseEnd_7319602 := by
    simpa [prefixWord, tailWord_7319602, baseEnd_7319602] using wordTrace_append hprefix tailTrace_7319602
  have hstable : (prefixWord ++ tailWord_7319602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319602).length < 2 ^ (prefixWord ++ tailWord_7319602).sum := by decide
  have hdescent : baseEnd_7319602 < baseStart_7319602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319625 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 1, 7]
def baseStart_7319625 : Nat := 118140960795 + 7319625 * 2 ^ 59
def prefixEnd_7319625 : Nat := 4983230072969 + 3 ^ 40 * 7319625 * 2
def baseEnd_7319625 : Nat := 1252828611888676555741721

theorem tailTrace_7319625 : CollatzResearch.WordTrace tailWord_7319625 prefixEnd_7319625 1252828611888676555741721 := by
  unfold tailWord_7319625
  simp only [CollatzResearch.WordTrace]
  refine ⟨266968656107256192270168329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177979104071504128180112219 266968656107256192270168329)
  ·
    refine ⟨200226492080442144202626247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266968656107256192270168329 200226492080442144202626247)
    ·
      refine ⟨300339738120663216303939371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200226492080442144202626247 300339738120663216303939371)
      ·
        refine ⟨450509607180994824455909057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300339738120663216303939371 450509607180994824455909057)
        ·
          refine ⟨337882205385746118341931793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450509607180994824455909057 337882205385746118341931793)
          ·
            refine ⟨253411654039309588756448845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337882205385746118341931793 253411654039309588756448845)
            ·
              refine ⟨95029370264741095783668317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253411654039309588756448845 95029370264741095783668317)
              ·
                refine ⟨35636013849277910918875619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95029370264741095783668317 35636013849277910918875619)
                ·
                  refine ⟨53454020773916866378313429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35636013849277910918875619 53454020773916866378313429)
                  ·
                    refine ⟨1252828611888676555741721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53454020773916866378313429 1252828611888676555741721)
                    ·
                      rfl

theorem cell23_7319625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 7].length) (baseStart_7319625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319625 prefixEnd_7319625 := by exact prefixLift 7319625
  have htrace : WordTrace (prefixWord ++ tailWord_7319625) baseStart_7319625 baseEnd_7319625 := by
    simpa [prefixWord, tailWord_7319625, baseEnd_7319625] using wordTrace_append hprefix tailTrace_7319625
  have hstable : (prefixWord ++ tailWord_7319625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319625).length < 2 ^ (prefixWord ++ tailWord_7319625).sum := by decide
  have hdescent : baseEnd_7319625 < baseStart_7319625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319632 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 3, 7, 2]
def baseStart_7319632 : Nat := 118140960795 + 7319632 * 2 ^ 59
def prefixEnd_7319632 : Nat := 4983230072969 + 3 ^ 40 * 7319632 * 2
def baseEnd_7319632 : Nat := 3758489430030611139837631

theorem tailTrace_7319632 : CollatzResearch.WordTrace tailWord_7319632 prefixEnd_7319632 3758489430030611139837631 := by
  unfold tailWord_7319632
  simp only [CollatzResearch.WordTrace]
  refine ⟨133484455709115416232836575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177979274278820554977115433 133484455709115416232836575)
  ·
    refine ⟨200226683563673124349254863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133484455709115416232836575 200226683563673124349254863)
    ·
      refine ⟨300340025345509686523882295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200226683563673124349254863 300340025345509686523882295)
      ·
        refine ⟨450510038018264529785823443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300340025345509686523882295 450510038018264529785823443)
        ·
          refine ⟨675765057027396794678735165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450510038018264529785823443 675765057027396794678735165)
          ·
            refine ⟨253411896385273798004525687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 675765057027396794678735165 253411896385273798004525687)
            ·
              refine ⟨380117844577910697006788531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253411896385273798004525687 380117844577910697006788531)
              ·
                refine ⟨570176766866866045510182797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380117844577910697006788531 570176766866866045510182797)
                ·
                  refine ⟨213816287575074767066318549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570176766866866045510182797 213816287575074767066318549)
                  ·
                    refine ⟨5011319240040814853116841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 213816287575074767066318549 5011319240040814853116841)
                    ·
                      refine ⟨3758489430030611139837631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5011319240040814853116841 3758489430030611139837631)
                      ·
                        rfl

theorem cell23_7319632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 7, 2].length) (baseStart_7319632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319632 prefixEnd_7319632 := by exact prefixLift 7319632
  have htrace : WordTrace (prefixWord ++ tailWord_7319632) baseStart_7319632 baseEnd_7319632 := by
    simpa [prefixWord, tailWord_7319632, baseEnd_7319632] using wordTrace_append hprefix tailTrace_7319632
  have hstable : (prefixWord ++ tailWord_7319632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319632).length < 2 ^ (prefixWord ++ tailWord_7319632).sum := by decide
  have hdescent : baseEnd_7319632 < baseStart_7319632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319642 : List Nat := [3, 1, 1, 2, 1, 1, 5, 2, 2, 5]
def baseStart_7319642 : Nat := 118140960795 + 7319642 * 2 ^ 59
def prefixEnd_7319642 : Nat := 4983230072969 + 3 ^ 40 * 7319642 * 2
def baseEnd_7319642 : Nat := 1252831521612385366904195

theorem tailTrace_7319642 : CollatzResearch.WordTrace tailWord_7319642 prefixEnd_7319642 1252831521612385366904195 := by
  unfold tailWord_7319642
  simp only [CollatzResearch.WordTrace]
  refine ⟨66742319037048651043384295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177979517432129736115691453 66742319037048651043384295)
  ·
    refine ⟨100113478555572976565076443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66742319037048651043384295 100113478555572976565076443)
    ·
      refine ⟨150170217833359464847614665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100113478555572976565076443 150170217833359464847614665)
      ·
        refine ⟨112627663375019598635710999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150170217833359464847614665 112627663375019598635710999)
        ·
          refine ⟨168941495062529397953566499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112627663375019598635710999 168941495062529397953566499)
          ·
            refine ⟨253412242593794096930349749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168941495062529397953566499 253412242593794096930349749)
            ·
              refine ⟨23757397743168196587220289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253412242593794096930349749 23757397743168196587220289)
              ·
                refine ⟨17818048307376147440415217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23757397743168196587220289 17818048307376147440415217)
                ·
                  refine ⟨13363536230532110580311413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17818048307376147440415217 13363536230532110580311413)
                  ·
                    refine ⟨1252831521612385366904195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13363536230532110580311413 1252831521612385366904195)
                    ·
                      rfl

theorem cell23_7319642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_7319642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319642 prefixEnd_7319642 := by exact prefixLift 7319642
  have htrace : WordTrace (prefixWord ++ tailWord_7319642) baseStart_7319642 baseEnd_7319642 := by
    simpa [prefixWord, tailWord_7319642, baseEnd_7319642] using wordTrace_append hprefix tailTrace_7319642
  have hstable : (prefixWord ++ tailWord_7319642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319642).length < 2 ^ (prefixWord ++ tailWord_7319642).sum := by decide
  have hdescent : baseEnd_7319642 < baseStart_7319642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319672 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 5, 4]
def baseStart_7319672 : Nat := 118140960795 + 7319672 * 2 ^ 59
def prefixEnd_7319672 : Nat := 4983230072969 + 3 ^ 40 * 7319672 * 2
def baseEnd_7319672 : Nat := 1252836656418930327779149

theorem tailTrace_7319672 : CollatzResearch.WordTrace tailWord_7319672 prefixEnd_7319672 1252836656418930327779149 := by
  unfold tailWord_7319672
  simp only [CollatzResearch.WordTrace]
  refine ⟨133485185169042959648564635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177980246892057279531419513 133485185169042959648564635)
  ·
    refine ⟨200227777753564439472846953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133485185169042959648564635 200227777753564439472846953)
    ·
      refine ⟨150170833315173329604635215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200227777753564439472846953 150170833315173329604635215)
      ·
        refine ⟨225256249972759994406952823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150170833315173329604635215 225256249972759994406952823)
        ·
          refine ⟨337884374959139991610429235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225256249972759994406952823 337884374959139991610429235)
          ·
            refine ⟨506826562438709987415643853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337884374959139991610429235 506826562438709987415643853)
            ·
              refine ⟨190059960914516245280866445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506826562438709987415643853 190059960914516245280866445)
              ·
                refine ⟨71272485342943591980324917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190059960914516245280866445 71272485342943591980324917)
                ·
                  refine ⟨6681795500900961748155461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71272485342943591980324917 6681795500900961748155461)
                  ·
                    refine ⟨1252836656418930327779149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6681795500900961748155461 1252836656418930327779149)
                    ·
                      rfl

theorem cell23_7319672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_7319672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319672 prefixEnd_7319672 := by exact prefixLift 7319672
  have htrace : WordTrace (prefixWord ++ tailWord_7319672) baseStart_7319672 baseEnd_7319672 := by
    simpa [prefixWord, tailWord_7319672, baseEnd_7319672] using wordTrace_append hprefix tailTrace_7319672
  have hstable : (prefixWord ++ tailWord_7319672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319672).length < 2 ^ (prefixWord ++ tailWord_7319672).sum := by decide
  have hdescent : baseEnd_7319672 < baseStart_7319672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319675 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 6]
def baseStart_7319675 : Nat := 118140960795 + 7319675 * 2 ^ 59
def prefixEnd_7319675 : Nat := 4983230072969 + 3 ^ 40 * 7319675 * 2
def baseEnd_7319675 : Nat := 3758511509698754471599933

theorem tailTrace_7319675 : CollatzResearch.WordTrace tailWord_7319675 prefixEnd_7319675 3758511509698754471599933 := by
  unfold tailWord_7319675
  simp only [CollatzResearch.WordTrace]
  refine ⟨266970479757075050809488479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177980319838050033872992319 266970479757075050809488479)
  ·
    refine ⟨400455719635612576214232719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266970479757075050809488479 400455719635612576214232719)
    ·
      refine ⟨600683579453418864321349079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400455719635612576214232719 600683579453418864321349079)
      ·
        refine ⟨901025369180128296482023619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600683579453418864321349079 901025369180128296482023619)
        ·
          refine ⟨1351538053770192444723035429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901025369180128296482023619 1351538053770192444723035429)
          ·
            refine ⟨253413385081911083385569143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1351538053770192444723035429 253413385081911083385569143)
            ·
              refine ⟨380120077622866625078353715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253413385081911083385569143 380120077622866625078353715)
              ·
                refine ⟨570180116434299937617530573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380120077622866625078353715 570180116434299937617530573)
                ·
                  refine ⟨213817543662862476606573965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570180116434299937617530573 213817543662862476606573965)
                  ·
                    refine ⟨80181578873573428727465237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213817543662862476606573965 80181578873573428727465237)
                    ·
                      refine ⟨3758511509698754471599933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80181578873573428727465237 3758511509698754471599933)
                      ·
                        rfl

theorem cell23_7319675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 6].length) (baseStart_7319675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319675 prefixEnd_7319675 := by exact prefixLift 7319675
  have htrace : WordTrace (prefixWord ++ tailWord_7319675) baseStart_7319675 baseEnd_7319675 := by
    simpa [prefixWord, tailWord_7319675, baseEnd_7319675] using wordTrace_append hprefix tailTrace_7319675
  have hstable : (prefixWord ++ tailWord_7319675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319675).length < 2 ^ (prefixWord ++ tailWord_7319675).sum := by decide
  have hdescent : baseEnd_7319675 < baseStart_7319675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319695 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 9]
def baseStart_7319695 : Nat := 118140960795 + 7319695 * 2 ^ 59
def prefixEnd_7319695 : Nat := 4983230072969 + 3 ^ 40 * 7319695 * 2
def baseEnd_7319695 : Nat := 3758521779311844393349841

theorem tailTrace_7319695 : CollatzResearch.WordTrace tailWord_7319695 prefixEnd_7319695 3758521779311844393349841 := by
  unfold tailWord_7319695
  simp only [CollatzResearch.WordTrace]
  refine ⟨266971209217002594225216539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177980806144668396150144359 266971209217002594225216539)
  ·
    refine ⟨400456813825503891337824809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266971209217002594225216539 400456813825503891337824809)
    ·
      refine ⟨300342610369127918503368607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400456813825503891337824809 300342610369127918503368607)
      ·
        refine ⟨450513915553691877755052911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300342610369127918503368607 450513915553691877755052911)
        ·
          refine ⟨675770873330537816632579367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450513915553691877755052911 675770873330537816632579367)
          ·
            refine ⟨1013656309995806724948869051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675770873330537816632579367 1013656309995806724948869051)
            ·
              refine ⟨1520484464993710087423303577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013656309995806724948869051 1520484464993710087423303577)
              ·
                refine ⟨1140363348745282565567477683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1520484464993710087423303577 1140363348745282565567477683)
                ·
                  refine ⟨1710545023117923848351216525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140363348745282565567477683 1710545023117923848351216525)
                  ·
                    refine ⟨641454383669221443131706197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1710545023117923848351216525 641454383669221443131706197)
                    ·
                      refine ⟨3758521779311844393349841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 641454383669221443131706197 3758521779311844393349841)
                      ·
                        rfl

theorem cell23_7319695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_7319695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319695 prefixEnd_7319695 := by exact prefixLift 7319695
  have htrace : WordTrace (prefixWord ++ tailWord_7319695) baseStart_7319695 baseEnd_7319695 := by
    simpa [prefixWord, tailWord_7319695, baseEnd_7319695] using wordTrace_append hprefix tailTrace_7319695
  have hstable : (prefixWord ++ tailWord_7319695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319695).length < 2 ^ (prefixWord ++ tailWord_7319695).sum := by decide
  have hdescent : baseEnd_7319695 < baseStart_7319695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319739 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 1, 5, 2]
def baseStart_7319739 : Nat := 118140960795 + 7319739 * 2 ^ 59
def prefixEnd_7319739 : Nat := 4983230072969 + 3 ^ 40 * 7319739 * 2
def baseEnd_7319739 : Nat := 3758544372460642221199639

theorem tailTrace_7319739 : CollatzResearch.WordTrace tailWord_7319739 prefixEnd_7319739 3758544372460642221199639 := by
  unfold tailWord_7319739
  simp only [CollatzResearch.WordTrace]
  refine ⟨266972814028843189739818271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177981876019228793159878847 266972814028843189739818271)
  ·
    refine ⟨400459221043264784609727407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266972814028843189739818271 400459221043264784609727407)
    ·
      refine ⟨600688831564897176914591111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400459221043264784609727407 600688831564897176914591111)
      ·
        refine ⟨901033247347345765371886667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600688831564897176914591111 901033247347345765371886667)
        ·
          refine ⟨1351549871021018648057830001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901033247347345765371886667 1351549871021018648057830001)
          ·
            refine ⟨1013662403265763986043372501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1351549871021018648057830001 1013662403265763986043372501)
            ·
              refine ⟨23757712576541343422891543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1013662403265763986043372501 23757712576541343422891543)
              ·
                refine ⟨35636568864812015134337315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23757712576541343422891543 35636568864812015134337315)
                ·
                  refine ⟨53454853297218022701505973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35636568864812015134337315 53454853297218022701505973)
                  ·
                    refine ⟨5011392496614189628266185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53454853297218022701505973 5011392496614189628266185)
                    ·
                      refine ⟨3758544372460642221199639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5011392496614189628266185 3758544372460642221199639)
                      ·
                        rfl

theorem cell23_7319739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 5, 2].length) (baseStart_7319739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319739 prefixEnd_7319739 := by exact prefixLift 7319739
  have htrace : WordTrace (prefixWord ++ tailWord_7319739) baseStart_7319739 baseEnd_7319739 := by
    simpa [prefixWord, tailWord_7319739, baseEnd_7319739] using wordTrace_append hprefix tailTrace_7319739
  have hstable : (prefixWord ++ tailWord_7319739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319739).length < 2 ^ (prefixWord ++ tailWord_7319739).sum := by decide
  have hdescent : baseEnd_7319739 < baseStart_7319739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319786 : List Nat := [3, 1, 3, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_7319786 : Nat := 118140960795 + 7319786 * 2 ^ 59
def prefixEnd_7319786 : Nat := 4983230072969 + 3 ^ 40 * 7319786 * 2
def baseEnd_7319786 : Nat := 3758568506051403537311923

theorem tailTrace_7319786 : CollatzResearch.WordTrace tailWord_7319786 prefixEnd_7319786 3758568506051403537311923 := by
  unfold tailWord_7319786
  simp only [CollatzResearch.WordTrace]
  refine ⟨66743632064918229191694803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177983018839781944511186141 66743632064918229191694803)
  ·
    refine ⟨100115448097377343787542205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66743632064918229191694803 100115448097377343787542205)
    ·
      refine ⟨37543293036516503920328327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100115448097377343787542205 37543293036516503920328327)
      ·
        refine ⟨56314939554774755880492491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37543293036516503920328327 56314939554774755880492491)
        ·
          refine ⟨84472409332162133820738737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56314939554774755880492491 84472409332162133820738737)
          ·
            refine ⟨63354306999121600365554053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84472409332162133820738737 63354306999121600365554053)
            ·
              refine ⟨11878932562335300068541385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63354306999121600365554053 11878932562335300068541385)
              ·
                refine ⟨8909199421751475051406039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11878932562335300068541385 8909199421751475051406039)
                ·
                  refine ⟨13363799132627212577109059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8909199421751475051406039 13363799132627212577109059)
                  ·
                    refine ⟨20045698698940818865663589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13363799132627212577109059 20045698698940818865663589)
                    ·
                      refine ⟨3758568506051403537311923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20045698698940818865663589 3758568506051403537311923)
                      ·
                        rfl

theorem cell23_7319786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_7319786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319786 prefixEnd_7319786 := by exact prefixLift 7319786
  have htrace : WordTrace (prefixWord ++ tailWord_7319786) baseStart_7319786 baseEnd_7319786 := by
    simpa [prefixWord, tailWord_7319786, baseEnd_7319786] using wordTrace_append hprefix tailTrace_7319786
  have hstable : (prefixWord ++ tailWord_7319786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319786).length < 2 ^ (prefixWord ++ tailWord_7319786).sum := by decide
  have hdescent : baseEnd_7319786 < baseStart_7319786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319806 : List Nat := [4, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_7319806 : Nat := 118140960795 + 7319806 * 2 ^ 59
def prefixEnd_7319806 : Nat := 4983230072969 + 3 ^ 40 * 7319806 * 2
def baseEnd_7319806 : Nat := 3758578775664493459061831

theorem tailTrace_7319806 : CollatzResearch.WordTrace tailWord_7319806 prefixEnd_7319806 3758578775664493459061831 := by
  unfold tailWord_7319806
  simp only [CollatzResearch.WordTrace]
  refine ⟨33371907214950057522813409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177983505146400306788338181 33371907214950057522813409)
  ·
    refine ⟨25028930411212543142110057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33371907214950057522813409 25028930411212543142110057)
    ·
      refine ⟨18771697808409407356582543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25028930411212543142110057 18771697808409407356582543)
      ·
        refine ⟨28157546712614111034873815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18771697808409407356582543 28157546712614111034873815)
        ·
          refine ⟨42236320068921166552310723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28157546712614111034873815 42236320068921166552310723)
          ·
            refine ⟨63354480103381749828466085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42236320068921166552310723 63354480103381749828466085)
            ·
              refine ⟨11878965019384078092837391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63354480103381749828466085 11878965019384078092837391)
              ·
                refine ⟨17818447529076117139256087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11878965019384078092837391 17818447529076117139256087)
                ·
                  refine ⟨26727671293614175708884131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17818447529076117139256087 26727671293614175708884131)
                  ·
                    refine ⟨40091506940421263563326197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26727671293614175708884131 40091506940421263563326197)
                    ·
                      refine ⟨3758578775664493459061831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40091506940421263563326197 3758578775664493459061831)
                      ·
                        rfl

theorem cell23_7319806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_7319806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319806 prefixEnd_7319806 := by exact prefixLift 7319806
  have htrace : WordTrace (prefixWord ++ tailWord_7319806) baseStart_7319806 baseEnd_7319806 := by
    simpa [prefixWord, tailWord_7319806, baseEnd_7319806] using wordTrace_append hprefix tailTrace_7319806
  have hstable : (prefixWord ++ tailWord_7319806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319806).length < 2 ^ (prefixWord ++ tailWord_7319806).sum := by decide
  have hdescent : baseEnd_7319806 < baseStart_7319806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319870 : List Nat := [4, 2, 1, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_7319870 : Nat := 118140960795 + 7319870 * 2 ^ 59
def prefixEnd_7319870 : Nat := 4983230072969 + 3 ^ 40 * 7319870 * 2
def baseEnd_7319870 : Nat := 3758611638426381208661537

theorem tailTrace_7319870 : CollatzResearch.WordTrace tailWord_7319870 prefixEnd_7319870 3758611638426381208661537 := by
  unfold tailWord_7319870
  simp only [CollatzResearch.WordTrace]
  refine ⟨33372198998921074889104633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177985061327579066075224709 33372198998921074889104633)
  ·
    refine ⟨25029149249190806166828475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33372198998921074889104633 25029149249190806166828475)
    ·
      refine ⟨37543723873786209250242713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25029149249190806166828475 37543723873786209250242713)
      ·
        refine ⟨28157792905339656937682035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37543723873786209250242713 28157792905339656937682035)
        ·
          refine ⟨42236689358009485406523053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28157792905339656937682035 42236689358009485406523053)
          ·
            refine ⟨15838758509253557027446145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42236689358009485406523053 15838758509253557027446145)
            ·
              refine ⟨11879068881940167770584609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15838758509253557027446145 11879068881940167770584609)
              ·
                refine ⟨8909301661455125827938457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11879068881940167770584609 8909301661455125827938457)
                ·
                  refine ⟨6681976246091344370953843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8909301661455125827938457 6681976246091344370953843)
                  ·
                    refine ⟨10022964369137016556430765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6681976246091344370953843 10022964369137016556430765)
                    ·
                      refine ⟨3758611638426381208661537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10022964369137016556430765 3758611638426381208661537)
                      ·
                        rfl

theorem cell23_7319870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_7319870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319870 prefixEnd_7319870 := by exact prefixLift 7319870
  have htrace : WordTrace (prefixWord ++ tailWord_7319870) baseStart_7319870 baseEnd_7319870 := by
    simpa [prefixWord, tailWord_7319870, baseEnd_7319870] using wordTrace_append hprefix tailTrace_7319870
  have hstable : (prefixWord ++ tailWord_7319870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319870).length < 2 ^ (prefixWord ++ tailWord_7319870).sum := by decide
  have hdescent : baseEnd_7319870 < baseStart_7319870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319879 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 3]
def baseStart_7319879 : Nat := 118140960795 + 7319879 * 2 ^ 59
def prefixEnd_7319879 : Nat := 4983230072969 + 3 ^ 40 * 7319879 * 2
def baseEnd_7319879 : Nat := 3758616259752271673448995

theorem tailTrace_7319879 : CollatzResearch.WordTrace tailWord_7319879 prefixEnd_7319879 3758616259752271673448995 := by
  unfold tailWord_7319879
  simp only [CollatzResearch.WordTrace]
  refine ⟨266977920248335993649914691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177985280165557329099943127 266977920248335993649914691)
  ·
    refine ⟨400466880372503990474872037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266977920248335993649914691 400466880372503990474872037)
    ·
      refine ⟨75087540069844498214038507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 400466880372503990474872037 75087540069844498214038507)
      ·
        refine ⟨112631310104766747321057761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75087540069844498214038507 112631310104766747321057761)
        ·
          refine ⟨84473482578575060490793321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112631310104766747321057761 84473482578575060490793321)
          ·
            refine ⟨63355111933931295368094991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84473482578575060490793321 63355111933931295368094991)
            ·
              refine ⟨95032667900896943052142487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63355111933931295368094991 95032667900896943052142487)
              ·
                refine ⟨142549001851345414578213731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95032667900896943052142487 142549001851345414578213731)
                ·
                  refine ⟨213823502777018121867320597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142549001851345414578213731 213823502777018121867320597)
                  ·
                    refine ⟨10022976692672724462530653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 213823502777018121867320597 10022976692672724462530653)
                    ·
                      refine ⟨3758616259752271673448995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10022976692672724462530653 3758616259752271673448995)
                      ·
                        rfl

theorem cell23_7319879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_7319879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319879 prefixEnd_7319879 := by exact prefixLift 7319879
  have htrace : WordTrace (prefixWord ++ tailWord_7319879) baseStart_7319879 baseEnd_7319879 := by
    simpa [prefixWord, tailWord_7319879, baseEnd_7319879] using wordTrace_append hprefix tailTrace_7319879
  have hstable : (prefixWord ++ tailWord_7319879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319879).length < 2 ^ (prefixWord ++ tailWord_7319879).sum := by decide
  have hdescent : baseEnd_7319879 < baseStart_7319879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319889 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 1, 4, 4]
def baseStart_7319889 : Nat := 118140960795 + 7319889 * 2 ^ 59
def prefixEnd_7319889 : Nat := 4983230072969 + 3 ^ 40 * 7319889 * 2
def baseEnd_7319889 : Nat := 3758621394558816634323949

theorem tailTrace_7319889 : CollatzResearch.WordTrace tailWord_7319889 prefixEnd_7319889 3758621394558816634323949 := by
  unfold tailWord_7319889
  simp only [CollatzResearch.WordTrace]
  refine ⟨266978284978299765357778721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177985523318866510238519147 266978284978299765357778721)
  ·
    refine ⟨200233713733724824018334041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266978284978299765357778721 200233713733724824018334041)
    ·
      refine ⟨150175285300293618013750531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200233713733724824018334041 150175285300293618013750531)
      ·
        refine ⟨225262927950440427020625797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150175285300293618013750531 225262927950440427020625797)
        ·
          refine ⟨42236798990707580066367337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225262927950440427020625797 42236798990707580066367337)
          ·
            refine ⟨31677599243030685049775503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42236798990707580066367337 31677599243030685049775503)
            ·
              refine ⟨47516398864546027574663255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31677599243030685049775503 47516398864546027574663255)
              ·
                refine ⟨71274598296819041361994883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47516398864546027574663255 71274598296819041361994883)
                ·
                  refine ⟨106911897445228562042992325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71274598296819041361994883 106911897445228562042992325)
                  ·
                    refine ⟨20045980770980355383061061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106911897445228562042992325 20045980770980355383061061)
                    ·
                      refine ⟨3758621394558816634323949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20045980770980355383061061 3758621394558816634323949)
                      ·
                        rfl

theorem cell23_7319889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_7319889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319889 prefixEnd_7319889 := by exact prefixLift 7319889
  have htrace : WordTrace (prefixWord ++ tailWord_7319889) baseStart_7319889 baseEnd_7319889 := by
    simpa [prefixWord, tailWord_7319889, baseEnd_7319889] using wordTrace_append hprefix tailTrace_7319889
  have hstable : (prefixWord ++ tailWord_7319889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319889).length < 2 ^ (prefixWord ++ tailWord_7319889).sum := by decide
  have hdescent : baseEnd_7319889 < baseStart_7319889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319929 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 4, 5]
def baseStart_7319929 : Nat := 118140960795 + 7319929 * 2 ^ 59
def prefixEnd_7319929 : Nat := 4983230072969 + 3 ^ 40 * 7319929 * 2
def baseEnd_7319929 : Nat := 1252880644594998825941255

theorem tailTrace_7319929 : CollatzResearch.WordTrace tailWord_7319929 prefixEnd_7319929 1252880644594998825941255 := by
  unfold tailWord_7319929
  simp only [CollatzResearch.WordTrace]
  refine ⟨266979743898154852189234841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177986495932103234792823227 266979743898154852189234841)
  ·
    refine ⟨200234807923616139141926131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266979743898154852189234841 200234807923616139141926131)
    ·
      refine ⟨300352211885424208712889197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200234807923616139141926131 300352211885424208712889197)
      ·
        refine ⟨112632079457034078267333449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300352211885424208712889197 112632079457034078267333449)
        ·
          refine ⟨84474059592775558700500087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112632079457034078267333449 84474059592775558700500087)
          ·
            refine ⟨126711089389163338050750131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84474059592775558700500087 126711089389163338050750131)
            ·
              refine ⟨190066634083745007076125197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126711089389163338050750131 190066634083745007076125197)
              ·
                refine ⟨71274987781404377653546949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190066634083745007076125197 71274987781404377653546949)
                ·
                  refine ⟨13364060209013320810040053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71274987781404377653546949 13364060209013320810040053)
                  ·
                    refine ⟨1252880644594998825941255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13364060209013320810040053 1252880644594998825941255)
                    ·
                      rfl

theorem cell23_7319929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 5].length) (baseStart_7319929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319929 prefixEnd_7319929 := by exact prefixLift 7319929
  have htrace : WordTrace (prefixWord ++ tailWord_7319929) baseStart_7319929 baseEnd_7319929 := by
    simpa [prefixWord, tailWord_7319929, baseEnd_7319929] using wordTrace_append hprefix tailTrace_7319929
  have hstable : (prefixWord ++ tailWord_7319929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319929).length < 2 ^ (prefixWord ++ tailWord_7319929).sum := by decide
  have hdescent : baseEnd_7319929 < baseStart_7319929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7319993 : List Nat := [1, 2, 1, 4, 3, 1, 3, 1, 3, 4]
def baseStart_7319993 : Nat := 118140960795 + 7319993 * 2 ^ 59
def prefixEnd_7319993 : Nat := 4983230072969 + 3 ^ 40 * 7319993 * 2
def baseEnd_7319993 : Nat := 1252891598848961409141157

theorem tailTrace_7319993 : CollatzResearch.WordTrace tailWord_7319993 prefixEnd_7319993 1252891598848961409141157 := by
  unfold tailWord_7319993
  simp only [CollatzResearch.WordTrace]
  refine ⟨266982078169922991119564633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177988052113281994079709755 266982078169922991119564633)
  ·
    refine ⟨200236558627442243339673475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266982078169922991119564633 200236558627442243339673475)
    ·
      refine ⟨300354837941163365009510213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200236558627442243339673475 300354837941163365009510213)
      ·
        refine ⟨56316532113968130939283165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300354837941163365009510213 56316532113968130939283165)
        ·
          refine ⟨21118699542738049102231187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56316532113968130939283165 21118699542738049102231187)
          ·
            refine ⟨31678049314107073653346781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21118699542738049102231187 31678049314107073653346781)
            ·
              refine ⟨11879268492790152620005043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31678049314107073653346781 11879268492790152620005043)
              ·
                refine ⟨17818902739185228930007565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11879268492790152620005043 17818902739185228930007565)
                ·
                  refine ⟨6682088527194460848752837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17818902739185228930007565 6682088527194460848752837)
                  ·
                    refine ⟨1252891598848961409141157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6682088527194460848752837 1252891598848961409141157)
                    ·
                      rfl

theorem cell23_7319993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 4].length) (baseStart_7319993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7319993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7319993 prefixEnd_7319993 := by exact prefixLift 7319993
  have htrace : WordTrace (prefixWord ++ tailWord_7319993) baseStart_7319993 baseEnd_7319993 := by
    simpa [prefixWord, tailWord_7319993, baseEnd_7319993] using wordTrace_append hprefix tailTrace_7319993
  have hstable : (prefixWord ++ tailWord_7319993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7319993).length < 2 ^ (prefixWord ++ tailWord_7319993).sum := by decide
  have hdescent : baseEnd_7319993 < baseStart_7319993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7319993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320009 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 1, 2, 6]
def baseStart_7320009 : Nat := 118140960795 + 7320009 * 2 ^ 59
def prefixEnd_7320009 : Nat := 4983230072969 + 3 ^ 40 * 7320009 * 2
def baseEnd_7320009 : Nat := 3758683012237356164823397

theorem tailTrace_7320009 : CollatzResearch.WordTrace tailWord_7320009 prefixEnd_7320009 3758683012237356164823397 := by
  unfold tailWord_7320009
  simp only [CollatzResearch.WordTrace]
  refine ⟨266982661737865025852147081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177988441158576683901431387 266982661737865025852147081)
  ·
    refine ⟨200236996303398769389110311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266982661737865025852147081 200236996303398769389110311)
    ·
      refine ⟨300355494455098154083665467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200236996303398769389110311 300355494455098154083665467)
      ·
        refine ⟨450533241682647231125498201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300355494455098154083665467 450533241682647231125498201)
        ·
          refine ⟨337899931261985423344123651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450533241682647231125498201 337899931261985423344123651)
          ·
            refine ⟨506849896892978135016185477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337899931261985423344123651 506849896892978135016185477)
            ·
              refine ⟨95034355667433400315534777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 506849896892978135016185477 95034355667433400315534777)
              ·
                refine ⟨71275766750575050236651083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95034355667433400315534777 71275766750575050236651083)
                ·
                  refine ⟨106913650125862575354976625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71275766750575050236651083 106913650125862575354976625)
                  ·
                    refine ⟨80185237594396931516232469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106913650125862575354976625 80185237594396931516232469)
                    ·
                      refine ⟨3758683012237356164823397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80185237594396931516232469 3758683012237356164823397)
                      ·
                        rfl

theorem cell23_7320009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_7320009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320009 prefixEnd_7320009 := by exact prefixLift 7320009
  have htrace : WordTrace (prefixWord ++ tailWord_7320009) baseStart_7320009 baseEnd_7320009 := by
    simpa [prefixWord, tailWord_7320009, baseEnd_7320009] using wordTrace_append hprefix tailTrace_7320009
  have hstable : (prefixWord ++ tailWord_7320009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320009).length < 2 ^ (prefixWord ++ tailWord_7320009).sum := by decide
  have hdescent : baseEnd_7320009 < baseStart_7320009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320020 : List Nat := [2, 4, 1, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_7320020 : Nat := 118140960795 + 7320020 * 2 ^ 59
def prefixEnd_7320020 : Nat := 4983230072969 + 3 ^ 40 * 7320020 * 2
def baseEnd_7320020 : Nat := 3758688660524555621785847

theorem tailTrace_7320020 : CollatzResearch.WordTrace tailWord_7320020 prefixEnd_7320020 3758688660524555621785847 := by
  unfold tailWord_7320020
  simp only [CollatzResearch.WordTrace]
  refine ⟨133491531470412587365398757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177988708627216783153865009 133491531470412587365398757)
  ·
    refine ⟨25029662150702360131012267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133491531470412587365398757 25029662150702360131012267)
    ·
      refine ⟨37544493226053540196518401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25029662150702360131012267 37544493226053540196518401)
      ·
        refine ⟨28158369919540155147388801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37544493226053540196518401 28158369919540155147388801)
        ·
          refine ⟨21118777439655116360541601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28158369919540155147388801 21118777439655116360541601)
          ·
            refine ⟨15839083079741337270406201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21118777439655116360541601 15839083079741337270406201)
            ·
              refine ⟨11879312309806002952804651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15839083079741337270406201 11879312309806002952804651)
              ·
                refine ⟨17818968464709004429206977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11879312309806002952804651 17818968464709004429206977)
                ·
                  refine ⟨13364226348531753321905233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17818968464709004429206977 13364226348531753321905233)
                  ·
                    refine ⟨10023169761398814991428925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13364226348531753321905233 10023169761398814991428925)
                    ·
                      refine ⟨3758688660524555621785847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10023169761398814991428925 3758688660524555621785847)
                      ·
                        rfl

theorem cell23_7320020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_7320020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320020 prefixEnd_7320020 := by exact prefixLift 7320020
  have htrace : WordTrace (prefixWord ++ tailWord_7320020) baseStart_7320020 baseEnd_7320020 := by
    simpa [prefixWord, tailWord_7320020, baseEnd_7320020] using wordTrace_append hprefix tailTrace_7320020
  have hstable : (prefixWord ++ tailWord_7320020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320020).length < 2 ^ (prefixWord ++ tailWord_7320020).sum := by decide
  have hdescent : baseEnd_7320020 < baseStart_7320020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320043 : List Nat := [1, 1, 1, 1, 2, 3, 3, 4, 2, 3, 2]
def baseStart_7320043 : Nat := 118140960795 + 7320043 * 2 ^ 59
def prefixEnd_7320043 : Nat := 4983230072969 + 3 ^ 40 * 7320043 * 2
def baseEnd_7320043 : Nat := 3758700470579609031798241

theorem tailTrace_7320043 : CollatzResearch.WordTrace tailWord_7320043 prefixEnd_7320043 3758700470579609031798241 := by
  unfold tailWord_7320043
  simp only [CollatzResearch.WordTrace]
  refine ⟨266983901819741849658884783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177989267879827899772589855 266983901819741849658884783)
  ·
    refine ⟨400475852729612774488327175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266983901819741849658884783 400475852729612774488327175)
    ·
      refine ⟨600713779094419161732490763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400475852729612774488327175 600713779094419161732490763)
      ·
        refine ⟨901070668641628742598736145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600713779094419161732490763 901070668641628742598736145)
        ·
          refine ⟨675803001481221556949052109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 901070668641628742598736145 675803001481221556949052109)
          ·
            refine ⟨253426125555458083855894541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 675803001481221556949052109 253426125555458083855894541)
            ·
              refine ⟨95034797083296781445960453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253426125555458083855894541 95034797083296781445960453)
              ·
                refine ⟨17819024453118146521117585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95034797083296781445960453 17819024453118146521117585)
                ·
                  refine ⟨13364268339838609890838189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17819024453118146521117585 13364268339838609890838189)
                  ·
                    refine ⟨5011600627439478709064321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13364268339838609890838189 5011600627439478709064321)
                    ·
                      refine ⟨3758700470579609031798241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5011600627439478709064321 3758700470579609031798241)
                      ·
                        rfl

theorem cell23_7320043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 3, 2].length) (baseStart_7320043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320043 prefixEnd_7320043 := by exact prefixLift 7320043
  have htrace : WordTrace (prefixWord ++ tailWord_7320043) baseStart_7320043 baseEnd_7320043 := by
    simpa [prefixWord, tailWord_7320043, baseEnd_7320043] using wordTrace_append hprefix tailTrace_7320043
  have hstable : (prefixWord ++ tailWord_7320043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320043).length < 2 ^ (prefixWord ++ tailWord_7320043).sum := by decide
  have hdescent : baseEnd_7320043 < baseStart_7320043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320056 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 5, 1, 4]
def baseStart_7320056 : Nat := 118140960795 + 7320056 * 2 ^ 59
def prefixEnd_7320056 : Nat := 4983230072969 + 3 ^ 40 * 7320056 * 2
def baseEnd_7320056 : Nat := 3758707145828117480935681

theorem tailTrace_7320056 : CollatzResearch.WordTrace tailWord_7320056 prefixEnd_7320056 3758707145828117480935681 := by
  unfold tailWord_7320056
  simp only [CollatzResearch.WordTrace]
  refine ⟨133492187984347376439554011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177989583979129835252738681 133492187984347376439554011)
  ·
    refine ⟨200238281976521064659331017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133492187984347376439554011 200238281976521064659331017)
    ·
      refine ⟨150178711482390798494498263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200238281976521064659331017 150178711482390798494498263)
      ·
        refine ⟨225268067223586197741747395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150178711482390798494498263 225268067223586197741747395)
        ·
          refine ⟨337902100835379296612621093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225268067223586197741747395 337902100835379296612621093)
          ·
            refine ⟨63356643906633618114866455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337902100835379296612621093 63356643906633618114866455)
            ·
              refine ⟨95034965859950427172299683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63356643906633618114866455 95034965859950427172299683)
              ·
                refine ⟨142552448789925640758449525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95034965859950427172299683 142552448789925640758449525)
                ·
                  refine ⟨13364292074055528821104643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142552448789925640758449525 13364292074055528821104643)
                  ·
                    refine ⟨20046438111083293231656965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13364292074055528821104643 20046438111083293231656965)
                    ·
                      refine ⟨3758707145828117480935681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20046438111083293231656965 3758707145828117480935681)
                      ·
                        rfl

theorem cell23_7320056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_7320056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320056 prefixEnd_7320056 := by exact prefixLift 7320056
  have htrace : WordTrace (prefixWord ++ tailWord_7320056) baseStart_7320056 baseEnd_7320056 := by
    simpa [prefixWord, tailWord_7320056, baseEnd_7320056] using wordTrace_append hprefix tailTrace_7320056
  have hstable : (prefixWord ++ tailWord_7320056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320056).length < 2 ^ (prefixWord ++ tailWord_7320056).sum := by decide
  have hdescent : baseEnd_7320056 < baseStart_7320056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320084 : List Nat := [2, 4, 3, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_7320084 : Nat := 118140960795 + 7320084 * 2 ^ 59
def prefixEnd_7320084 : Nat := 4983230072969 + 3 ^ 40 * 7320084 * 2
def baseEnd_7320084 : Nat := 3758721523286443371385553

theorem tailTrace_7320084 : CollatzResearch.WordTrace tailWord_7320084 prefixEnd_7320084 3758721523286443371385553 := by
  unfold tailWord_7320084
  simp only [CollatzResearch.WordTrace]
  refine ⟨133492698606296656830563653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177990264808395542440751537 133492698606296656830563653)
  ·
    refine ⟨25029880988680623155730685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133492698606296656830563653 25029880988680623155730685)
    ·
      refine ⟨9386205370755233683399007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25029880988680623155730685 9386205370755233683399007)
      ·
        refine ⟨14079308056132850525098511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9386205370755233683399007 14079308056132850525098511)
        ·
          refine ⟨21118962084199275787647767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14079308056132850525098511 21118962084199275787647767)
          ·
            refine ⟨31678443126298913681471651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21118962084199275787647767 31678443126298913681471651)
            ·
              refine ⟨47517664689448370522207477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31678443126298913681471651 47517664689448370522207477)
              ·
                refine ⟨4454781064635784736456951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47517664689448370522207477 4454781064635784736456951)
                ·
                  refine ⟨6682171596953677104685427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4454781064635784736456951 6682171596953677104685427)
                  ·
                    refine ⟨10023257395430515657028141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6682171596953677104685427 10023257395430515657028141)
                    ·
                      refine ⟨3758721523286443371385553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10023257395430515657028141 3758721523286443371385553)
                      ·
                        rfl

theorem cell23_7320084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_7320084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320084 prefixEnd_7320084 := by exact prefixLift 7320084
  have htrace : WordTrace (prefixWord ++ tailWord_7320084) baseStart_7320084 baseEnd_7320084 := by
    simpa [prefixWord, tailWord_7320084, baseEnd_7320084] using wordTrace_append hprefix tailTrace_7320084
  have hstable : (prefixWord ++ tailWord_7320084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320084).length < 2 ^ (prefixWord ++ tailWord_7320084).sum := by decide
  have hdescent : baseEnd_7320084 < baseStart_7320084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320090 : List Nat := [3, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4]
def baseStart_7320090 : Nat := 118140960795 + 7320090 * 2 ^ 59
def prefixEnd_7320090 : Nat := 4983230072969 + 3 ^ 40 * 7320090 * 2
def baseEnd_7320090 : Nat := 3758724604170370347910525

theorem tailTrace_7320090 : CollatzResearch.WordTrace tailWord_7320090 prefixEnd_7320090 3758724604170370347910525 := by
  unfold tailWord_7320090
  simp only [CollatzResearch.WordTrace]
  refine ⟨66746404012642894171461431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177990410700381051123897149 66746404012642894171461431)
  ·
    refine ⟨100119606018964341257192147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66746404012642894171461431 100119606018964341257192147)
    ·
      refine ⟨150179409028446511885788221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100119606018964341257192147 150179409028446511885788221)
      ·
        refine ⟨56317278385667441957170583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150179409028446511885788221 56317278385667441957170583)
        ·
          refine ⟨84475917578501162935755875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56317278385667441957170583 84475917578501162935755875)
          ·
            refine ⟨126713876367751744403633813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84475917578501162935755875 126713876367751744403633813)
            ·
              refine ⟨5939712954738363018920335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126713876367751744403633813 5939712954738363018920335)
              ·
                refine ⟨8909569432107544528380503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5939712954738363018920335 8909569432107544528380503)
                ·
                  refine ⟨13364354148161316792570755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8909569432107544528380503 13364354148161316792570755)
                  ·
                    refine ⟨20046531222241975188856133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13364354148161316792570755 20046531222241975188856133)
                    ·
                      refine ⟨3758724604170370347910525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20046531222241975188856133 3758724604170370347910525)
                      ·
                        rfl

theorem cell23_7320090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_7320090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320090 prefixEnd_7320090 := by exact prefixLift 7320090
  have htrace : WordTrace (prefixWord ++ tailWord_7320090) baseStart_7320090 baseEnd_7320090 := by
    simpa [prefixWord, tailWord_7320090, baseEnd_7320090] using wordTrace_append hprefix tailTrace_7320090
  have hstable : (prefixWord ++ tailWord_7320090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320090).length < 2 ^ (prefixWord ++ tailWord_7320090).sum := by decide
  have hdescent : baseEnd_7320090 < baseStart_7320090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320110 : List Nat := [4, 1, 3, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_7320110 : Nat := 118140960795 + 7320110 * 2 ^ 59
def prefixEnd_7320110 : Nat := 4983230072969 + 3 ^ 40 * 7320110 * 2
def baseEnd_7320110 : Nat := 3758734873783460269660433

theorem tailTrace_7320110 : CollatzResearch.WordTrace tailWord_7320110 prefixEnd_7320110 3758734873783460269660433 := by
  unfold tailWord_7320110
  simp only [CollatzResearch.WordTrace]
  refine ⟨33373293188812390012696723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177990897006999413401049189 33373293188812390012696723)
  ·
    refine ⟨50059939783218585019045085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33373293188812390012696723 50059939783218585019045085)
    ·
      refine ⟨18772477418706969382141907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50059939783218585019045085 18772477418706969382141907)
      ·
        refine ⟨28158716128060454073212861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18772477418706969382141907 28158716128060454073212861)
        ·
          refine ⟨10559518548022670277454823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28158716128060454073212861 10559518548022670277454823)
          ·
            refine ⟨15839277822034005416182235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10559518548022670277454823 15839277822034005416182235)
            ·
              refine ⟨23758916733051008124273353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15839277822034005416182235 23758916733051008124273353)
              ·
                refine ⟨17819187549788256093205015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23758916733051008124273353 17819187549788256093205015)
                ·
                  refine ⟨26728781324682384139807523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17819187549788256093205015 26728781324682384139807523)
                  ·
                    refine ⟨40093171987023576209711285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26728781324682384139807523 40093171987023576209711285)
                    ·
                      refine ⟨3758734873783460269660433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40093171987023576209711285 3758734873783460269660433)
                      ·
                        rfl

theorem cell23_7320110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_7320110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320110 prefixEnd_7320110 := by exact prefixLift 7320110
  have htrace : WordTrace (prefixWord ++ tailWord_7320110) baseStart_7320110 baseEnd_7320110 := by
    simpa [prefixWord, tailWord_7320110, baseEnd_7320110] using wordTrace_append hprefix tailTrace_7320110
  have hstable : (prefixWord ++ tailWord_7320110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320110).length < 2 ^ (prefixWord ++ tailWord_7320110).sum := by decide
  have hdescent : baseEnd_7320110 < baseStart_7320110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320141 : List Nat := [1, 6, 1, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_7320141 : Nat := 118140960795 + 7320141 * 2 ^ 59
def prefixEnd_7320141 : Nat := 4983230072969 + 3 ^ 40 * 7320141 * 2
def baseEnd_7320141 : Nat := 3758750791683749648372791

theorem tailTrace_7320141 : CollatzResearch.WordTrace tailWord_7320141 prefixEnd_7320141 3758750791683749648372791 := by
  unfold tailWord_7320141
  simp only [CollatzResearch.WordTrace]
  refine ⟨266987476173386812395952277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177991650782257874930634851 266987476173386812395952277)
  ·
    refine ⟨12515037945627506831060263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 266987476173386812395952277 12515037945627506831060263)
    ·
      refine ⟨18772556918441260246590395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12515037945627506831060263 18772556918441260246590395)
      ·
        refine ⟨28158835377661890369885593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18772556918441260246590395 28158835377661890369885593)
        ·
          refine ⟨21119126533246417777414195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28158835377661890369885593 21119126533246417777414195)
          ·
            refine ⟨31678689799869626666121293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21119126533246417777414195 31678689799869626666121293)
            ·
              refine ⟨11879508674951109999795485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31678689799869626666121293 11879508674951109999795485)
              ·
                refine ⟨4454815753106666249923307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11879508674951109999795485 4454815753106666249923307)
                ·
                  refine ⟨6682223629659999374884961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4454815753106666249923307 6682223629659999374884961)
                  ·
                    refine ⟨5011667722244999531163721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6682223629659999374884961 5011667722244999531163721)
                    ·
                      refine ⟨3758750791683749648372791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5011667722244999531163721 3758750791683749648372791)
                      ·
                        rfl

theorem cell23_7320141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_7320141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320141 prefixEnd_7320141 := by exact prefixLift 7320141
  have htrace : WordTrace (prefixWord ++ tailWord_7320141) baseStart_7320141 baseEnd_7320141 := by
    simpa [prefixWord, tailWord_7320141, baseEnd_7320141] using wordTrace_append hprefix tailTrace_7320141
  have hstable : (prefixWord ++ tailWord_7320141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320141).length < 2 ^ (prefixWord ++ tailWord_7320141).sum := by decide
  have hdescent : baseEnd_7320141 < baseStart_7320141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320174 : List Nat := [4, 1, 2, 2, 2, 1, 4, 1, 2, 1, 3]
def baseStart_7320174 : Nat := 118140960795 + 7320174 * 2 ^ 59
def prefixEnd_7320174 : Nat := 4983230072969 + 3 ^ 40 * 7320174 * 2
def baseEnd_7320174 : Nat := 3758767736545348019260139

theorem tailTrace_7320174 : CollatzResearch.WordTrace tailWord_7320174 prefixEnd_7320174 3758767736545348019260139 := by
  unfold tailWord_7320174
  simp only [CollatzResearch.WordTrace]
  refine ⟨33373584972783407378987947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177992453188178172687935717 33373584972783407378987947)
  ·
    refine ⟨50060377459175111068481921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33373584972783407378987947 50060377459175111068481921)
    ·
      refine ⟨37545283094381333301361441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50060377459175111068481921 37545283094381333301361441)
      ·
        refine ⟨28158962320785999976021081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37545283094381333301361441 28158962320785999976021081)
        ·
          refine ⟨21119221740589499982015811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28158962320785999976021081 21119221740589499982015811)
          ·
            refine ⟨31678832610884249973023717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21119221740589499982015811 31678832610884249973023717)
            ·
              refine ⟨5939781114540796869941947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31678832610884249973023717 5939781114540796869941947)
              ·
                refine ⟨8909671671811195304912921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5939781114540796869941947 8909671671811195304912921)
                ·
                  refine ⟨6682253753858396478684691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8909671671811195304912921 6682253753858396478684691)
                  ·
                    refine ⟨10023380630787594718027037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6682253753858396478684691 10023380630787594718027037)
                    ·
                      refine ⟨3758767736545348019260139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10023380630787594718027037 3758767736545348019260139)
                      ·
                        rfl

theorem cell23_7320174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_7320174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320174 prefixEnd_7320174 := by exact prefixLift 7320174
  have htrace : WordTrace (prefixWord ++ tailWord_7320174) baseStart_7320174 baseEnd_7320174 := by
    simpa [prefixWord, tailWord_7320174, baseEnd_7320174] using wordTrace_append hprefix tailTrace_7320174
  have hstable : (prefixWord ++ tailWord_7320174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320174).length < 2 ^ (prefixWord ++ tailWord_7320174).sum := by decide
  have hdescent : baseEnd_7320174 < baseStart_7320174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320280 : List Nat := [2, 1, 2, 2, 3, 2, 1, 3, 3, 4]
def baseStart_7320280 : Nat := 118140960795 + 7320280 * 2 ^ 59
def prefixEnd_7320280 : Nat := 4983230072969 + 3 ^ 40 * 7320280 * 2
def baseEnd_7320280 : Nat := 1252940721831574868178217

theorem tailTrace_7320280 : CollatzResearch.WordTrace tailWord_7320280 prefixEnd_7320280 1252940721831574868178217 := by
  unfold tailWord_7320280
  simp only [CollatzResearch.WordTrace]
  refine ⟨133496272959941619567631147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177995030613255492756841529 133496272959941619567631147)
  ·
    refine ⟨200244409439912429351446721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133496272959941619567631147 200244409439912429351446721)
    ·
      refine ⟨150183307079934322013585041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200244409439912429351446721 150183307079934322013585041)
      ·
        refine ⟨112637480309950741510188781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150183307079934322013585041 112637480309950741510188781)
        ·
          refine ⟨42239055116231528066320793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112637480309950741510188781 42239055116231528066320793)
          ·
            refine ⟨31679291337173646049740595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42239055116231528066320793 31679291337173646049740595)
            ·
              refine ⟨47518937005760469074610893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31679291337173646049740595 47518937005760469074610893)
              ·
                refine ⟨17819601377160175902979085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47518937005760469074610893 17819601377160175902979085)
                ·
                  refine ⟨6682350516435065963617157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17819601377160175902979085 6682350516435065963617157)
                  ·
                    refine ⟨1252940721831574868178217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6682350516435065963617157 1252940721831574868178217)
                    ·
                      rfl

theorem cell23_7320280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_7320280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320280 prefixEnd_7320280 := by exact prefixLift 7320280
  have htrace : WordTrace (prefixWord ++ tailWord_7320280) baseStart_7320280 baseEnd_7320280 := by
    simpa [prefixWord, tailWord_7320280, baseEnd_7320280] using wordTrace_append hprefix tailTrace_7320280
  have hstable : (prefixWord ++ tailWord_7320280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320280).length < 2 ^ (prefixWord ++ tailWord_7320280).sum := by decide
  have hdescent : baseEnd_7320280 < baseStart_7320280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320323 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 5, 5]
def baseStart_7320323 : Nat := 118140960795 + 7320323 * 2 ^ 59
def prefixEnd_7320323 : Nat := 4983230072969 + 3 ^ 40 * 7320323 * 2
def baseEnd_7320323 : Nat := 1252948081720955978765651

theorem tailTrace_7320323 : CollatzResearch.WordTrace tailWord_7320323 prefixEnd_7320323 1252948081720955978765651 := by
  unfold tailWord_7320323
  simp only [CollatzResearch.WordTrace]
  refine ⟨266994114258727457479077623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177996076172484971652718415 266994114258727457479077623)
  ·
    refine ⟨400491171388091186218616435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266994114258727457479077623 400491171388091186218616435)
    ·
      refine ⟨600736757082136779327924653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400491171388091186218616435 600736757082136779327924653)
      ·
        refine ⟨225276283905801292247971745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 600736757082136779327924653 225276283905801292247971745)
        ·
          refine ⟨168957212929350969185978809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225276283905801292247971745 168957212929350969185978809)
          ·
            refine ⟨126717909697013226889484107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168957212929350969185978809 126717909697013226889484107)
            ·
              refine ⟨190076864545519840334226161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126717909697013226889484107 190076864545519840334226161)
              ·
                refine ⟨142557648409139880250669621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190076864545519840334226161 142557648409139880250669621)
                ·
                  refine ⟨13364779538356863773500277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142557648409139880250669621 13364779538356863773500277)
                  ·
                    refine ⟨1252948081720955978765651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13364779538356863773500277 1252948081720955978765651)
                    ·
                      rfl

theorem cell23_7320323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 5].length) (baseStart_7320323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320323 prefixEnd_7320323 := by exact prefixLift 7320323
  have htrace : WordTrace (prefixWord ++ tailWord_7320323) baseStart_7320323 baseEnd_7320323 := by
    simpa [prefixWord, tailWord_7320323, baseEnd_7320323] using wordTrace_append hprefix tailTrace_7320323
  have hstable : (prefixWord ++ tailWord_7320323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320323).length < 2 ^ (prefixWord ++ tailWord_7320323).sum := by decide
  have hdescent : baseEnd_7320323 < baseStart_7320323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320337 : List Nat := [1, 2, 2, 1, 1, 3, 5, 1, 3, 1, 3]
def baseStart_7320337 : Nat := 118140960795 + 7320337 * 2 ^ 59
def prefixEnd_7320337 : Nat := 4983230072969 + 3 ^ 40 * 7320337 * 2
def baseEnd_7320337 : Nat := 3758851433892030881521889

theorem tailTrace_7320337 : CollatzResearch.WordTrace tailWord_7320337 prefixEnd_7320337 3758851433892030881521889 := by
  unfold tailWord_7320337
  simp only [CollatzResearch.WordTrace]
  refine ⟨266994624880676737870087265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177996416587117825246724843 266994624880676737870087265)
  ·
    refine ⟨200245968660507553402565449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266994624880676737870087265 200245968660507553402565449)
    ·
      refine ⟨150184476495380665051924087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200245968660507553402565449 150184476495380665051924087)
      ·
        refine ⟨225276714743070997577886131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150184476495380665051924087 225276714743070997577886131)
        ·
          refine ⟨337915072114606496366829197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225276714743070997577886131 337915072114606496366829197)
          ·
            refine ⟨126718152042977436137560949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337915072114606496366829197 126718152042977436137560949)
            ·
              refine ⟨11879826754029134637896339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126718152042977436137560949 11879826754029134637896339)
              ·
                refine ⟨17819740131043701956844509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11879826754029134637896339 17819740131043701956844509)
                ·
                  refine ⟨6682402549141388233816691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17819740131043701956844509 6682402549141388233816691)
                  ·
                    refine ⟨10023603823712082350725037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6682402549141388233816691 10023603823712082350725037)
                    ·
                      refine ⟨3758851433892030881521889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10023603823712082350725037 3758851433892030881521889)
                      ·
                        rfl

theorem cell23_7320337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 1, 3].length) (baseStart_7320337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320337 prefixEnd_7320337 := by exact prefixLift 7320337
  have htrace : WordTrace (prefixWord ++ tailWord_7320337) baseStart_7320337 baseEnd_7320337 := by
    simpa [prefixWord, tailWord_7320337, baseEnd_7320337] using wordTrace_append hprefix tailTrace_7320337
  have hstable : (prefixWord ++ tailWord_7320337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320337).length < 2 ^ (prefixWord ++ tailWord_7320337).sum := by decide
  have hdescent : baseEnd_7320337 < baseStart_7320337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320363 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 5]
def baseStart_7320363 : Nat := 118140960795 + 7320363 * 2 ^ 59
def prefixEnd_7320363 : Nat := 4983230072969 + 3 ^ 40 * 7320363 * 2
def baseEnd_7320363 : Nat := 3758864784389047779796769

theorem tailTrace_7320363 : CollatzResearch.WordTrace tailWord_7320363 prefixEnd_7320363 3758864784389047779796769 := by
  unfold tailWord_7320363
  simp only [CollatzResearch.WordTrace]
  refine ⟨266995573178582544310533743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177997048785721696207022495 266995573178582544310533743)
  ·
    refine ⟨400493359767873816465800615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266995573178582544310533743 400493359767873816465800615)
    ·
      refine ⟨600740039651810724698700923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400493359767873816465800615 600740039651810724698700923)
      ·
        refine ⟨901110059477716087048051385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600740039651810724698700923 901110059477716087048051385)
        ·
          refine ⟨675832544608287065286038539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 901110059477716087048051385 675832544608287065286038539)
          ·
            refine ⟨1013748816912430597929057809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675832544608287065286038539 1013748816912430597929057809)
            ·
              refine ⟨760311612684322948446793357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1013748816912430597929057809 760311612684322948446793357)
              ·
                refine ⟨285116854756621105667547509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 760311612684322948446793357 285116854756621105667547509)
                ·
                  refine ⟨26729705133433228656332579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 285116854756621105667547509 26729705133433228656332579)
                  ·
                    refine ⟨40094557700149842984498869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26729705133433228656332579 40094557700149842984498869)
                    ·
                      refine ⟨3758864784389047779796769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40094557700149842984498869 3758864784389047779796769)
                      ·
                        rfl

theorem cell23_7320363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 5].length) (baseStart_7320363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320363 prefixEnd_7320363 := by exact prefixLift 7320363
  have htrace : WordTrace (prefixWord ++ tailWord_7320363) baseStart_7320363 baseEnd_7320363 := by
    simpa [prefixWord, tailWord_7320363, baseEnd_7320363] using wordTrace_append hprefix tailTrace_7320363
  have hstable : (prefixWord ++ tailWord_7320363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320363).length < 2 ^ (prefixWord ++ tailWord_7320363).sum := by decide
  have hdescent : baseEnd_7320363 < baseStart_7320363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320370 : List Nat := [3, 2, 1, 1, 3, 1, 3, 2, 1, 6]
def baseStart_7320370 : Nat := 118140960795 + 7320370 * 2 ^ 59
def prefixEnd_7320370 : Nat := 4983230072969 + 3 ^ 40 * 7320370 * 2
def baseEnd_7320370 : Nat := 1252956126251209750803079

theorem tailTrace_7320370 : CollatzResearch.WordTrace tailWord_7320370 prefixEnd_7320370 1252956126251209750803079 := by
  unfold tailWord_7320370
  simp only [CollatzResearch.WordTrace]
  refine ⟨66748957122389296126509641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177997218993038123004025709 66748957122389296126509641)
  ·
    refine ⟨50061717841791972094882231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66748957122389296126509641 50061717841791972094882231)
    ·
      refine ⟨75092576762687958142323347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50061717841791972094882231 75092576762687958142323347)
      ·
        refine ⟨112638865144031937213485021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75092576762687958142323347 112638865144031937213485021)
        ·
          refine ⟨42239574429011976455056883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112638865144031937213485021 42239574429011976455056883)
          ·
            refine ⟨63359361643517964682585325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42239574429011976455056883 63359361643517964682585325)
            ·
              refine ⟨23759760616319236755969497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63359361643517964682585325 23759760616319236755969497)
              ·
                refine ⟨17819820462239427566977123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23759760616319236755969497 17819820462239427566977123)
                ·
                  refine ⟨26729730693359141350465685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17819820462239427566977123 26729730693359141350465685)
                  ·
                    refine ⟨1252956126251209750803079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26729730693359141350465685 1252956126251209750803079)
                    ·
                      rfl

theorem cell23_7320370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_7320370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320370 prefixEnd_7320370 := by exact prefixLift 7320370
  have htrace : WordTrace (prefixWord ++ tailWord_7320370) baseStart_7320370 baseEnd_7320370 := by
    simpa [prefixWord, tailWord_7320370, baseEnd_7320370] using wordTrace_append hprefix tailTrace_7320370
  have hstable : (prefixWord ++ tailWord_7320370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320370).length < 2 ^ (prefixWord ++ tailWord_7320370).sum := by decide
  have hdescent : baseEnd_7320370 < baseStart_7320370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320383 : List Nat := [1, 1, 2, 2, 5, 12]
def baseStart_7320383 : Nat := 118140960795 + 7320383 * 2 ^ 59
def prefixEnd_7320383 : Nat := 4983230072969 + 3 ^ 40 * 7320383 * 2
def baseEnd_7320383 : Nat := 15468621621407974080439

theorem tailTrace_7320383 : CollatzResearch.WordTrace tailWord_7320383 prefixEnd_7320383 15468621621407974080439 := by
  unfold tailWord_7320383
  simp only [CollatzResearch.WordTrace]
  refine ⟨266996302638510087726261803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177997535092340058484174535 266996302638510087726261803)
  ·
    refine ⟨400494453957765131589392705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266996302638510087726261803 400494453957765131589392705)
    ·
      refine ⟨300370840468323848692044529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400494453957765131589392705 300370840468323848692044529)
      ·
        refine ⟨225278130351242886519033397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300370840468323848692044529 225278130351242886519033397)
        ·
          refine ⟨21119824720429020611159381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225278130351242886519033397 21119824720429020611159381)
          ·
            refine ⟨15468621621407974080439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 21119824720429020611159381 15468621621407974080439)
            ·
              rfl

theorem cell23_7320383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 12].length) (baseStart_7320383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320383 prefixEnd_7320383 := by exact prefixLift 7320383
  have htrace : WordTrace (prefixWord ++ tailWord_7320383) baseStart_7320383 baseEnd_7320383 := by
    simpa [prefixWord, tailWord_7320383, baseEnd_7320383] using wordTrace_append hprefix tailTrace_7320383
  have hstable : (prefixWord ++ tailWord_7320383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320383).length < 2 ^ (prefixWord ++ tailWord_7320383).sum := by decide
  have hdescent : baseEnd_7320383 < baseStart_7320383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320387 : List Nat := [1, 1, 1, 3, 1, 4, 4, 2, 2, 4]
def baseStart_7320387 : Nat := 118140960795 + 7320387 * 2 ^ 59
def prefixEnd_7320387 : Nat := 4983230072969 + 3 ^ 40 * 7320387 * 2
def baseEnd_7320387 : Nat := 1252959035974918561965553

theorem tailTrace_7320387 : CollatzResearch.WordTrace tailWord_7320387 prefixEnd_7320387 1252959035974918561965553 := by
  unfold tailWord_7320387
  simp only [CollatzResearch.WordTrace]
  refine ⟨266996448530495596409407415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177997632353663730939604943 266996448530495596409407415)
  ·
    refine ⟨400494672795743394614111123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266996448530495596409407415 400494672795743394614111123)
    ·
      refine ⟨600742009193615091921166685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400494672795743394614111123 600742009193615091921166685)
      ·
        refine ⟨225278253447605659470437507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 600742009193615091921166685 225278253447605659470437507)
        ·
          refine ⟨337917380171408489205656261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225278253447605659470437507 337917380171408489205656261)
          ·
            refine ⟨63359508782139091726060549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337917380171408489205656261 63359508782139091726060549)
            ·
              refine ⟨11879907896651079698636353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63359508782139091726060549 11879907896651079698636353)
              ·
                refine ⟨8909930922488309773977265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11879907896651079698636353 8909930922488309773977265)
                ·
                  refine ⟨6682448191866232330482949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8909930922488309773977265 6682448191866232330482949)
                  ·
                    refine ⟨1252959035974918561965553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6682448191866232330482949 1252959035974918561965553)
                    ·
                      rfl

theorem cell23_7320387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 4].length) (baseStart_7320387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320387 prefixEnd_7320387 := by exact prefixLift 7320387
  have htrace : WordTrace (prefixWord ++ tailWord_7320387) baseStart_7320387 baseEnd_7320387 := by
    simpa [prefixWord, tailWord_7320387, baseEnd_7320387] using wordTrace_append hprefix tailTrace_7320387
  have hstable : (prefixWord ++ tailWord_7320387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320387).length < 2 ^ (prefixWord ++ tailWord_7320387).sum := by decide
  have hdescent : baseEnd_7320387 < baseStart_7320387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320403 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 6]
def baseStart_7320403 : Nat := 118140960795 + 7320403 * 2 ^ 59
def prefixEnd_7320403 : Nat := 4983230072969 + 3 ^ 40 * 7320403 * 2
def baseEnd_7320403 : Nat := 3758885323615227623296585

theorem tailTrace_7320403 : CollatzResearch.WordTrace tailWord_7320403 prefixEnd_7320403 3758885323615227623296585 := by
  unfold tailWord_7320403
  simp only [CollatzResearch.WordTrace]
  refine ⟨266997032098437631141989863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177998021398958420761326575 266997032098437631141989863)
  ·
    refine ⟨400495548147656446712984795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266997032098437631141989863 400495548147656446712984795)
    ·
      refine ⟨600743322221484670069477193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400495548147656446712984795 600743322221484670069477193)
      ·
        refine ⟨450557491666113502552107895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600743322221484670069477193 450557491666113502552107895)
        ·
          refine ⟨675836237499170253828161843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450557491666113502552107895 675836237499170253828161843)
          ·
            refine ⟨1013754356248755380742242765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675836237499170253828161843 1013754356248755380742242765)
            ·
              refine ⟨380157883593283267778341037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1013754356248755380742242765 380157883593283267778341037)
              ·
                refine ⟨142559206347481225416877889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380157883593283267778341037 142559206347481225416877889)
                ·
                  refine ⟨106919404760610919062658417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142559206347481225416877889 106919404760610919062658417)
                  ·
                    refine ⟨80189553570458189296993813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106919404760610919062658417 80189553570458189296993813)
                    ·
                      refine ⟨3758885323615227623296585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80189553570458189296993813 3758885323615227623296585)
                      ·
                        rfl

theorem cell23_7320403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_7320403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320403 prefixEnd_7320403 := by exact prefixLift 7320403
  have htrace : WordTrace (prefixWord ++ tailWord_7320403) baseStart_7320403 baseEnd_7320403 := by
    simpa [prefixWord, tailWord_7320403, baseEnd_7320403] using wordTrace_append hprefix tailTrace_7320403
  have hstable : (prefixWord ++ tailWord_7320403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320403).length < 2 ^ (prefixWord ++ tailWord_7320403).sum := by decide
  have hdescent : baseEnd_7320403 < baseStart_7320403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320407 : List Nat := [1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 4]
def baseStart_7320407 : Nat := 118140960795 + 7320407 * 2 ^ 59
def prefixEnd_7320407 : Nat := 4983230072969 + 3 ^ 40 * 7320407 * 2
def baseEnd_7320407 : Nat := 3758887377537845607646567

theorem tailTrace_7320407 : CollatzResearch.WordTrace tailWord_7320407 prefixEnd_7320407 3758887377537845607646567 := by
  unfold tailWord_7320407
  simp only [CollatzResearch.WordTrace]
  refine ⟨266997177990423139825135475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177998118660282093216756983 266997177990423139825135475)
  ·
    refine ⟨400495766985634709737703213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266997177990423139825135475 400495766985634709737703213)
    ·
      refine ⟨150185912619613016151638705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400495766985634709737703213 150185912619613016151638705)
      ·
        refine ⟨112639434464709762113729029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150185912619613016151638705 112639434464709762113729029)
        ·
          refine ⟨21119893962133080396324193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112639434464709762113729029 21119893962133080396324193)
          ·
            refine ⟨15839920471599810297243145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21119893962133080396324193 15839920471599810297243145)
            ·
              refine ⟨11879940353699857722932359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15839920471599810297243145 11879940353699857722932359)
              ·
                refine ⟨17819910530549786584398539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11879940353699857722932359 17819910530549786584398539)
                ·
                  refine ⟨26729865795824679876597809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17819910530549786584398539 26729865795824679876597809)
                  ·
                    refine ⟨20047399346868509907448357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26729865795824679876597809 20047399346868509907448357)
                    ·
                      refine ⟨3758887377537845607646567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20047399346868509907448357 3758887377537845607646567)
                      ·
                        rfl

theorem cell23_7320407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_7320407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320407 prefixEnd_7320407 := by exact prefixLift 7320407
  have htrace : WordTrace (prefixWord ++ tailWord_7320407) baseStart_7320407 baseEnd_7320407 := by
    simpa [prefixWord, tailWord_7320407, baseEnd_7320407] using wordTrace_append hprefix tailTrace_7320407
  have hstable : (prefixWord ++ tailWord_7320407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320407).length < 2 ^ (prefixWord ++ tailWord_7320407).sum := by decide
  have hdescent : baseEnd_7320407 < baseStart_7320407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320460 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 2, 6]
def baseStart_7320460 : Nat := 118140960795 + 7320460 * 2 ^ 59
def prefixEnd_7320460 : Nat := 4983230072969 + 3 ^ 40 * 7320460 * 2
def baseEnd_7320460 : Nat := 1252971530670844633427941

theorem tailTrace_7320460 : CollatzResearch.WordTrace tailWord_7320460 prefixEnd_7320460 1252971530670844633427941 := by
  unfold tailWord_7320460
  simp only [CollatzResearch.WordTrace]
  refine ⟨133499555529615564938407417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177999407372820753251209889 133499555529615564938407417)
  ·
    refine ⟨100124666647211673703805563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133499555529615564938407417 100124666647211673703805563)
    ·
      refine ⟨150186999970817510555708345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100124666647211673703805563 150186999970817510555708345)
      ·
        refine ⟨112640249978113132916781259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150186999970817510555708345 112640249978113132916781259)
        ·
          refine ⟨168960374967169699375171889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112640249978113132916781259 168960374967169699375171889)
          ·
            refine ⟨126720281225377274531378917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168960374967169699375171889 126720281225377274531378917)
            ·
              refine ⟨23760052729758238974633547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126720281225377274531378917 23760052729758238974633547)
              ·
                refine ⟨35640079094637358461950321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23760052729758238974633547 35640079094637358461950321)
                ·
                  refine ⟨26730059320978018846462741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35640079094637358461950321 26730059320978018846462741)
                  ·
                    refine ⟨1252971530670844633427941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26730059320978018846462741 1252971530670844633427941)
                    ·
                      rfl

theorem cell23_7320460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_7320460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320460 prefixEnd_7320460 := by exact prefixLift 7320460
  have htrace : WordTrace (prefixWord ++ tailWord_7320460) baseStart_7320460 baseEnd_7320460 := by
    simpa [prefixWord, tailWord_7320460, baseEnd_7320460] using wordTrace_append hprefix tailTrace_7320460
  have hstable : (prefixWord ++ tailWord_7320460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320460).length < 2 ^ (prefixWord ++ tailWord_7320460).sum := by decide
  have hdescent : baseEnd_7320460 < baseStart_7320460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320467 : List Nat := [1, 1, 1, 2, 1, 2, 1, 7, 1, 4, 2]
def baseStart_7320467 : Nat := 118140960795 + 7320467 * 2 ^ 59
def prefixEnd_7320467 : Nat := 4983230072969 + 3 ^ 40 * 7320467 * 2
def baseEnd_7320467 : Nat := 3758918186377115372896291

theorem tailTrace_7320467 : CollatzResearch.WordTrace tailWord_7320467 prefixEnd_7320467 3758918186377115372896291 := by
  unfold tailWord_7320467
  simp only [CollatzResearch.WordTrace]
  refine ⟨266999366370205770072319655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177999577580137180048213103 266999366370205770072319655)
  ·
    refine ⟨400499049555308655108479483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266999366370205770072319655 400499049555308655108479483)
    ·
      refine ⟨600748574332962982662719225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400499049555308655108479483 600748574332962982662719225)
      ·
        refine ⟨450561430749722236997039419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600748574332962982662719225 450561430749722236997039419)
        ·
          refine ⟨675842146124583355495559129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450561430749722236997039419 675842146124583355495559129)
          ·
            refine ⟨506881609593437516621669347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 675842146124583355495559129 506881609593437516621669347)
            ·
              refine ⟨760322414390156274932504021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506881609593437516621669347 760322414390156274932504021)
              ·
                refine ⟨17820056587269287693730563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 760322414390156274932504021 17820056587269287693730563)
                ·
                  refine ⟨26730084880903931540595845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17820056587269287693730563 26730084880903931540595845)
                  ·
                    refine ⟨5011890915169487163861721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26730084880903931540595845 5011890915169487163861721)
                    ·
                      refine ⟨3758918186377115372896291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5011890915169487163861721 3758918186377115372896291)
                      ·
                        rfl

theorem cell23_7320467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 4, 2].length) (baseStart_7320467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320467 prefixEnd_7320467 := by exact prefixLift 7320467
  have htrace : WordTrace (prefixWord ++ tailWord_7320467) baseStart_7320467 baseEnd_7320467 := by
    simpa [prefixWord, tailWord_7320467, baseEnd_7320467] using wordTrace_append hprefix tailTrace_7320467
  have hstable : (prefixWord ++ tailWord_7320467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320467).length < 2 ^ (prefixWord ++ tailWord_7320467).sum := by decide
  have hdescent : baseEnd_7320467 < baseStart_7320467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320480 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 4]
def baseStart_7320480 : Nat := 118140960795 + 7320480 * 2 ^ 59
def prefixEnd_7320480 : Nat := 4983230072969 + 3 ^ 40 * 7320480 * 2
def baseEnd_7320480 : Nat := 3758924861625623822033731

theorem tailTrace_7320480 : CollatzResearch.WordTrace tailWord_7320480 prefixEnd_7320480 3758924861625623822033731 := by
  unfold tailWord_7320480
  simp only [CollatzResearch.WordTrace]
  refine ⟨133499920259579336646271447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177999893679439115528361929 133499920259579336646271447)
  ·
    refine ⟨200249880389369004969407171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133499920259579336646271447 200249880389369004969407171)
    ·
      refine ⟨300374820584053507454110757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200249880389369004969407171 300374820584053507454110757)
      ·
        refine ⟨56320278859510032647645767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300374820584053507454110757 56320278859510032647645767)
        ·
          refine ⟨84480418289265048971468651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56320278859510032647645767 84480418289265048971468651)
          ·
            refine ⟨126720627433897573457202977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84480418289265048971468651 126720627433897573457202977)
            ·
              refine ⟨95040470575423180092902233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126720627433897573457202977 95040470575423180092902233)
              ·
                refine ⟨71280352931567385069676675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95040470575423180092902233 71280352931567385069676675)
                ·
                  refine ⟨106920529397351077604515013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71280352931567385069676675 106920529397351077604515013)
                  ·
                    refine ⟨20047599262003327050846565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106920529397351077604515013 20047599262003327050846565)
                    ·
                      refine ⟨3758924861625623822033731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20047599262003327050846565 3758924861625623822033731)
                      ·
                        rfl

theorem cell23_7320480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_7320480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320480 prefixEnd_7320480 := by exact prefixLift 7320480
  have htrace : WordTrace (prefixWord ++ tailWord_7320480) baseStart_7320480 baseEnd_7320480 := by
    simpa [prefixWord, tailWord_7320480, baseEnd_7320480] using wordTrace_append hprefix tailTrace_7320480
  have hstable : (prefixWord ++ tailWord_7320480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320480).length < 2 ^ (prefixWord ++ tailWord_7320480).sum := by decide
  have hdescent : baseEnd_7320480 < baseStart_7320480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320484 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 6, 2, 2]
def baseStart_7320484 : Nat := 118140960795 + 7320484 * 2 ^ 59
def prefixEnd_7320484 : Nat := 4983230072969 + 3 ^ 40 * 7320484 * 2
def baseEnd_7320484 : Nat := 3758926915548241806383713

theorem tailTrace_7320484 : CollatzResearch.WordTrace tailWord_7320484 prefixEnd_7320484 3758926915548241806383713 := by
  unfold tailWord_7320484
  simp only [CollatzResearch.WordTrace]
  refine ⟨133499993205572090987844253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177999990940762787983792337 133499993205572090987844253)
  ·
    refine ⟨50062497452089534120441595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133499993205572090987844253 50062497452089534120441595)
    ·
      refine ⟨75093746178134301180662393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50062497452089534120441595 75093746178134301180662393)
      ·
        refine ⟨56320309633600725885496795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75093746178134301180662393 56320309633600725885496795)
        ·
          refine ⟨84480464450401088828245193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56320309633600725885496795 84480464450401088828245193)
          ·
            refine ⟨63360348337800816621183895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84480464450401088828245193 63360348337800816621183895)
            ·
              refine ⟨95040522506701224931775843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63360348337800816621183895 95040522506701224931775843)
              ·
                refine ⟨142560783760051837397663765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95040522506701224931775843 142560783760051837397663765)
                ·
                  refine ⟨6682536738752429878015489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 142560783760051837397663765 6682536738752429878015489)
                  ·
                    refine ⟨5011902554064322408511617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6682536738752429878015489 5011902554064322408511617)
                    ·
                      refine ⟨3758926915548241806383713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5011902554064322408511617 3758926915548241806383713)
                      ·
                        rfl

theorem cell23_7320484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_7320484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320484 prefixEnd_7320484 := by exact prefixLift 7320484
  have htrace : WordTrace (prefixWord ++ tailWord_7320484) baseStart_7320484 baseEnd_7320484 := by
    simpa [prefixWord, tailWord_7320484, baseEnd_7320484] using wordTrace_append hprefix tailTrace_7320484
  have hstable : (prefixWord ++ tailWord_7320484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320484).length < 2 ^ (prefixWord ++ tailWord_7320484).sum := by decide
  have hdescent : baseEnd_7320484 < baseStart_7320484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320501 : List Nat := [1, 3, 3, 2, 1, 1, 2, 4, 2, 2, 2]
def baseStart_7320501 : Nat := 118140960795 + 7320501 * 2 ^ 59
def prefixEnd_7320501 : Nat := 4983230072969 + 3 ^ 40 * 7320501 * 2
def baseEnd_7320501 : Nat := 3758935644719368239871135

theorem tailTrace_7320501 : CollatzResearch.WordTrace tailWord_7320501 prefixEnd_7320501 3758935644719368239871135 := by
  unfold tailWord_7320501
  simp only [CollatzResearch.WordTrace]
  refine ⟨267000606452082593879057357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178000404301388395919371571 267000606452082593879057357)
  ·
    refine ⟨100125227419530972704646509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267000606452082593879057357 100125227419530972704646509)
    ·
      refine ⟨37546960282324114764242441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100125227419530972704646509 37546960282324114764242441)
      ·
        refine ⟨28160220211743086073181831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37546960282324114764242441 28160220211743086073181831)
        ·
          refine ⟨42240330317614629109772747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28160220211743086073181831 42240330317614629109772747)
          ·
            refine ⟨63360495476421943664659121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42240330317614629109772747 63360495476421943664659121)
            ·
              refine ⟨47520371607316457748494341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63360495476421943664659121 47520371607316457748494341)
              ·
                refine ⟨8910069676371835827842689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47520371607316457748494341 8910069676371835827842689)
                ·
                  refine ⟨6682552257278876870882017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8910069676371835827842689 6682552257278876870882017)
                  ·
                    refine ⟨5011914192959157653161513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6682552257278876870882017 5011914192959157653161513)
                    ·
                      refine ⟨3758935644719368239871135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5011914192959157653161513 3758935644719368239871135)
                      ·
                        rfl

theorem cell23_7320501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_7320501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320501 prefixEnd_7320501 := by exact prefixLift 7320501
  have htrace : WordTrace (prefixWord ++ tailWord_7320501) baseStart_7320501 baseEnd_7320501 := by
    simpa [prefixWord, tailWord_7320501, baseEnd_7320501] using wordTrace_append hprefix tailTrace_7320501
  have hstable : (prefixWord ++ tailWord_7320501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320501).length < 2 ^ (prefixWord ++ tailWord_7320501).sum := by decide
  have hdescent : baseEnd_7320501 < baseStart_7320501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320537 : List Nat := [1, 2, 1, 2, 5, 1, 1, 3, 2, 5]
def baseStart_7320537 : Nat := 118140960795 + 7320537 * 2 ^ 59
def prefixEnd_7320537 : Nat := 4983230072969 + 3 ^ 40 * 7320537 * 2
def baseEnd_7320537 : Nat := 1252984710007643366340323

theorem tailTrace_7320537 : CollatzResearch.WordTrace tailWord_7320537 prefixEnd_7320537 1252984710007643366340323 := by
  unfold tailWord_7320537
  simp only [CollatzResearch.WordTrace]
  refine ⟨267001919479952172027367865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178001279653301448018245243 267001919479952172027367865)
  ·
    refine ⟨200251439609964129020525899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267001919479952172027367865 200251439609964129020525899)
    ·
      refine ⟨300377159414946193530788849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200251439609964129020525899 300377159414946193530788849)
      ·
        refine ⟨225282869561209645148091637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300377159414946193530788849 225282869561209645148091637)
        ·
          refine ⟨21120269021363404232633591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225282869561209645148091637 21120269021363404232633591)
          ·
            refine ⟨31680403532045106348950387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21120269021363404232633591 31680403532045106348950387)
            ·
              refine ⟨47520605298067659523425581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31680403532045106348950387 47520605298067659523425581)
              ·
                refine ⟨17820226986775372321284593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47520605298067659523425581 17820226986775372321284593)
                ·
                  refine ⟨13365170240081529240963445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17820226986775372321284593 13365170240081529240963445)
                  ·
                    refine ⟨1252984710007643366340323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13365170240081529240963445 1252984710007643366340323)
                    ·
                      rfl

theorem cell23_7320537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 5].length) (baseStart_7320537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320537 prefixEnd_7320537 := by exact prefixLift 7320537
  have htrace : WordTrace (prefixWord ++ tailWord_7320537) baseStart_7320537 baseEnd_7320537 := by
    simpa [prefixWord, tailWord_7320537, baseEnd_7320537] using wordTrace_append hprefix tailTrace_7320537
  have hstable : (prefixWord ++ tailWord_7320537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320537).length < 2 ^ (prefixWord ++ tailWord_7320537).sum := by decide
  have hdescent : baseEnd_7320537 < baseStart_7320537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320558 : List Nat := [4, 1, 2, 1, 4, 2, 2, 2, 5]
def baseStart_7320558 : Nat := 118140960795 + 7320558 * 2 ^ 59
def prefixEnd_7320558 : Nat := 4983230072969 + 3 ^ 40 * 7320558 * 2
def baseEnd_7320558 : Nat := 417662768124074946317597

theorem tailTrace_7320558 : CollatzResearch.WordTrace tailWord_7320558 prefixEnd_7320558 417662768124074946317597 := by
  unfold tailWord_7320558
  simp only [CollatzResearch.WordTrace]
  refine ⟨33375335676609511576735291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178001790275250728409254885 33375335676609511576735291)
  ·
    refine ⟨50063003514914267365102937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33375335676609511576735291 50063003514914267365102937)
    ·
      refine ⟨37547252636185700523827203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50063003514914267365102937 37547252636185700523827203)
      ·
        refine ⟨56320878954278550785740805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37547252636185700523827203 56320878954278550785740805)
        ·
          refine ⟨10560164803927228272326401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56320878954278550785740805 10560164803927228272326401)
          ·
            refine ⟨7920123602945421204244801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10560164803927228272326401 7920123602945421204244801)
            ·
              refine ⟨5940092702209065903183601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7920123602945421204244801 5940092702209065903183601)
              ·
                refine ⟨4455069526656799427387701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5940092702209065903183601 4455069526656799427387701)
                ·
                  refine ⟨417662768124074946317597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4455069526656799427387701 417662768124074946317597)
                  ·
                    rfl

theorem cell23_7320558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_7320558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320558 prefixEnd_7320558 := by exact prefixLift 7320558
  have htrace : WordTrace (prefixWord ++ tailWord_7320558) baseStart_7320558 baseEnd_7320558 := by
    simpa [prefixWord, tailWord_7320558, baseEnd_7320558] using wordTrace_append hprefix tailTrace_7320558
  have hstable : (prefixWord ++ tailWord_7320558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320558).length < 2 ^ (prefixWord ++ tailWord_7320558).sum := by decide
  have hdescent : baseEnd_7320558 < baseStart_7320558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320560 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 5]
def baseStart_7320560 : Nat := 118140960795 + 7320560 * 2 ^ 59
def prefixEnd_7320560 : Nat := 4983230072969 + 3 ^ 40 * 7320560 * 2
def baseEnd_7320560 : Nat := 3758965940077983509033363

theorem tailTrace_7320560 : CollatzResearch.WordTrace tailWord_7320560 prefixEnd_7320560 3758965940077983509033363 := by
  unfold tailWord_7320560
  simp only [CollatzResearch.WordTrace]
  refine ⟨133501379179434423477727567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178001838905912564636970089 133501379179434423477727567)
  ·
    refine ⟨200252068769151635216591351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133501379179434423477727567 200252068769151635216591351)
    ·
      refine ⟨300378103153727452824887027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200252068769151635216591351 300378103153727452824887027)
      ·
        refine ⟨450567154730591179237330541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300378103153727452824887027 450567154730591179237330541)
        ·
          refine ⟨168962683023971692213998953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 450567154730591179237330541 168962683023971692213998953)
          ·
            refine ⟨126722012267978769160499215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168962683023971692213998953 126722012267978769160499215)
            ·
              refine ⟨190083018401968153740748823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126722012267978769160499215 190083018401968153740748823)
              ·
                refine ⟨285124527602952230611123235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190083018401968153740748823 285124527602952230611123235)
                ·
                  refine ⟨427686791404428345916684853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285124527602952230611123235 427686791404428345916684853)
                  ·
                    refine ⟨40095636694165157429689205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 427686791404428345916684853 40095636694165157429689205)
                    ·
                      refine ⟨3758965940077983509033363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40095636694165157429689205 3758965940077983509033363)
                      ·
                        rfl

theorem cell23_7320560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_7320560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320560 prefixEnd_7320560 := by exact prefixLift 7320560
  have htrace : WordTrace (prefixWord ++ tailWord_7320560) baseStart_7320560 baseEnd_7320560 := by
    simpa [prefixWord, tailWord_7320560, baseEnd_7320560] using wordTrace_append hprefix tailTrace_7320560
  have hstable : (prefixWord ++ tailWord_7320560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320560).length < 2 ^ (prefixWord ++ tailWord_7320560).sum := by decide
  have hdescent : baseEnd_7320560 < baseStart_7320560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320584 : List Nat := [2, 1, 3, 2, 1, 4, 1, 2, 3, 4]
def baseStart_7320584 : Nat := 118140960795 + 7320584 * 2 ^ 59
def prefixEnd_7320584 : Nat := 4983230072969 + 3 ^ 40 * 7320584 * 2
def baseEnd_7320584 : Nat := 1252992754537897138377751

theorem tailTrace_7320584 : CollatzResearch.WordTrace tailWord_7320584 prefixEnd_7320584 1252992754537897138377751 := by
  unfold tailWord_7320584
  simp only [CollatzResearch.WordTrace]
  refine ⟨133501816855390949527164403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178002422473854599369552537 133501816855390949527164403)
  ·
    refine ⟨200252725283086424290746605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133501816855390949527164403 200252725283086424290746605)
    ·
      refine ⟨75094771981157409109029977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200252725283086424290746605 75094771981157409109029977)
      ·
        refine ⟨56321078985868056831772483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75094771981157409109029977 56321078985868056831772483)
        ·
          refine ⟨84481618478802085247658725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56321078985868056831772483 84481618478802085247658725)
          ·
            refine ⟨15840303464775390983936011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84481618478802085247658725 15840303464775390983936011)
            ·
              refine ⟨23760455197163086475904017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15840303464775390983936011 23760455197163086475904017)
              ·
                refine ⟨17820341397872314856928013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23760455197163086475904017 17820341397872314856928013)
                ·
                  refine ⟨6682628024202118071348005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17820341397872314856928013 6682628024202118071348005)
                  ·
                    refine ⟨1252992754537897138377751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6682628024202118071348005 1252992754537897138377751)
                    ·
                      rfl

theorem cell23_7320584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_7320584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320584 prefixEnd_7320584 := by exact prefixLift 7320584
  have htrace : WordTrace (prefixWord ++ tailWord_7320584) baseStart_7320584 baseEnd_7320584 := by
    simpa [prefixWord, tailWord_7320584, baseEnd_7320584] using wordTrace_append hprefix tailTrace_7320584
  have hstable : (prefixWord ++ tailWord_7320584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320584).length < 2 ^ (prefixWord ++ tailWord_7320584).sum := by decide
  have hdescent : baseEnd_7320584 < baseStart_7320584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320634 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2]
def baseStart_7320634 : Nat := 118140960795 + 7320634 * 2 ^ 59
def prefixEnd_7320634 : Nat := 4983230072969 + 3 ^ 40 * 7320634 * 2
def baseEnd_7320634 : Nat := 3759003937646416219508023

theorem tailTrace_7320634 : CollatzResearch.WordTrace tailWord_7320634 prefixEnd_7320634 3759003937646416219508023 := by
  unfold tailWord_7320634
  simp only [CollatzResearch.WordTrace]
  refine ⟨66751364340150189398412239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178003638240400505062432637 66751364340150189398412239)
  ·
    refine ⟨100127046510225284097618359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66751364340150189398412239 100127046510225284097618359)
    ·
      refine ⟨150190569765337926146427539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100127046510225284097618359 150190569765337926146427539)
      ·
        refine ⟨225285854648006889219641309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150190569765337926146427539 225285854648006889219641309)
        ·
          refine ⟨84482195493002583457365491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225285854648006889219641309 84482195493002583457365491)
          ·
            refine ⟨126723293239503875186048237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84482195493002583457365491 126723293239503875186048237)
            ·
              refine ⟨47521234964813953194768089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126723293239503875186048237 47521234964813953194768089)
              ·
                refine ⟨35640926223610464896076067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47521234964813953194768089 35640926223610464896076067)
                ·
                  refine ⟨53461389335415697344114101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35640926223610464896076067 53461389335415697344114101)
                  ·
                    refine ⟨5012005250195221626010697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53461389335415697344114101 5012005250195221626010697)
                    ·
                      refine ⟨3759003937646416219508023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5012005250195221626010697 3759003937646416219508023)
                      ·
                        rfl

theorem cell23_7320634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2].length) (baseStart_7320634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320634 prefixEnd_7320634 := by exact prefixLift 7320634
  have htrace : WordTrace (prefixWord ++ tailWord_7320634) baseStart_7320634 baseEnd_7320634 := by
    simpa [prefixWord, tailWord_7320634, baseEnd_7320634] using wordTrace_append hprefix tailTrace_7320634
  have hstable : (prefixWord ++ tailWord_7320634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320634).length < 2 ^ (prefixWord ++ tailWord_7320634).sum := by decide
  have hdescent : baseEnd_7320634 < baseStart_7320634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320657 : List Nat := [1, 2, 2, 1, 3, 1, 2, 4, 1, 6]
def baseStart_7320657 : Nat := 118140960795 + 7320657 * 2 ^ 59
def prefixEnd_7320657 : Nat := 4983230072969 + 3 ^ 40 * 7320657 * 2
def baseEnd_7320657 : Nat := 1253005249233823209840139

theorem tailTrace_7320657 : CollatzResearch.WordTrace tailWord_7320657 prefixEnd_7320657 1253005249233823209840139 := by
  unfold tailWord_7320657
  simp only [CollatzResearch.WordTrace]
  refine ⟨267006296239517432521736225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178004197493011621681157483 267006296239517432521736225)
  ·
    refine ⟨200254722179638074391302169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267006296239517432521736225 200254722179638074391302169)
    ·
      refine ⟨150191041634728555793476627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200254722179638074391302169 150191041634728555793476627)
      ·
        refine ⟨225286562452092833690214941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150191041634728555793476627 225286562452092833690214941)
        ·
          refine ⟨84482460919534812633830603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225286562452092833690214941 84482460919534812633830603)
          ·
            refine ⟨126723691379302218950745905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84482460919534812633830603 126723691379302218950745905)
            ·
              refine ⟨95042768534476664213059429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126723691379302218950745905 95042768534476664213059429)
              ·
                refine ⟨17820519100214374539948643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95042768534476664213059429 17820519100214374539948643)
                ·
                  refine ⟨26730778650321561809922965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17820519100214374539948643 26730778650321561809922965)
                  ·
                    refine ⟨1253005249233823209840139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26730778650321561809922965 1253005249233823209840139)
                    ·
                      rfl

theorem cell23_7320657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_7320657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320657 prefixEnd_7320657 := by exact prefixLift 7320657
  have htrace : WordTrace (prefixWord ++ tailWord_7320657) baseStart_7320657 baseEnd_7320657 := by
    simpa [prefixWord, tailWord_7320657, baseEnd_7320657] using wordTrace_append hprefix tailTrace_7320657
  have hstable : (prefixWord ++ tailWord_7320657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320657).length < 2 ^ (prefixWord ++ tailWord_7320657).sum := by decide
  have hdescent : baseEnd_7320657 < baseStart_7320657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320664 : List Nat := [2, 1, 2, 2, 1, 3, 1, 5, 1, 1, 4]
def baseStart_7320664 : Nat := 118140960795 + 7320664 * 2 ^ 59
def prefixEnd_7320664 : Nat := 4983230072969 + 3 ^ 40 * 7320664 * 2
def baseEnd_7320664 : Nat := 3759019342066051102132885

theorem tailTrace_7320664 : CollatzResearch.WordTrace tailWord_7320664 prefixEnd_7320664 3759019342066051102132885 := by
  unfold tailWord_7320664
  simp only [CollatzResearch.WordTrace]
  refine ⟨133503275775246036358620523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178004367700328048478160697 133503275775246036358620523)
  ·
    refine ⟨200254913662869054537930785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133503275775246036358620523 200254913662869054537930785)
    ·
      refine ⟨150191185247151790903448089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200254913662869054537930785 150191185247151790903448089)
      ·
        refine ⟨112643388935363843177586067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150191185247151790903448089 112643388935363843177586067)
        ·
          refine ⟨168965083403045764766379101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112643388935363843177586067 168965083403045764766379101)
          ·
            refine ⟨63361906276142161787392163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168965083403045764766379101 63361906276142161787392163)
            ·
              refine ⟨95042859414213242681088245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63361906276142161787392163 95042859414213242681088245)
              ·
                refine ⟨8910268070082491501352023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95042859414213242681088245 8910268070082491501352023)
                ·
                  refine ⟨13365402105123737252028035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8910268070082491501352023 13365402105123737252028035)
                  ·
                    refine ⟨20048103157685605878042053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13365402105123737252028035 20048103157685605878042053)
                    ·
                      refine ⟨3759019342066051102132885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20048103157685605878042053 3759019342066051102132885)
                      ·
                        rfl

theorem cell23_7320664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_7320664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320664 prefixEnd_7320664 := by exact prefixLift 7320664
  have htrace : WordTrace (prefixWord ++ tailWord_7320664) baseStart_7320664 baseEnd_7320664 := by
    simpa [prefixWord, tailWord_7320664, baseEnd_7320664] using wordTrace_append hprefix tailTrace_7320664
  have hstable : (prefixWord ++ tailWord_7320664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320664).length < 2 ^ (prefixWord ++ tailWord_7320664).sum := by decide
  have hdescent : baseEnd_7320664 < baseStart_7320664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320677 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 3, 1, 6]
def baseStart_7320677 : Nat := 118140960795 + 7320677 * 2 ^ 59
def prefixEnd_7320677 : Nat := 4983230072969 + 3 ^ 40 * 7320677 * 2
def baseEnd_7320677 : Nat := 3759026017314559551270325

theorem tailTrace_7320677 : CollatzResearch.WordTrace tailWord_7320677 prefixEnd_7320677 3759026017314559551270325 := by
  unfold tailWord_7320677
  simp only [CollatzResearch.WordTrace]
  refine ⟨267007025699444975937464285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178004683799629983958309523 267007025699444975937464285)
  ·
    refine ⟨100127634637291865976549107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267007025699444975937464285 100127634637291865976549107)
    ·
      refine ⟨150191451955937798964823661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100127634637291865976549107 150191451955937798964823661)
      ·
        refine ⟨56321794483476674611808873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150191451955937798964823661 56321794483476674611808873)
        ·
          refine ⟨42241345862607505958856655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56321794483476674611808873 42241345862607505958856655)
          ·
            refine ⟨63362018793911258938284983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42241345862607505958856655 63362018793911258938284983)
            ·
              refine ⟨95043028190866888407427475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63362018793911258938284983 95043028190866888407427475)
              ·
                refine ⟨142564542286300332611141213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95043028190866888407427475 142564542286300332611141213)
                ·
                  refine ⟨53461703357362624729177955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142564542286300332611141213 53461703357362624729177955)
                  ·
                    refine ⟨80192555036043937093766933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53461703357362624729177955 80192555036043937093766933)
                    ·
                      refine ⟨3759026017314559551270325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80192555036043937093766933 3759026017314559551270325)
                      ·
                        rfl

theorem cell23_7320677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_7320677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320677 prefixEnd_7320677 := by exact prefixLift 7320677
  have htrace : WordTrace (prefixWord ++ tailWord_7320677) baseStart_7320677 baseEnd_7320677 := by
    simpa [prefixWord, tailWord_7320677, baseEnd_7320677] using wordTrace_append hprefix tailTrace_7320677
  have hstable : (prefixWord ++ tailWord_7320677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320677).length < 2 ^ (prefixWord ++ tailWord_7320677).sum := by decide
  have hdescent : baseEnd_7320677 < baseStart_7320677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320684 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 3]
def baseStart_7320684 : Nat := 118140960795 + 7320684 * 2 ^ 59
def prefixEnd_7320684 : Nat := 4983230072969 + 3 ^ 40 * 7320684 * 2
def baseEnd_7320684 : Nat := 3759029611679141023882793

theorem tailTrace_7320684 : CollatzResearch.WordTrace tailWord_7320684 prefixEnd_7320684 3759029611679141023882793 := by
  unfold tailWord_7320684
  simp only [CollatzResearch.WordTrace]
  refine ⟨133503640505209808066484553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178004854006946410755312737 133503640505209808066484553)
  ·
    refine ⟨100127730378907356049863415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133503640505209808066484553 100127730378907356049863415)
    ·
      refine ⟨150191595568361034074795123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100127730378907356049863415 150191595568361034074795123)
      ·
        refine ⟨225287393352541551112192685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150191595568361034074795123 225287393352541551112192685)
        ·
          refine ⟨84482772507203081667072257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225287393352541551112192685 84482772507203081667072257)
          ·
            refine ⟨63362079380402311250304193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84482772507203081667072257 63362079380402311250304193)
            ·
              refine ⟨47521559535301733437728145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63362079380402311250304193 47521559535301733437728145)
              ·
                refine ⟨35641169651476300078296109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47521559535301733437728145 35641169651476300078296109)
                ·
                  refine ⟨13365438619303612529361041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35641169651476300078296109 13365438619303612529361041)
                  ·
                    refine ⟨10024078964477709397020781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13365438619303612529361041 10024078964477709397020781)
                    ·
                      refine ⟨3759029611679141023882793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10024078964477709397020781 3759029611679141023882793)
                      ·
                        rfl

theorem cell23_7320684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_7320684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320684 prefixEnd_7320684 := by exact prefixLift 7320684
  have htrace : WordTrace (prefixWord ++ tailWord_7320684) baseStart_7320684 baseEnd_7320684 := by
    simpa [prefixWord, tailWord_7320684, baseEnd_7320684] using wordTrace_append hprefix tailTrace_7320684
  have hstable : (prefixWord ++ tailWord_7320684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320684).length < 2 ^ (prefixWord ++ tailWord_7320684).sum := by decide
  have hdescent : baseEnd_7320684 < baseStart_7320684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320687 : List Nat := [1, 1, 2, 1, 3, 3, 4, 8]
def baseStart_7320687 : Nat := 118140960795 + 7320687 * 2 ^ 59
def prefixEnd_7320687 : Nat := 4983230072969 + 3 ^ 40 * 7320687 * 2
def baseEnd_7320687 : Nat := 139223376004485352301677

theorem tailTrace_7320687 : CollatzResearch.WordTrace tailWord_7320687 prefixEnd_7320687 139223376004485352301677 := by
  unfold tailWord_7320687
  simp only [CollatzResearch.WordTrace]
  refine ⟨267007390429408747645328315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178004926952939165096885543 267007390429408747645328315)
  ·
    refine ⟨400511085644113121467992473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267007390429408747645328315 400511085644113121467992473)
    ·
      refine ⟨300383314233084841100994355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400511085644113121467992473 300383314233084841100994355)
      ·
        refine ⟨450574971349627261651491533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300383314233084841100994355 450574971349627261651491533)
        ·
          refine ⟨168965614256110223119309325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 450574971349627261651491533 168965614256110223119309325)
          ·
            refine ⟨63362105346041333669740997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168965614256110223119309325 63362105346041333669740997)
            ·
              refine ⟨11880394752382750063076437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63362105346041333669740997 11880394752382750063076437)
              ·
                refine ⟨139223376004485352301677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11880394752382750063076437 139223376004485352301677)
                ·
                  rfl

theorem cell23_7320687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 8].length) (baseStart_7320687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320687 prefixEnd_7320687 := by exact prefixLift 7320687
  have htrace : WordTrace (prefixWord ++ tailWord_7320687) baseStart_7320687 baseEnd_7320687 := by
    simpa [prefixWord, tailWord_7320687, baseEnd_7320687] using wordTrace_append hprefix tailTrace_7320687
  have hstable : (prefixWord ++ tailWord_7320687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320687).length < 2 ^ (prefixWord ++ tailWord_7320687).sum := by decide
  have hdescent : baseEnd_7320687 < baseStart_7320687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320694 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_7320694 : Nat := 118140960795 + 7320694 * 2 ^ 59
def prefixEnd_7320694 : Nat := 4983230072969 + 3 ^ 40 * 7320694 * 2
def baseEnd_7320694 : Nat := 3759034746485685984757747

theorem tailTrace_7320694 : CollatzResearch.WordTrace tailWord_7320694 prefixEnd_7320694 3759034746485685984757747 := by
  unfold tailWord_7320694
  simp only [CollatzResearch.WordTrace]
  refine ⟨16687977858773961740052071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178005097160255591893888757 16687977858773961740052071)
  ·
    refine ⟨25031966788160942610078107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16687977858773961740052071 25031966788160942610078107)
    ·
      refine ⟨37547950182241413915117161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25031966788160942610078107 37547950182241413915117161)
      ·
        refine ⟨28160962636681060436337871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37547950182241413915117161 28160962636681060436337871)
        ·
          refine ⟨42241443955021590654506807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28160962636681060436337871 42241443955021590654506807)
          ·
            refine ⟨63362165932532385981760211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42241443955021590654506807 63362165932532385981760211)
            ·
              refine ⟨95043248898798578972640317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63362165932532385981760211 95043248898798578972640317)
              ·
                refine ⟨35641218337049467114740119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95043248898798578972640317 35641218337049467114740119)
                ·
                  refine ⟨53461827505574200672110179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35641218337049467114740119 53461827505574200672110179)
                  ·
                    refine ⟨80192741258361301008165269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53461827505574200672110179 80192741258361301008165269)
                    ·
                      refine ⟨3759034746485685984757747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80192741258361301008165269 3759034746485685984757747)
                      ·
                        rfl

theorem cell23_7320694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_7320694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320694 prefixEnd_7320694 := by exact prefixLift 7320694
  have htrace : WordTrace (prefixWord ++ tailWord_7320694) baseStart_7320694 baseEnd_7320694 := by
    simpa [prefixWord, tailWord_7320694, baseEnd_7320694] using wordTrace_append hprefix tailTrace_7320694
  have hstable : (prefixWord ++ tailWord_7320694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320694).length < 2 ^ (prefixWord ++ tailWord_7320694).sum := by decide
  have hdescent : baseEnd_7320694 < baseStart_7320694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320732 : List Nat := [2, 2, 3, 2, 1, 2, 4, 2, 1, 2, 2]
def baseStart_7320732 : Nat := 118140960795 + 7320732 * 2 ^ 59
def prefixEnd_7320732 : Nat := 4983230072969 + 3 ^ 40 * 7320732 * 2
def baseEnd_7320732 : Nat := 3759054258750556836082573

theorem tailTrace_7320732 : CollatzResearch.WordTrace tailWord_7320732 prefixEnd_7320732 3759054258750556836082573 := by
  unfold tailWord_7320732
  simp only [CollatzResearch.WordTrace]
  refine ⟨133504515857122860165358225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178006021142830480220477633 133504515857122860165358225)
  ·
    refine ⟨100128386892842145124018669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133504515857122860165358225 100128386892842145124018669)
    ·
      refine ⟨37548145084815804421507001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100128386892842145124018669 37548145084815804421507001)
      ·
        refine ⟨28161108813611853316130251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37548145084815804421507001 28161108813611853316130251)
        ·
          refine ⟨42241663220417779974195377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28161108813611853316130251 42241663220417779974195377)
          ·
            refine ⟨31681247415313334980646533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42241663220417779974195377 31681247415313334980646533)
            ·
              refine ⟨5940233890371250308871225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31681247415313334980646533 5940233890371250308871225)
              ·
                refine ⟨4455175417778437731653419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5940233890371250308871225 4455175417778437731653419)
                ·
                  refine ⟨6682763126667656597480129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4455175417778437731653419 6682763126667656597480129)
                  ·
                    refine ⟨5012072345000742448110097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6682763126667656597480129 5012072345000742448110097)
                    ·
                      refine ⟨3759054258750556836082573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5012072345000742448110097 3759054258750556836082573)
                      ·
                        rfl

theorem cell23_7320732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_7320732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320732 prefixEnd_7320732 := by exact prefixLift 7320732
  have htrace : WordTrace (prefixWord ++ tailWord_7320732) baseStart_7320732 baseEnd_7320732 := by
    simpa [prefixWord, tailWord_7320732, baseEnd_7320732] using wordTrace_append hprefix tailTrace_7320732
  have hstable : (prefixWord ++ tailWord_7320732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320732).length < 2 ^ (prefixWord ++ tailWord_7320732).sum := by decide
  have hdescent : baseEnd_7320732 < baseStart_7320732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320738 : List Nat := [3, 3, 1, 3, 3, 1, 1, 8]
def baseStart_7320738 : Nat := 118140960795 + 7320738 * 2 ^ 59
def prefixEnd_7320738 : Nat := 4983230072969 + 3 ^ 40 * 7320738 * 2
def baseEnd_7320738 : Nat := 139224345912388289355835

theorem tailTrace_7320738 : CollatzResearch.WordTrace tailWord_7320738 prefixEnd_7320738 139224345912388289355835 := by
  unfold tailWord_7320738
  simp only [CollatzResearch.WordTrace]
  refine ⟨66752312638055995838858717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178006167034815988903623245 66752312638055995838858717)
  ·
    refine ⟨25032117239270998439572019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66752312638055995838858717 25032117239270998439572019)
    ·
      refine ⟨37548175858906497659358029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25032117239270998439572019 37548175858906497659358029)
      ·
        refine ⟨14080565947089936622259261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37548175858906497659358029 14080565947089936622259261)
        ·
          refine ⟨5280212230158726233347223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14080565947089936622259261 5280212230158726233347223)
          ·
            refine ⟨7920318345238089350020835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5280212230158726233347223 7920318345238089350020835)
            ·
              refine ⟨11880477517857134025031253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7920318345238089350020835 11880477517857134025031253)
              ·
                refine ⟨139224345912388289355835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11880477517857134025031253 139224345912388289355835)
                ·
                  rfl

theorem cell23_7320738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 8].length) (baseStart_7320738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320738 prefixEnd_7320738 := by exact prefixLift 7320738
  have htrace : WordTrace (prefixWord ++ tailWord_7320738) baseStart_7320738 baseEnd_7320738 := by
    simpa [prefixWord, tailWord_7320738, baseEnd_7320738] using wordTrace_append hprefix tailTrace_7320738
  have hstable : (prefixWord ++ tailWord_7320738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320738).length < 2 ^ (prefixWord ++ tailWord_7320738).sum := by decide
  have hdescent : baseEnd_7320738 < baseStart_7320738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320741 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 3, 3, 2]
def baseStart_7320741 : Nat := 118140960795 + 7320741 * 2 ^ 59
def prefixEnd_7320741 : Nat := 4983230072969 + 3 ^ 40 * 7320741 * 2
def baseEnd_7320741 : Nat := 3759058880076447300870031

theorem tailTrace_7320741 : CollatzResearch.WordTrace tailWord_7320741 prefixEnd_7320741 3759058880076447300870031 := by
  unfold tailWord_7320741
  simp only [CollatzResearch.WordTrace]
  refine ⟨267009359971213114867794077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178006239980808743245196051 267009359971213114867794077)
  ·
    refine ⟨100128509989204918075422779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267009359971213114867794077 100128509989204918075422779)
    ·
      refine ⟨150192764983807377113134169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100128509989204918075422779 150192764983807377113134169)
      ·
        refine ⟨112644573737855532834850627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150192764983807377113134169 112644573737855532834850627)
        ·
          refine ⟨168966860606783299252275941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112644573737855532834850627 168966860606783299252275941)
          ·
            refine ⟨31681286363771868609801739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168966860606783299252275941 31681286363771868609801739)
            ·
              refine ⟨47521929545657802914702609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31681286363771868609801739 47521929545657802914702609)
              ·
                refine ⟨35641447159243352186026957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47521929545657802914702609 35641447159243352186026957)
                ·
                  refine ⟨13365542684716257069760109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35641447159243352186026957 13365542684716257069760109)
                  ·
                    refine ⟨5012078506768596401160041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13365542684716257069760109 5012078506768596401160041)
                    ·
                      refine ⟨3759058880076447300870031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5012078506768596401160041 3759058880076447300870031)
                      ·
                        rfl

theorem cell23_7320741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_7320741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320741 prefixEnd_7320741 := by exact prefixLift 7320741
  have htrace : WordTrace (prefixWord ++ tailWord_7320741) baseStart_7320741 baseEnd_7320741 := by
    simpa [prefixWord, tailWord_7320741, baseEnd_7320741] using wordTrace_append hprefix tailTrace_7320741
  have hstable : (prefixWord ++ tailWord_7320741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320741).length < 2 ^ (prefixWord ++ tailWord_7320741).sum := by decide
  have hdescent : baseEnd_7320741 < baseStart_7320741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320782 : List Nat := [4, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3]
def baseStart_7320782 : Nat := 118140960795 + 7320782 * 2 ^ 59
def prefixEnd_7320782 : Nat := 4983230072969 + 3 ^ 40 * 7320782 * 2
def baseEnd_7320782 : Nat := 3759079932783281640457343

theorem tailTrace_7320782 : CollatzResearch.WordTrace tailWord_7320782 prefixEnd_7320782 3759079932783281640457343 := by
  unfold tailWord_7320782
  simp only [CollatzResearch.WordTrace]
  refine ⟨33376356920508072358754575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178007236909376385913357733 33376356920508072358754575)
  ·
    refine ⟨50064535380762108538131863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33376356920508072358754575 50064535380762108538131863)
    ·
      refine ⟨75096803071143162807197795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50064535380762108538131863 75096803071143162807197795)
      ·
        refine ⟨112645204606714744210796693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75096803071143162807197795 112645204606714744210796693)
        ·
          refine ⟨5280243965939753634881095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112645204606714744210796693 5280243965939753634881095)
          ·
            refine ⟨7920365948909630452321643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5280243965939753634881095 7920365948909630452321643)
            ·
              refine ⟨11880548923364445678482465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7920365948909630452321643 11880548923364445678482465)
              ·
                refine ⟨8910411692523334258861849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11880548923364445678482465 8910411692523334258861849)
                ·
                  refine ⟨6682808769392500694146387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8910411692523334258861849 6682808769392500694146387)
                  ·
                    refine ⟨10024213154088751041219581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6682808769392500694146387 10024213154088751041219581)
                    ·
                      refine ⟨3759079932783281640457343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10024213154088751041219581 3759079932783281640457343)
                      ·
                        rfl

theorem cell23_7320782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_7320782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320782 prefixEnd_7320782 := by exact prefixLift 7320782
  have htrace : WordTrace (prefixWord ++ tailWord_7320782) baseStart_7320782 baseEnd_7320782 := by
    simpa [prefixWord, tailWord_7320782, baseEnd_7320782] using wordTrace_append hprefix tailTrace_7320782
  have hstable : (prefixWord ++ tailWord_7320782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320782).length < 2 ^ (prefixWord ++ tailWord_7320782).sum := by decide
  have hdescent : baseEnd_7320782 < baseStart_7320782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320787 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 7]
def baseStart_7320787 : Nat := 118140960795 + 7320787 * 2 ^ 59
def prefixEnd_7320787 : Nat := 4983230072969 + 3 ^ 40 * 7320787 * 2
def baseEnd_7320787 : Nat := 3759082500186554120894819

theorem tailTrace_7320787 : CollatzResearch.WordTrace tailWord_7320787 prefixEnd_7320787 3759082500186554120894819 := by
  unfold tailWord_7320787
  simp only [CollatzResearch.WordTrace]
  refine ⟨267011037729046464723968615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178007358486030976482645743 267011037729046464723968615)
  ·
    refine ⟨400516556593569697085952923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267011037729046464723968615 400516556593569697085952923)
    ·
      refine ⟨600774834890354545628929385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400516556593569697085952923 600774834890354545628929385)
      ·
        refine ⟨450581126167765909221697039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600774834890354545628929385 450581126167765909221697039)
        ·
          refine ⟨675871689251648863832545559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450581126167765909221697039 675871689251648863832545559)
          ·
            refine ⟨1013807533877473295748818339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675871689251648863832545559 1013807533877473295748818339)
            ·
              refine ⟨1520711300816209943623227509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013807533877473295748818339 1520711300816209943623227509)
              ·
                refine ⟨142566684451519682214677579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1520711300816209943623227509 142566684451519682214677579)
                ·
                  refine ⟨213850026677279523322016369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142566684451519682214677579 213850026677279523322016369)
                  ·
                    refine ⟨160387520007959642491512277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 213850026677279523322016369 160387520007959642491512277)
                    ·
                      refine ⟨3759082500186554120894819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160387520007959642491512277 3759082500186554120894819)
                      ·
                        rfl

theorem cell23_7320787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_7320787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320787 prefixEnd_7320787 := by exact prefixLift 7320787
  have htrace : WordTrace (prefixWord ++ tailWord_7320787) baseStart_7320787 baseEnd_7320787 := by
    simpa [prefixWord, tailWord_7320787, baseEnd_7320787] using wordTrace_append hprefix tailTrace_7320787
  have hstable : (prefixWord ++ tailWord_7320787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320787).length < 2 ^ (prefixWord ++ tailWord_7320787).sum := by decide
  have hdescent : baseEnd_7320787 < baseStart_7320787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320805 : List Nat := [1, 3, 1, 4, 3, 2, 1, 1, 1, 4, 2]
def baseStart_7320805 : Nat := 118140960795 + 7320805 * 2 ^ 59
def prefixEnd_7320805 : Nat := 4983230072969 + 3 ^ 40 * 7320805 * 2
def baseEnd_7320805 : Nat := 3759091742838335050469737

theorem tailTrace_7320805 : CollatzResearch.WordTrace tailWord_7320805 prefixEnd_7320805 3759091742838335050469737 := by
  unfold tailWord_7320805
  simp only [CollatzResearch.WordTrace]
  refine ⟨267011694242981253798123869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178007796161987502532082579 267011694242981253798123869)
  ·
    refine ⟨100129385341117970174296451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267011694242981253798123869 100129385341117970174296451)
    ·
      refine ⟨150194078011676955261444677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100129385341117970174296451 150194078011676955261444677)
      ·
        refine ⟨28161389627189429111520877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150194078011676955261444677 28161389627189429111520877)
        ·
          refine ⟨10560521110196035916820329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28161389627189429111520877 10560521110196035916820329)
          ·
            refine ⟨7920390832647026937615247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10560521110196035916820329 7920390832647026937615247)
            ·
              refine ⟨11880586248970540406422871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7920390832647026937615247 11880586248970540406422871)
              ·
                refine ⟨17820879373455810609634307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11880586248970540406422871 17820879373455810609634307)
                ·
                  refine ⟨26731319060183715914451461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17820879373455810609634307 26731319060183715914451461)
                  ·
                    refine ⟨5012122323784446733959649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26731319060183715914451461 5012122323784446733959649)
                    ·
                      refine ⟨3759091742838335050469737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5012122323784446733959649 3759091742838335050469737)
                      ·
                        rfl

theorem cell23_7320805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_7320805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320805 prefixEnd_7320805 := by exact prefixLift 7320805
  have htrace : WordTrace (prefixWord ++ tailWord_7320805) baseStart_7320805 baseEnd_7320805 := by
    simpa [prefixWord, tailWord_7320805, baseEnd_7320805] using wordTrace_append hprefix tailTrace_7320805
  have hstable : (prefixWord ++ tailWord_7320805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320805).length < 2 ^ (prefixWord ++ tailWord_7320805).sum := by decide
  have hdescent : baseEnd_7320805 < baseStart_7320805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320888 : List Nat := [2, 1, 2, 1, 3, 1, 1, 7, 1, 4]
def baseStart_7320888 : Nat := 118140960795 + 7320888 * 2 ^ 59
def prefixEnd_7320888 : Nat := 4983230072969 + 3 ^ 40 * 7320888 * 2
def baseEnd_7320888 : Nat := 1253044787244219408577285

theorem tailTrace_7320888 : CollatzResearch.WordTrace tailWord_7320888 prefixEnd_7320888 1253044787244219408577285 := by
  unfold tailWord_7320888
  simp only [CollatzResearch.WordTrace]
  refine ⟨133507360750840279486697659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178009814334453705982263545 133507360750840279486697659)
  ·
    refine ⟨200261041126260419230046489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133507360750840279486697659 200261041126260419230046489)
    ·
      refine ⟨150195780844695314422534867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200261041126260419230046489 150195780844695314422534867)
      ·
        refine ⟨225293671267042971633802301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150195780844695314422534867 225293671267042971633802301)
        ·
          refine ⟨84485126725141114362675863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225293671267042971633802301 84485126725141114362675863)
          ·
            refine ⟨126727690087711671544013795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84485126725141114362675863 126727690087711671544013795)
            ·
              refine ⟨190091535131567507316020693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126727690087711671544013795 190091535131567507316020693)
              ·
                refine ⟨4455270354646113452719235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 190091535131567507316020693 4455270354646113452719235)
                ·
                  refine ⟨6682905531969170179078853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4455270354646113452719235 6682905531969170179078853)
                  ·
                    refine ⟨1253044787244219408577285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6682905531969170179078853 1253044787244219408577285)
                    ·
                      rfl

theorem cell23_7320888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 1, 4].length) (baseStart_7320888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320888 prefixEnd_7320888 := by exact prefixLift 7320888
  have htrace : WordTrace (prefixWord ++ tailWord_7320888) baseStart_7320888 baseEnd_7320888 := by
    simpa [prefixWord, tailWord_7320888, baseEnd_7320888] using wordTrace_append hprefix tailTrace_7320888
  have hstable : (prefixWord ++ tailWord_7320888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320888).length < 2 ^ (prefixWord ++ tailWord_7320888).sum := by decide
  have hdescent : baseEnd_7320888 < baseStart_7320888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320904 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_7320904 : Nat := 118140960795 + 7320904 * 2 ^ 59
def prefixEnd_7320904 : Nat := 4983230072969 + 3 ^ 40 * 7320904 * 2
def baseEnd_7320904 : Nat := 3759142577423130163131781

theorem tailTrace_7320904 : CollatzResearch.WordTrace tailWord_7320904 prefixEnd_7320904 3759142577423130163131781 := by
  unfold tailWord_7320904
  simp only [CollatzResearch.WordTrace]
  refine ⟨133507652534811296852988883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178010203379748395803985177 133507652534811296852988883)
  ·
    refine ⟨200261478802216945279483325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133507652534811296852988883 200261478802216945279483325)
    ·
      refine ⟨75098054550831354479806247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200261478802216945279483325 75098054550831354479806247)
      ·
        refine ⟨112647081826247031719709371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75098054550831354479806247 112647081826247031719709371)
        ·
          refine ⟨168970622739370547579564057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112647081826247031719709371 168970622739370547579564057)
          ·
            refine ⟨126727967054527910684673043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168970622739370547579564057 126727967054527910684673043)
            ·
              refine ⟨190091950581791866027009565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126727967054527910684673043 190091950581791866027009565)
              ·
                refine ⟨71284481468171949760128587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190091950581791866027009565 71284481468171949760128587)
                ·
                  refine ⟨106926722202257924640192881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71284481468171949760128587 106926722202257924640192881)
                  ·
                    refine ⟨80195041651693443480144661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106926722202257924640192881 80195041651693443480144661)
                    ·
                      refine ⟨3759142577423130163131781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80195041651693443480144661 3759142577423130163131781)
                      ·
                        rfl

theorem cell23_7320904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_7320904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320904 prefixEnd_7320904 := by exact prefixLift 7320904
  have htrace : WordTrace (prefixWord ++ tailWord_7320904) baseStart_7320904 baseEnd_7320904 := by
    simpa [prefixWord, tailWord_7320904, baseEnd_7320904] using wordTrace_append hprefix tailTrace_7320904
  have hstable : (prefixWord ++ tailWord_7320904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320904).length < 2 ^ (prefixWord ++ tailWord_7320904).sum := by decide
  have hdescent : baseEnd_7320904 < baseStart_7320904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320905 : List Nat := [1, 2, 1, 1, 2, 3, 6, 2, 1, 4]
def baseStart_7320905 : Nat := 118140960795 + 7320905 * 2 ^ 59
def prefixEnd_7320905 : Nat := 4983230072969 + 3 ^ 40 * 7320905 * 2
def baseEnd_7320905 : Nat := 1253047696967928219739759

theorem tailTrace_7320905 : CollatzResearch.WordTrace tailWord_7320905 prefixEnd_7320905 1253047696967928219739759 := by
  unfold tailWord_7320905
  simp only [CollatzResearch.WordTrace]
  refine ⟨267015341542618970876764169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178010227695079313917842779 267015341542618970876764169)
  ·
    refine ⟨200261506156964228157573127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267015341542618970876764169 200261506156964228157573127)
    ·
      refine ⟨300392259235446342236359691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200261506156964228157573127 300392259235446342236359691)
      ·
        refine ⟨450588388853169513354539537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300392259235446342236359691 450588388853169513354539537)
        ·
          refine ⟨337941291639877135015904653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450588388853169513354539537 337941291639877135015904653)
          ·
            refine ⟨126727984364953925630964245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337941291639877135015904653 126727984364953925630964245)
            ·
              refine ⟨5940374267107215263951449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126727984364953925630964245 5940374267107215263951449)
              ·
                refine ⟨4455280700330411447963587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5940374267107215263951449 4455280700330411447963587)
                ·
                  refine ⟨6682921050495617171945381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4455280700330411447963587 6682921050495617171945381)
                  ·
                    refine ⟨1253047696967928219739759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6682921050495617171945381 1253047696967928219739759)
                    ·
                      rfl

theorem cell23_7320905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 1, 4].length) (baseStart_7320905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320905 prefixEnd_7320905 := by exact prefixLift 7320905
  have htrace : WordTrace (prefixWord ++ tailWord_7320905) baseStart_7320905 baseEnd_7320905 := by
    simpa [prefixWord, tailWord_7320905, baseEnd_7320905] using wordTrace_append hprefix tailTrace_7320905
  have hstable : (prefixWord ++ tailWord_7320905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320905).length < 2 ^ (prefixWord ++ tailWord_7320905).sum := by decide
  have hdescent : baseEnd_7320905 < baseStart_7320905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320928 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 5, 1, 3]
def baseStart_7320928 : Nat := 118140960795 + 7320928 * 2 ^ 59
def prefixEnd_7320928 : Nat := 4983230072969 + 3 ^ 40 * 7320928 * 2
def baseEnd_7320928 : Nat := 3759154900958838069231671

theorem tailTrace_7320928 : CollatzResearch.WordTrace tailWord_7320928 prefixEnd_7320928 3759154900958838069231671 := by
  unfold tailWord_7320928
  simp only [CollatzResearch.WordTrace]
  refine ⟨133508090210767822902425719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178010786947690430536567625 133508090210767822902425719)
  ·
    refine ⟨200262135316151734353638579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133508090210767822902425719 200262135316151734353638579)
    ·
      refine ⟨300393202974227601530457869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200262135316151734353638579 300393202974227601530457869)
      ·
        refine ⟨112647451115335350573921701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300393202974227601530457869 112647451115335350573921701)
        ·
          refine ⟨21121397084125378232610319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112647451115335350573921701 21121397084125378232610319)
          ·
            refine ⟨31682095626188067348915479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21121397084125378232610319 31682095626188067348915479)
            ·
              refine ⟨47523143439282101023373219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31682095626188067348915479 47523143439282101023373219)
              ·
                refine ⟨71284715158923151535059829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47523143439282101023373219 71284715158923151535059829)
                ·
                  refine ⟨6682942046149045456411859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71284715158923151535059829 6682942046149045456411859)
                  ·
                    refine ⟨10024413069223568184617789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6682942046149045456411859 10024413069223568184617789)
                    ·
                      refine ⟨3759154900958838069231671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10024413069223568184617789 3759154900958838069231671)
                      ·
                        rfl

theorem cell23_7320928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_7320928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320928 prefixEnd_7320928 := by exact prefixLift 7320928
  have htrace : WordTrace (prefixWord ++ tailWord_7320928) baseStart_7320928 baseEnd_7320928 := by
    simpa [prefixWord, tailWord_7320928, baseEnd_7320928] using wordTrace_append hprefix tailTrace_7320928
  have hstable : (prefixWord ++ tailWord_7320928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320928).length < 2 ^ (prefixWord ++ tailWord_7320928).sum := by decide
  have hdescent : baseEnd_7320928 < baseStart_7320928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320931 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 3, 5]
def baseStart_7320931 : Nat := 118140960795 + 7320931 * 2 ^ 59
def prefixEnd_7320931 : Nat := 4983230072969 + 3 ^ 40 * 7320931 * 2
def baseEnd_7320931 : Nat := 1253052147133600519164719

theorem tailTrace_7320931 : CollatzResearch.WordTrace tailWord_7320931 prefixEnd_7320931 1253052147133600519164719 := by
  unfold tailWord_7320931
  simp only [CollatzResearch.WordTrace]
  refine ⟨267016289840524777317210647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178010859893683184878140431 267016289840524777317210647)
  ·
    refine ⟨400524434760787165975815971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267016289840524777317210647 400524434760787165975815971)
    ·
      refine ⟨600786652141180748963723957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400524434760787165975815971 600786652141180748963723957)
      ·
        refine ⟨56323748638235695215349121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 600786652141180748963723957 56323748638235695215349121)
        ·
          refine ⟨42242811478676771411511841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56323748638235695215349121 42242811478676771411511841)
          ·
            refine ⟨31682108609007578558633881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42242811478676771411511841 31682108609007578558633881)
            ·
              refine ⟨23761581456755683918975411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31682108609007578558633881 23761581456755683918975411)
              ·
                refine ⟨35642372185133525878463117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23761581456755683918975411 35642372185133525878463117)
                ·
                  refine ⟨13365889569425072204423669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35642372185133525878463117 13365889569425072204423669)
                  ·
                    refine ⟨1253052147133600519164719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13365889569425072204423669 1253052147133600519164719)
                    ·
                      rfl

theorem cell23_7320931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 5].length) (baseStart_7320931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320931 prefixEnd_7320931 := by exact prefixLift 7320931
  have htrace : WordTrace (prefixWord ++ tailWord_7320931) baseStart_7320931 baseEnd_7320931 := by
    simpa [prefixWord, tailWord_7320931, baseEnd_7320931] using wordTrace_append hprefix tailTrace_7320931
  have hstable : (prefixWord ++ tailWord_7320931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320931).length < 2 ^ (prefixWord ++ tailWord_7320931).sum := by decide
  have hdescent : baseEnd_7320931 < baseStart_7320931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320945 : List Nat := [1, 2, 2, 2, 1, 2, 3, 5, 1, 1, 3]
def baseStart_7320945 : Nat := 118140960795 + 7320945 * 2 ^ 59
def prefixEnd_7320945 : Nat := 4983230072969 + 3 ^ 40 * 7320945 * 2
def baseEnd_7320945 : Nat := 3759163630129964502719093

theorem tailTrace_7320945 : CollatzResearch.WordTrace tailWord_7320945 prefixEnd_7320945 3759163630129964502719093 := by
  unfold tailWord_7320945
  simp only [CollatzResearch.WordTrace]
  refine ⟨267016800462474057708220289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178011200308316038472146859 267016800462474057708220289)
  ·
    refine ⟨200262600346855543281165217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267016800462474057708220289 200262600346855543281165217)
    ·
      refine ⟨150196950260141657460873913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200262600346855543281165217 150196950260141657460873913)
      ·
        refine ⟨112647712695106243095655435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150196950260141657460873913 112647712695106243095655435)
        ·
          refine ⟨168971569042659364643483153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112647712695106243095655435 168971569042659364643483153)
          ·
            refine ⟨126728676781994523482612365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168971569042659364643483153 126728676781994523482612365)
            ·
              refine ⟨47523253793247946305979637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126728676781994523482612365 47523253793247946305979637)
              ·
                refine ⟨4455305043116994966185591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47523253793247946305979637 4455305043116994966185591)
                ·
                  refine ⟨6682957564675492449278387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4455305043116994966185591 6682957564675492449278387)
                  ·
                    refine ⟨10024436347013238673917581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6682957564675492449278387 10024436347013238673917581)
                    ·
                      refine ⟨3759163630129964502719093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10024436347013238673917581 3759163630129964502719093)
                      ·
                        rfl

theorem cell23_7320945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_7320945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320945 prefixEnd_7320945 := by exact prefixLift 7320945
  have htrace : WordTrace (prefixWord ++ tailWord_7320945) baseStart_7320945 baseEnd_7320945 := by
    simpa [prefixWord, tailWord_7320945, baseEnd_7320945] using wordTrace_append hprefix tailTrace_7320945
  have hstable : (prefixWord ++ tailWord_7320945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320945).length < 2 ^ (prefixWord ++ tailWord_7320945).sum := by decide
  have hdescent : baseEnd_7320945 < baseStart_7320945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320962 : List Nat := [3, 4, 2, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_7320962 : Nat := 118140960795 + 7320962 * 2 ^ 59
def prefixEnd_7320962 : Nat := 4983230072969 + 3 ^ 40 * 7320962 * 2
def baseEnd_7320962 : Nat := 3759172359301090936206515

theorem tailTrace_7320962 : CollatzResearch.WordTrace tailWord_7320962 prefixEnd_7320962 3759172359301090936206515 := by
  unfold tailWord_7320962
  simp only [CollatzResearch.WordTrace]
  refine ⟨66754355125853117402897285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178011613668941646407726093 66754355125853117402897285)
  ·
    refine ⟨12516441586097459513043241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66754355125853117402897285 12516441586097459513043241)
    ·
      refine ⟨9387331189573094634782431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12516441586097459513043241 9387331189573094634782431)
      ·
        refine ⟨14080996784359641952173647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9387331189573094634782431 14080996784359641952173647)
        ·
          refine ⟨21121495176539462928260471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14080996784359641952173647 21121495176539462928260471)
          ·
            refine ⟨31682242764809194392390707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21121495176539462928260471 31682242764809194392390707)
            ·
              refine ⟨47523364147213791588586061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31682242764809194392390707 47523364147213791588586061)
              ·
                refine ⟨17821261555205171845719773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47523364147213791588586061 17821261555205171845719773)
                ·
                  refine ⟨6682973083201939442144915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17821261555205171845719773 6682973083201939442144915)
                  ·
                    refine ⟨10024459624802909163217373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6682973083201939442144915 10024459624802909163217373)
                    ·
                      refine ⟨3759172359301090936206515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10024459624802909163217373 3759172359301090936206515)
                      ·
                        rfl

theorem cell23_7320962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_7320962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320962 prefixEnd_7320962 := by exact prefixLift 7320962
  have htrace : WordTrace (prefixWord ++ tailWord_7320962) baseStart_7320962 baseEnd_7320962 := by
    simpa [prefixWord, tailWord_7320962, baseEnd_7320962] using wordTrace_append hprefix tailTrace_7320962
  have hstable : (prefixWord ++ tailWord_7320962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320962).length < 2 ^ (prefixWord ++ tailWord_7320962).sum := by decide
  have hdescent : baseEnd_7320962 < baseStart_7320962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320971 : List Nat := [1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 5]
def baseStart_7320971 : Nat := 118140960795 + 7320971 * 2 ^ 59
def prefixEnd_7320971 : Nat := 4983230072969 + 3 ^ 40 * 7320971 * 2
def baseEnd_7320971 : Nat := 3759176980626981400993973

theorem tailTrace_7320971 : CollatzResearch.WordTrace tailWord_7320971 prefixEnd_7320971 3759176980626981400993973 := by
  unfold tailWord_7320971
  simp only [CollatzResearch.WordTrace]
  refine ⟨267017748760379864148666767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178011832506919909432444511 267017748760379864148666767)
  ·
    refine ⟨400526623140569796223000151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267017748760379864148666767 400526623140569796223000151)
    ·
      refine ⟨600789934710854694334500227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400526623140569796223000151 600789934710854694334500227)
      ·
        refine ⟨901184902066282041501750341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600789934710854694334500227 901184902066282041501750341)
        ·
          refine ⟨168972169137427882781578189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 901184902066282041501750341 168972169137427882781578189)
          ·
            refine ⟨63364563426535456043091821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168972169137427882781578189 63364563426535456043091821)
            ·
              refine ⟨23761711284950796016159433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63364563426535456043091821 23761711284950796016159433)
              ·
                refine ⟨17821283463713097012119575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23761711284950796016159433 17821283463713097012119575)
                ·
                  refine ⟨26731925195569645518179363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17821283463713097012119575 26731925195569645518179363)
                  ·
                    refine ⟨40097887793354468277269045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26731925195569645518179363 40097887793354468277269045)
                    ·
                      refine ⟨3759176980626981400993973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40097887793354468277269045 3759176980626981400993973)
                      ·
                        rfl

theorem cell23_7320971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 5].length) (baseStart_7320971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320971 prefixEnd_7320971 := by exact prefixLift 7320971
  have htrace : WordTrace (prefixWord ++ tailWord_7320971) baseStart_7320971 baseEnd_7320971 := by
    simpa [prefixWord, tailWord_7320971, baseEnd_7320971] using wordTrace_append hprefix tailTrace_7320971
  have hstable : (prefixWord ++ tailWord_7320971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320971).length < 2 ^ (prefixWord ++ tailWord_7320971).sum := by decide
  have hdescent : baseEnd_7320971 < baseStart_7320971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320985 : List Nat := [1, 2, 1, 2, 1, 5, 2, 2, 3, 2, 2]
def baseStart_7320985 : Nat := 118140960795 + 7320985 * 2 ^ 59
def prefixEnd_7320985 : Nat := 4983230072969 + 3 ^ 40 * 7320985 * 2
def baseEnd_7320985 : Nat := 3759184169356144346218909

theorem tailTrace_7320985 : CollatzResearch.WordTrace tailWord_7320985 prefixEnd_7320985 3759184169356144346218909 := by
  unfold tailWord_7320985
  simp only [CollatzResearch.WordTrace]
  refine ⟨267018259382329144539676409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178012172921552763026450939 267018259382329144539676409)
  ·
    refine ⟨200263694536746858404757307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267018259382329144539676409 200263694536746858404757307)
    ·
      refine ⟨300395541805120287607135961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200263694536746858404757307 300395541805120287607135961)
      ·
        refine ⟨225296656353840215705351971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300395541805120287607135961 225296656353840215705351971)
        ·
          refine ⟨337944984530760323558027957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225296656353840215705351971 337944984530760323558027957)
          ·
            refine ⟨31682342299758780333565121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 337944984530760323558027957 31682342299758780333565121)
            ·
              refine ⟨23761756724819085250173841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31682342299758780333565121 23761756724819085250173841)
              ·
                refine ⟨17821317543614313937630381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23761756724819085250173841 17821317543614313937630381)
                ·
                  refine ⟨6682994078855367726611393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17821317543614313937630381 6682994078855367726611393)
                  ·
                    refine ⟨5012245559141525794958545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6682994078855367726611393 5012245559141525794958545)
                    ·
                      refine ⟨3759184169356144346218909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5012245559141525794958545 3759184169356144346218909)
                      ·
                        rfl

theorem cell23_7320985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 2, 2].length) (baseStart_7320985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320985 prefixEnd_7320985 := by exact prefixLift 7320985
  have htrace : WordTrace (prefixWord ++ tailWord_7320985) baseStart_7320985 baseEnd_7320985 := by
    simpa [prefixWord, tailWord_7320985, baseEnd_7320985] using wordTrace_append hprefix tailTrace_7320985
  have hstable : (prefixWord ++ tailWord_7320985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320985).length < 2 ^ (prefixWord ++ tailWord_7320985).sum := by decide
  have hdescent : baseEnd_7320985 < baseStart_7320985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7320991 : List Nat := [1, 1, 2, 5, 1, 3, 1, 9]
def baseStart_7320991 : Nat := 118140960795 + 7320991 * 2 ^ 59
def prefixEnd_7320991 : Nat := 4983230072969 + 3 ^ 40 * 7320991 * 2
def baseEnd_7320991 : Nat := 139229157416298937879403

theorem tailTrace_7320991 : CollatzResearch.WordTrace tailWord_7320991 prefixEnd_7320991 139229157416298937879403 := by
  unfold tailWord_7320991
  simp only [CollatzResearch.WordTrace]
  refine ⟨267018478220307407564394827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178012318813538271709596551 267018478220307407564394827)
  ·
    refine ⟨400527717330461111346592241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267018478220307407564394827 400527717330461111346592241)
    ·
      refine ⟨300395787997845833509944181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400527717330461111346592241 300395787997845833509944181)
      ·
        refine ⟨28162105124798046891557267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 300395787997845833509944181 28162105124798046891557267)
        ·
          refine ⟨42243157687197070337335901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28162105124798046891557267 42243157687197070337335901)
          ·
            refine ⟨15841184132698901376500963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42243157687197070337335901 15841184132698901376500963)
            ·
              refine ⟨23761776199048352064751445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15841184132698901376500963 23761776199048352064751445)
              ·
                refine ⟨139229157416298937879403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23761776199048352064751445 139229157416298937879403)
                ·
                  rfl

theorem cell23_7320991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 9].length) (baseStart_7320991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7320991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7320991 prefixEnd_7320991 := by exact prefixLift 7320991
  have htrace : WordTrace (prefixWord ++ tailWord_7320991) baseStart_7320991 baseEnd_7320991 := by
    simpa [prefixWord, tailWord_7320991, baseEnd_7320991] using wordTrace_append hprefix tailTrace_7320991
  have hstable : (prefixWord ++ tailWord_7320991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7320991).length < 2 ^ (prefixWord ++ tailWord_7320991).sum := by decide
  have hdescent : baseEnd_7320991 < baseStart_7320991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7320991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321005 : List Nat := [1, 5, 2, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_7321005 : Nat := 118140960795 + 7321005 * 2 ^ 59
def prefixEnd_7321005 : Nat := 4983230072969 + 3 ^ 40 * 7321005 * 2
def baseEnd_7321005 : Nat := 3759194438969234267968817

theorem tailTrace_7321005 : CollatzResearch.WordTrace tailWord_7321005 prefixEnd_7321005 3759194438969234267968817 := by
  unfold tailWord_7321005
  simp only [CollatzResearch.WordTrace]
  refine ⟨267018988842256687955404469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178012659228171125303602979 267018988842256687955404469)
  ·
    refine ⟨25033030203961564495819169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267018988842256687955404469 25033030203961564495819169)
    ·
      refine ⟨18774772652971173371864377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25033030203961564495819169 18774772652971173371864377)
      ·
        refine ⟨14081079489728380028898283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18774772652971173371864377 14081079489728380028898283)
        ·
          refine ⟨21121619234592570043347425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14081079489728380028898283 21121619234592570043347425)
          ·
            refine ⟨15841214425944427532510569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21121619234592570043347425 15841214425944427532510569)
            ·
              refine ⟨11880910819458320649382927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15841214425944427532510569 11880910819458320649382927)
              ·
                refine ⟨17821366229187480974074391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11880910819458320649382927 17821366229187480974074391)
                ·
                  refine ⟨26732049343781221461111587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17821366229187480974074391 26732049343781221461111587)
                  ·
                    refine ⟨40098074015671832191667381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26732049343781221461111587 40098074015671832191667381)
                    ·
                      refine ⟨3759194438969234267968817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40098074015671832191667381 3759194438969234267968817)
                      ·
                        rfl

theorem cell23_7321005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_7321005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321005 prefixEnd_7321005 := by exact prefixLift 7321005
  have htrace : WordTrace (prefixWord ++ tailWord_7321005) baseStart_7321005 baseEnd_7321005 := by
    simpa [prefixWord, tailWord_7321005, baseEnd_7321005] using wordTrace_append hprefix tailTrace_7321005
  have hstable : (prefixWord ++ tailWord_7321005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321005).length < 2 ^ (prefixWord ++ tailWord_7321005).sum := by decide
  have hdescent : baseEnd_7321005 < baseStart_7321005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321021 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 2, 7]
def baseStart_7321021 : Nat := 118140960795 + 7321021 * 2 ^ 59
def prefixEnd_7321021 : Nat := 4983230072969 + 3 ^ 40 * 7321021 * 2
def baseEnd_7321021 : Nat := 1253067551553235401789581

theorem tailTrace_7321021 : CollatzResearch.WordTrace tailWord_7321021 prefixEnd_7321021 1253067551553235401789581 := by
  unfold tailWord_7321021
  simp only [CollatzResearch.WordTrace]
  refine ⟨267019572410198722687986917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178013048273465815125324611 267019572410198722687986917)
  ·
    refine ⟨50066169826912260503997547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267019572410198722687986917 50066169826912260503997547)
    ·
      refine ⟨75099254740368390755996321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50066169826912260503997547 75099254740368390755996321)
      ·
        refine ⟨56324441055276293066997241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75099254740368390755996321 56324441055276293066997241)
        ·
          refine ⟨42243330791457219800247931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56324441055276293066997241 42243330791457219800247931)
          ·
            refine ⟨63364996187185829700371897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42243330791457219800247931 63364996187185829700371897)
            ·
              refine ⟨47523747140389372275278923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63364996187185829700371897 47523747140389372275278923)
              ·
                refine ⟨71285620710584058412918385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47523747140389372275278923 71285620710584058412918385)
                ·
                  refine ⟨53464215532938043809688789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71285620710584058412918385 53464215532938043809688789)
                  ·
                    refine ⟨1253067551553235401789581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53464215532938043809688789 1253067551553235401789581)
                    ·
                      rfl

theorem cell23_7321021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_7321021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321021 prefixEnd_7321021 := by exact prefixLift 7321021
  have htrace : WordTrace (prefixWord ++ tailWord_7321021) baseStart_7321021 baseEnd_7321021 := by
    simpa [prefixWord, tailWord_7321021, baseEnd_7321021] using wordTrace_append hprefix tailTrace_7321021
  have hstable : (prefixWord ++ tailWord_7321021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321021).length < 2 ^ (prefixWord ++ tailWord_7321021).sum := by decide
  have hdescent : baseEnd_7321021 < baseStart_7321021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321045 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 3, 3, 2]
def baseStart_7321045 : Nat := 118140960795 + 7321045 * 2 ^ 59
def prefixEnd_7321045 : Nat := 4983230072969 + 3 ^ 40 * 7321045 * 2
def baseEnd_7321045 : Nat := 3759214978195414111468633

theorem tailTrace_7321045 : CollatzResearch.WordTrace tailWord_7321045 prefixEnd_7321045 3759214978195414111468633 := by
  unfold tailWord_7321045
  simp only [CollatzResearch.WordTrace]
  refine ⟨267020447762111774786860589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178013631841407849857907059 267020447762111774786860589)
  ·
    refine ⟨100132667910791915545072721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267020447762111774786860589 100132667910791915545072721)
    ·
      refine ⟨75099500933093936658804541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100132667910791915545072721 75099500933093936658804541)
      ·
        refine ⟨28162312849910226247051703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75099500933093936658804541 28162312849910226247051703)
        ·
          refine ⟨42243469274865339370577555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28162312849910226247051703 42243469274865339370577555)
          ·
            refine ⟨63365203912298009055866333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42243469274865339370577555 63365203912298009055866333)
            ·
              refine ⟨23761951467111753395949875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63365203912298009055866333 23761951467111753395949875)
              ·
                refine ⟨35642927200667630093924813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23761951467111753395949875 35642927200667630093924813)
                ·
                  refine ⟨13366097700250361285221805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35642927200667630093924813 13366097700250361285221805)
                  ·
                    refine ⟨5012286637593885481958177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13366097700250361285221805 5012286637593885481958177)
                    ·
                      refine ⟨3759214978195414111468633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5012286637593885481958177 3759214978195414111468633)
                      ·
                        rfl

theorem cell23_7321045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_7321045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321045 prefixEnd_7321045 := by exact prefixLift 7321045
  have htrace : WordTrace (prefixWord ++ tailWord_7321045) baseStart_7321045 baseEnd_7321045 := by
    simpa [prefixWord, tailWord_7321045, baseEnd_7321045] using wordTrace_append hprefix tailTrace_7321045
  have hstable : (prefixWord ++ tailWord_7321045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321045).length < 2 ^ (prefixWord ++ tailWord_7321045).sum := by decide
  have hdescent : baseEnd_7321045 < baseStart_7321045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321069 : List Nat := [1, 5, 1, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_7321069 : Nat := 118140960795 + 7321069 * 2 ^ 59
def prefixEnd_7321069 : Nat := 4983230072969 + 3 ^ 40 * 7321069 * 2
def baseEnd_7321069 : Nat := 3759227301731122017568523

theorem tailTrace_7321069 : CollatzResearch.WordTrace tailWord_7321069 prefixEnd_7321069 3759227301731122017568523 := by
  unfold tailWord_7321069
  simp only [CollatzResearch.WordTrace]
  refine ⟨267021323114024826885734261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178014215409349884590489507 267021323114024826885734261)
  ·
    refine ⟨25033249041939827520537587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267021323114024826885734261 25033249041939827520537587)
    ·
      refine ⟨37549873562909741280806381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25033249041939827520537587 37549873562909741280806381)
      ·
        refine ⟨14081202586091152980302393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37549873562909741280806381 14081202586091152980302393)
        ·
          refine ⟨10560901939568364735226795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14081202586091152980302393 10560901939568364735226795)
          ·
            refine ⟨15841352909352547102840193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10560901939568364735226795 15841352909352547102840193)
            ·
              refine ⟨11881014682014410327130145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15841352909352547102840193 11881014682014410327130145)
              ·
                refine ⟨8910761011510807745347609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11881014682014410327130145 8910761011510807745347609)
                ·
                  refine ⟨6683070758633105809010707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8910761011510807745347609 6683070758633105809010707)
                  ·
                    refine ⟨10024606137949658713516061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6683070758633105809010707 10024606137949658713516061)
                    ·
                      refine ⟨3759227301731122017568523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10024606137949658713516061 3759227301731122017568523)
                      ·
                        rfl

theorem cell23_7321069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_7321069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321069 prefixEnd_7321069 := by exact prefixLift 7321069
  have htrace : WordTrace (prefixWord ++ tailWord_7321069) baseStart_7321069 baseEnd_7321069 := by
    simpa [prefixWord, tailWord_7321069, baseEnd_7321069] using wordTrace_append hprefix tailTrace_7321069
  have hstable : (prefixWord ++ tailWord_7321069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321069).length < 2 ^ (prefixWord ++ tailWord_7321069).sum := by decide
  have hdescent : baseEnd_7321069 < baseStart_7321069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321081 : List Nat := [1, 2, 1, 3, 1, 2, 1, 5, 7]
def baseStart_7321081 : Nat := 118140960795 + 7321081 * 2 ^ 59
def prefixEnd_7321081 : Nat := 4983230072969 + 3 ^ 40 * 7321081 * 2
def baseEnd_7321081 : Nat := 417692607055441774513163

theorem tailTrace_7321081 : CollatzResearch.WordTrace tailWord_7321081 prefixEnd_7321081 417692607055441774513163 := by
  unfold tailWord_7321081
  simp only [CollatzResearch.WordTrace]
  refine ⟨267021760789981352935171097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178014507193320901956780731 267021760789981352935171097)
  ·
    refine ⟨200266320592486014701378323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267021760789981352935171097 200266320592486014701378323)
    ·
      refine ⟨300399480888729022052067485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200266320592486014701378323 300399480888729022052067485)
      ·
        refine ⟨112649805333273383269525307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300399480888729022052067485 112649805333273383269525307)
        ·
          refine ⟨168974707999910074904287961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112649805333273383269525307 168974707999910074904287961)
          ·
            refine ⟨126731030999932556178215971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168974707999910074904287961 126731030999932556178215971)
            ·
              refine ⟨190096546499898834267323957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126731030999932556178215971 190096546499898834267323957)
              ·
                refine ⟨17821551234365515712561621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190096546499898834267323957 17821551234365515712561621)
                ·
                  refine ⟨417692607055441774513163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17821551234365515712561621 417692607055441774513163)
                  ·
                    rfl

theorem cell23_7321081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 7].length) (baseStart_7321081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321081 prefixEnd_7321081 := by exact prefixLift 7321081
  have htrace : WordTrace (prefixWord ++ tailWord_7321081) baseStart_7321081 baseEnd_7321081 := by
    simpa [prefixWord, tailWord_7321081, baseEnd_7321081] using wordTrace_append hprefix tailTrace_7321081
  have hstable : (prefixWord ++ tailWord_7321081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321081).length < 2 ^ (prefixWord ++ tailWord_7321081).sum := by decide
  have hdescent : baseEnd_7321081 < baseStart_7321081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321098 : List Nat := [3, 1, 2, 2, 2, 3, 1, 2, 7]
def baseStart_7321098 : Nat := 118140960795 + 7321098 * 2 ^ 59
def prefixEnd_7321098 : Nat := 4983230072969 + 3 ^ 40 * 7321098 * 2
def baseEnd_7321098 : Nat := 417693576963344711567321

theorem tailTrace_7321098 : CollatzResearch.WordTrace tailWord_7321098 prefixEnd_7321098 417693576963344711567321 := by
  unfold tailWord_7321098
  simp only [CollatzResearch.WordTrace]
  refine ⟨66755595207729941209634987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178014920553946509892359965 66755595207729941209634987)
  ·
    refine ⟨100133392811594911814452481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66755595207729941209634987 100133392811594911814452481)
    ·
      refine ⟨75100044608696183860839361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100133392811594911814452481 75100044608696183860839361)
      ·
        refine ⟨56325033456522137895629521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75100044608696183860839361 56325033456522137895629521)
        ·
          refine ⟨42243775092391603421722141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56325033456522137895629521 42243775092391603421722141)
          ·
            refine ⟨15841415659646851283145803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42243775092391603421722141 15841415659646851283145803)
            ·
              refine ⟨23762123489470276924718705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15841415659646851283145803 23762123489470276924718705)
              ·
                refine ⟨17821592617102707693539029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23762123489470276924718705 17821592617102707693539029)
                ·
                  refine ⟨417693576963344711567321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17821592617102707693539029 417693576963344711567321)
                  ·
                    rfl

theorem cell23_7321098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 7].length) (baseStart_7321098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321098 prefixEnd_7321098 := by exact prefixLift 7321098
  have htrace : WordTrace (prefixWord ++ tailWord_7321098) baseStart_7321098 baseEnd_7321098 := by
    simpa [prefixWord, tailWord_7321098, baseEnd_7321098] using wordTrace_append hprefix tailTrace_7321098
  have hstable : (prefixWord ++ tailWord_7321098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321098).length < 2 ^ (prefixWord ++ tailWord_7321098).sum := by decide
  have hdescent : baseEnd_7321098 < baseStart_7321098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321168 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 3]
def baseStart_7321168 : Nat := 118140960795 + 7321168 * 2 ^ 59
def prefixEnd_7321168 : Nat := 4983230072969 + 3 ^ 40 * 7321168 * 2
def baseEnd_7321168 : Nat := 3759278136315917130230567

theorem tailTrace_7321168 : CollatzResearch.WordTrace tailWord_7321168 prefixEnd_7321168 3759278136315917130230567 := by
  unfold tailWord_7321168
  simp only [CollatzResearch.WordTrace]
  refine ⟨133512466970333083396794079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178016622627110777862392105 133512466970333083396794079)
  ·
    refine ⟨200268700455499625095191119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133512466970333083396794079 200268700455499625095191119)
    ·
      refine ⟨300403050683249437642786679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200268700455499625095191119 300403050683249437642786679)
      ·
        refine ⟨450604576024874156464180019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300403050683249437642786679 450604576024874156464180019)
        ·
          refine ⟨675906864037311234696270029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450604576024874156464180019 675906864037311234696270029)
          ·
            refine ⟨253465074013991713011101261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 675906864037311234696270029 253465074013991713011101261)
            ·
              refine ⟨95049402755246892379162973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253465074013991713011101261 95049402755246892379162973)
              ·
                refine ⟨35643526033217584642186115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95049402755246892379162973 35643526033217584642186115)
                ·
                  refine ⟨53465289049826376963279173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35643526033217584642186115 53465289049826376963279173)
                  ·
                    refine ⟨10024741696842445680614845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53465289049826376963279173 10024741696842445680614845)
                    ·
                      refine ⟨3759278136315917130230567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10024741696842445680614845 3759278136315917130230567)
                      ·
                        rfl

theorem cell23_7321168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 3].length) (baseStart_7321168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321168 prefixEnd_7321168 := by exact prefixLift 7321168
  have htrace : WordTrace (prefixWord ++ tailWord_7321168) baseStart_7321168 baseEnd_7321168 := by
    simpa [prefixWord, tailWord_7321168, baseEnd_7321168] using wordTrace_append hprefix tailTrace_7321168
  have hstable : (prefixWord ++ tailWord_7321168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321168).length < 2 ^ (prefixWord ++ tailWord_7321168).sum := by decide
  have hdescent : baseEnd_7321168 < baseStart_7321168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321185 : List Nat := [1, 2, 3, 1, 1, 3, 3, 2, 2, 2, 3]
def baseStart_7321185 : Nat := 118140960795 + 7321185 * 2 ^ 59
def prefixEnd_7321185 : Nat := 4983230072969 + 3 ^ 40 * 7321185 * 2
def baseEnd_7321185 : Nat := 3759286865487043563717989

theorem tailTrace_7321185 : CollatzResearch.WordTrace tailWord_7321185 prefixEnd_7321185 3759286865487043563717989 := by
  unfold tailWord_7321185
  simp only [CollatzResearch.WordTrace]
  refine ⟨267025553981604578696957009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178017035987736385797971339 267025553981604578696957009)
  ·
    refine ⟨200269165486203434022717757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267025553981604578696957009 200269165486203434022717757)
    ·
      refine ⟨75100937057326287758519159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200269165486203434022717757 75100937057326287758519159)
      ·
        refine ⟨112651405585989431637778739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75100937057326287758519159 112651405585989431637778739)
        ·
          refine ⟨168977108378984147456668109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112651405585989431637778739 168977108378984147456668109)
          ·
            refine ⟨63366415642119055296250541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168977108378984147456668109 63366415642119055296250541)
            ·
              refine ⟨23762405865794645736093953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63366415642119055296250541 23762405865794645736093953)
              ·
                refine ⟨17821804399345984302070465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23762405865794645736093953 17821804399345984302070465)
                ·
                  refine ⟨13366353299509488226552849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17821804399345984302070465 13366353299509488226552849)
                  ·
                    refine ⟨10024764974632116169914637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13366353299509488226552849 10024764974632116169914637)
                    ·
                      refine ⟨3759286865487043563717989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10024764974632116169914637 3759286865487043563717989)
                      ·
                        rfl

theorem cell23_7321185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_7321185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321185 prefixEnd_7321185 := by exact prefixLift 7321185
  have htrace : WordTrace (prefixWord ++ tailWord_7321185) baseStart_7321185 baseEnd_7321185 := by
    simpa [prefixWord, tailWord_7321185, baseEnd_7321185] using wordTrace_append hprefix tailTrace_7321185
  have hstable : (prefixWord ++ tailWord_7321185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321185).length < 2 ^ (prefixWord ++ tailWord_7321185).sum := by decide
  have hdescent : baseEnd_7321185 < baseStart_7321185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321188 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 8]
def baseStart_7321188 : Nat := 118140960795 + 7321188 * 2 ^ 59
def prefixEnd_7321188 : Nat := 4983230072969 + 3 ^ 40 * 7321188 * 2
def baseEnd_7321188 : Nat := 417698711769889672442275

theorem tailTrace_7321188 : CollatzResearch.WordTrace tailWord_7321188 prefixEnd_7321188 417698711769889672442275 := by
  unfold tailWord_7321188
  simp only [CollatzResearch.WordTrace]
  refine ⟨133512831700296855104658109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178017108933729140139544145 133512831700296855104658109)
  ·
    refine ⟨50067311887611320664246791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133512831700296855104658109 50067311887611320664246791)
    ·
      refine ⟨75100967831416980996370187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50067311887611320664246791 75100967831416980996370187)
      ·
        refine ⟨112651451747125471494555281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75100967831416980996370187 112651451747125471494555281)
        ·
          refine ⟨84488588810344103620916461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112651451747125471494555281 84488588810344103620916461)
          ·
            refine ⟨31683220803879038857843673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84488588810344103620916461 31683220803879038857843673)
            ·
              refine ⟨23762415602909279143382755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31683220803879038857843673 23762415602909279143382755)
              ·
                refine ⟨35643623404363918715074133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23762415602909279143382755 35643623404363918715074133)
                ·
                  refine ⟨417698711769889672442275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35643623404363918715074133 417698711769889672442275)
                  ·
                    rfl

theorem cell23_7321188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_7321188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321188 prefixEnd_7321188 := by exact prefixLift 7321188
  have htrace : WordTrace (prefixWord ++ tailWord_7321188) baseStart_7321188 baseEnd_7321188 := by
    simpa [prefixWord, tailWord_7321188, baseEnd_7321188] using wordTrace_append hprefix tailTrace_7321188
  have hstable : (prefixWord ++ tailWord_7321188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321188).length < 2 ^ (prefixWord ++ tailWord_7321188).sum := by decide
  have hdescent : baseEnd_7321188 < baseStart_7321188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321192 : List Nat := [2, 1, 4, 3, 1, 1, 3, 1, 3, 4]
def baseStart_7321192 : Nat := 118140960795 + 7321192 * 2 ^ 59
def prefixEnd_7321192 : Nat := 4983230072969 + 3 ^ 40 * 7321192 * 2
def baseEnd_7321192 : Nat := 1253096819950541678776819

theorem tailTrace_7321192 : CollatzResearch.WordTrace tailWord_7321192 prefixEnd_7321192 1253096819950541678776819 := by
  unfold tailWord_7321192
  simp only [CollatzResearch.WordTrace]
  refine ⟨133512904646289609446230915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178017206195052812594974553 133512904646289609446230915)
  ·
    refine ⟨200269356969434414169346373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133512904646289609446230915 200269356969434414169346373)
    ·
      refine ⟨37550504431768952656752445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200269356969434414169346373 37550504431768952656752445)
      ·
        refine ⟨14081439161913357246282167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37550504431768952656752445 14081439161913357246282167)
        ·
          refine ⟨21122158742870035869423251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14081439161913357246282167 21122158742870035869423251)
          ·
            refine ⟨31683238114305053804134877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21122158742870035869423251 31683238114305053804134877)
            ·
              refine ⟨11881214292864395176550579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31683238114305053804134877 11881214292864395176550579)
              ·
                refine ⟨17821821439296592764825869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11881214292864395176550579 17821821439296592764825869)
                ·
                  refine ⟨6683183039736222286809701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17821821439296592764825869 6683183039736222286809701)
                  ·
                    refine ⟨1253096819950541678776819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6683183039736222286809701 1253096819950541678776819)
                    ·
                      rfl

theorem cell23_7321192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_7321192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321192 prefixEnd_7321192 := by exact prefixLift 7321192
  have htrace : WordTrace (prefixWord ++ tailWord_7321192) baseStart_7321192 baseEnd_7321192 := by
    simpa [prefixWord, tailWord_7321192, baseEnd_7321192] using wordTrace_append hprefix tailTrace_7321192
  have hstable : (prefixWord ++ tailWord_7321192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321192).length < 2 ^ (prefixWord ++ tailWord_7321192).sum := by decide
  have hdescent : baseEnd_7321192 < baseStart_7321192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321225 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 1, 5, 2]
def baseStart_7321225 : Nat := 118140960795 + 7321225 * 2 ^ 59
def prefixEnd_7321225 : Nat := 4983230072969 + 3 ^ 40 * 7321225 * 2
def baseEnd_7321225 : Nat := 3759307404713223407217805

theorem tailTrace_7321225 : CollatzResearch.WordTrace tailWord_7321225 prefixEnd_7321225 3759307404713223407217805 := by
  unfold tailWord_7321225
  simp only [CollatzResearch.WordTrace]
  refine ⟨267027012901459665528413129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178018008600973110352275419 267027012901459665528413129)
  ·
    refine ⟨200270259676094749146309847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267027012901459665528413129 200270259676094749146309847)
    ·
      refine ⟨300405389514142123719464771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200270259676094749146309847 300405389514142123719464771)
      ·
        refine ⟨450608084271213185579197157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300405389514142123719464771 450608084271213185579197157)
        ·
          refine ⟨84489015800852472296099467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 450608084271213185579197157 84489015800852472296099467)
          ·
            refine ⟨126733523701278708444149201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84489015800852472296099467 126733523701278708444149201)
            ·
              refine ⟨95050142775959031333111901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126733523701278708444149201 95050142775959031333111901)
              ·
                refine ⟨35643803540984636749916963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95050142775959031333111901 35643803540984636749916963)
                ·
                  refine ⟨53465705311476955124875445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35643803540984636749916963 53465705311476955124875445)
                  ·
                    refine ⟨5012409872950964542957073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53465705311476955124875445 5012409872950964542957073)
                    ·
                      refine ⟨3759307404713223407217805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5012409872950964542957073 3759307404713223407217805)
                      ·
                        rfl

theorem cell23_7321225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 5, 2].length) (baseStart_7321225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321225 prefixEnd_7321225 := by exact prefixLift 7321225
  have htrace : WordTrace (prefixWord ++ tailWord_7321225) baseStart_7321225 baseEnd_7321225 := by
    simpa [prefixWord, tailWord_7321225, baseEnd_7321225] using wordTrace_append hprefix tailTrace_7321225
  have hstable : (prefixWord ++ tailWord_7321225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321225).length < 2 ^ (prefixWord ++ tailWord_7321225).sum := by decide
  have hdescent : baseEnd_7321225 < baseStart_7321225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321286 : List Nat := [6, 1, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_7321286 : Nat := 118140960795 + 7321286 * 2 ^ 59
def prefixEnd_7321286 : Nat := 4983230072969 + 3 ^ 40 * 7321286 * 2
def baseEnd_7321286 : Nat := 1253112909011049222851675

theorem tailTrace_7321286 : CollatzResearch.WordTrace tailWord_7321286 prefixEnd_7321286 1253112909011049222851675 := by
  unfold tailWord_7321286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8344663679819958529574491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 178019491836159115297589141 8344663679819958529574491)
  ·
    refine ⟨12516995519729937794361737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8344663679819958529574491 12516995519729937794361737)
    ·
      refine ⟨9387746639797453345771303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12516995519729937794361737 9387746639797453345771303)
      ·
        refine ⟨14081619959696180018656955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9387746639797453345771303 14081619959696180018656955)
        ·
          refine ⟨21122429939544270027985433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14081619959696180018656955 21122429939544270027985433)
          ·
            refine ⟨15841822454658202520989075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21122429939544270027985433 15841822454658202520989075)
            ·
              refine ⟨23762733681987303781483613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15841822454658202520989075 23762733681987303781483613)
              ·
                refine ⟨8911025130745238918056355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23762733681987303781483613 8911025130745238918056355)
                ·
                  refine ⟨13366537696117858377084533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8911025130745238918056355 13366537696117858377084533)
                  ·
                    refine ⟨1253112909011049222851675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13366537696117858377084533 1253112909011049222851675)
                    ·
                      rfl

theorem cell23_7321286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_7321286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321286 prefixEnd_7321286 := by exact prefixLift 7321286
  have htrace : WordTrace (prefixWord ++ tailWord_7321286) baseStart_7321286 baseEnd_7321286 := by
    simpa [prefixWord, tailWord_7321286, baseEnd_7321286] using wordTrace_append hprefix tailTrace_7321286
  have hstable : (prefixWord ++ tailWord_7321286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321286).length < 2 ^ (prefixWord ++ tailWord_7321286).sum := by decide
  have hdescent : baseEnd_7321286 < baseStart_7321286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321306 : List Nat := [3, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2]
def baseStart_7321306 : Nat := 118140960795 + 7321306 * 2 ^ 59
def prefixEnd_7321306 : Nat := 4983230072969 + 3 ^ 40 * 7321306 * 2
def baseEnd_7321306 : Nat := 3759348996646237590304933

theorem tailTrace_7321306 : CollatzResearch.WordTrace tailWord_7321306 prefixEnd_7321306 3759348996646237590304933 := by
  unfold tailWord_7321306
  simp only [CollatzResearch.WordTrace]
  refine ⟨66757491803541554090527943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178019978142777477574741181 66757491803541554090527943)
  ·
    refine ⟨100136237705312331135791915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66757491803541554090527943 100136237705312331135791915)
    ·
      refine ⟨150204356557968496703687873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100136237705312331135791915 150204356557968496703687873)
      ·
        refine ⟨112653267418476372527765905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150204356557968496703687873 112653267418476372527765905)
        ·
          refine ⟨84489950563857279395824429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112653267418476372527765905 84489950563857279395824429)
          ·
            refine ⟨31683731461446479773434161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84489950563857279395824429 31683731461446479773434161)
            ·
              refine ⟨23762798596084859830075621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31683731461446479773434161 23762798596084859830075621)
              ·
                refine ⟨4455524736765911218139179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23762798596084859830075621 4455524736765911218139179)
                ·
                  refine ⟨6683287105148866827208769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4455524736765911218139179 6683287105148866827208769)
                  ·
                    refine ⟨5012465328861650120406577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6683287105148866827208769 5012465328861650120406577)
                    ·
                      refine ⟨3759348996646237590304933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5012465328861650120406577 3759348996646237590304933)
                      ·
                        rfl

theorem cell23_7321306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_7321306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321306 prefixEnd_7321306 := by exact prefixLift 7321306
  have htrace : WordTrace (prefixWord ++ tailWord_7321306) baseStart_7321306 baseEnd_7321306 := by
    simpa [prefixWord, tailWord_7321306, baseEnd_7321306] using wordTrace_append hprefix tailTrace_7321306
  have hstable : (prefixWord ++ tailWord_7321306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321306).length < 2 ^ (prefixWord ++ tailWord_7321306).sum := by decide
  have hdescent : baseEnd_7321306 < baseStart_7321306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321309 : List Nat := [1, 4, 3, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_7321309 : Nat := 118140960795 + 7321309 * 2 ^ 59
def prefixEnd_7321309 : Nat := 4983230072969 + 3 ^ 40 * 7321309 * 2
def baseEnd_7321309 : Nat := 3759350537088201078567419

theorem tailTrace_7321309 : CollatzResearch.WordTrace tailWord_7321309 prefixEnd_7321309 3759350537088201078567419 := by
  unfold tailWord_7321309
  simp only [CollatzResearch.WordTrace]
  refine ⟨267030076633155347874470981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178020051088770231916313987 267030076633155347874470981)
  ·
    refine ⟨50068139368716627726463309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267030076633155347874470981 50068139368716627726463309)
    ·
      refine ⟨18775552263268735397423741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50068139368716627726463309 18775552263268735397423741)
      ·
        refine ⟨7040832098725775774033903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18775552263268735397423741 7040832098725775774033903)
        ·
          refine ⟨10561248148088663661050855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7040832098725775774033903 10561248148088663661050855)
          ·
            refine ⟨15841872222132995491576283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10561248148088663661050855 15841872222132995491576283)
            ·
              refine ⟨23762808333199493237364425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15841872222132995491576283 23762808333199493237364425)
              ·
                refine ⟨17822106249899619928023319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23762808333199493237364425 17822106249899619928023319)
                ·
                  refine ⟨26733159374849429892034979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17822106249899619928023319 26733159374849429892034979)
                  ·
                    refine ⟨40099739062274144838052469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26733159374849429892034979 40099739062274144838052469)
                    ·
                      refine ⟨3759350537088201078567419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40099739062274144838052469 3759350537088201078567419)
                      ·
                        rfl

theorem cell23_7321309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_7321309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321309 prefixEnd_7321309 := by exact prefixLift 7321309
  have htrace : WordTrace (prefixWord ++ tailWord_7321309) baseStart_7321309 baseEnd_7321309 := by
    simpa [prefixWord, tailWord_7321309, baseEnd_7321309] using wordTrace_append hprefix tailTrace_7321309
  have hstable : (prefixWord ++ tailWord_7321309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321309).length < 2 ^ (prefixWord ++ tailWord_7321309).sum := by decide
  have hdescent : baseEnd_7321309 < baseStart_7321309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321322 : List Nat := [3, 1, 3, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_7321322 : Nat := 118140960795 + 7321322 * 2 ^ 59
def prefixEnd_7321322 : Nat := 4983230072969 + 3 ^ 40 * 7321322 * 2
def baseEnd_7321322 : Nat := 3759357212336709527704859

theorem tailTrace_7321322 : CollatzResearch.WordTrace tailWord_7321322 prefixEnd_7321322 3759357212336709527704859 := by
  unfold tailWord_7321322
  simp only [CollatzResearch.WordTrace]
  refine ⟨66757637695527062773673555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178020367188072167396462813 66757637695527062773673555)
  ·
    refine ⟨100136456543290594160510333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66757637695527062773673555 100136456543290594160510333)
    ·
      refine ⟨37551171203733972810191375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100136456543290594160510333 37551171203733972810191375)
      ·
        refine ⟨56326756805600959215287063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37551171203733972810191375 56326756805600959215287063)
        ·
          refine ⟨84490135208401438822930595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56326756805600959215287063 84490135208401438822930595)
          ·
            refine ⟨126735202812602158234395893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84490135208401438822930595 126735202812602158234395893)
            ·
              refine ⟨11881425263681452334474615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126735202812602158234395893 11881425263681452334474615)
              ·
                refine ⟨17822137895522178501711923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11881425263681452334474615 17822137895522178501711923)
                ·
                  refine ⟨26733206843283267752567885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17822137895522178501711923 26733206843283267752567885)
                  ·
                    refine ⟨10024952566231225407212957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26733206843283267752567885 10024952566231225407212957)
                    ·
                      refine ⟨3759357212336709527704859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10024952566231225407212957 3759357212336709527704859)
                      ·
                        rfl

theorem cell23_7321322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_7321322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321322 prefixEnd_7321322 := by exact prefixLift 7321322
  have htrace : WordTrace (prefixWord ++ tailWord_7321322) baseStart_7321322 baseEnd_7321322 := by
    simpa [prefixWord, tailWord_7321322, baseEnd_7321322] using wordTrace_append hprefix tailTrace_7321322
  have hstable : (prefixWord ++ tailWord_7321322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321322).length < 2 ^ (prefixWord ++ tailWord_7321322).sum := by decide
  have hdescent : baseEnd_7321322 < baseStart_7321322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321328 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 8]
def baseStart_7321328 : Nat := 118140960795 + 7321328 * 2 ^ 59
def prefixEnd_7321328 : Nat := 4983230072969 + 3 ^ 40 * 7321328 * 2
def baseEnd_7321328 : Nat := 3759360293220636504229831

theorem tailTrace_7321328 : CollatzResearch.WordTrace tailWord_7321328 prefixEnd_7321328 3759360293220636504229831 := by
  unfold tailWord_7321328
  simp only [CollatzResearch.WordTrace]
  refine ⟨133515384810043257059706319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178020513080057676079608425 133515384810043257059706319)
  ·
    refine ⟨200273077215064885589559479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133515384810043257059706319 200273077215064885589559479)
    ·
      refine ⟨300409615822597328384339219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200273077215064885589559479 300409615822597328384339219)
      ·
        refine ⟨450614423733895992576508829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300409615822597328384339219 450614423733895992576508829)
        ·
          refine ⟨168980408900210997216190811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 450614423733895992576508829 168980408900210997216190811)
          ·
            refine ⟨253470613350316495824286217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168980408900210997216190811 253470613350316495824286217)
            ·
              refine ⟨190102960012737371868214663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253470613350316495824286217 190102960012737371868214663)
              ·
                refine ⟨285154440019106057802321995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190102960012737371868214663 285154440019106057802321995)
                ·
                  refine ⟨427731660028659086703482993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285154440019106057802321995 427731660028659086703482993)
                  ·
                    refine ⟨320798745021494315027612245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 427731660028659086703482993 320798745021494315027612245)
                    ·
                      refine ⟨3759360293220636504229831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 320798745021494315027612245 3759360293220636504229831)
                      ·
                        rfl

theorem cell23_7321328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_7321328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321328 prefixEnd_7321328 := by exact prefixLift 7321328
  have htrace : WordTrace (prefixWord ++ tailWord_7321328) baseStart_7321328 baseEnd_7321328 := by
    simpa [prefixWord, tailWord_7321328, baseEnd_7321328] using wordTrace_append hprefix tailTrace_7321328
  have hstable : (prefixWord ++ tailWord_7321328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321328).length < 2 ^ (prefixWord ++ tailWord_7321328).sum := by decide
  have hdescent : baseEnd_7321328 < baseStart_7321328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321375 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 4]
def baseStart_7321375 : Nat := 118140960795 + 7321375 * 2 ^ 59
def prefixEnd_7321375 : Nat := 4983230072969 + 3 ^ 40 * 7321375 * 2
def baseEnd_7321375 : Nat := 3759384426811397820342115

theorem tailTrace_7321375 : CollatzResearch.WordTrace tailWord_7321375 prefixEnd_7321375 3759384426811397820342115 := by
  unfold tailWord_7321375
  simp only [CollatzResearch.WordTrace]
  refine ⟨267032483850916241146373579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178021655900610827430915719 267032483850916241146373579)
  ·
    refine ⟨400548725776374361719560369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267032483850916241146373579 400548725776374361719560369)
    ·
      refine ⟨300411544332280771289670277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400548725776374361719560369 300411544332280771289670277)
      ·
        refine ⟨56327164562302644616813177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300411544332280771289670277 56327164562302644616813177)
        ·
          refine ⟨42245373421726983462609883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56327164562302644616813177 42245373421726983462609883)
          ·
            refine ⟨63368060132590475193914825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42245373421726983462609883 63368060132590475193914825)
            ·
              refine ⟨47526045099442856395436119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63368060132590475193914825 47526045099442856395436119)
              ·
                refine ⟨71289067649164284593154179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47526045099442856395436119 71289067649164284593154179)
                ·
                  refine ⟨106933601473746426889731269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71289067649164284593154179 106933601473746426889731269)
                  ·
                    refine ⟨20050050276327455041824613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106933601473746426889731269 20050050276327455041824613)
                    ·
                      refine ⟨3759384426811397820342115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20050050276327455041824613 3759384426811397820342115)
                      ·
                        rfl

theorem cell23_7321375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_7321375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321375 prefixEnd_7321375 := by exact prefixLift 7321375
  have htrace : WordTrace (prefixWord ++ tailWord_7321375) baseStart_7321375 baseEnd_7321375 := by
    simpa [prefixWord, tailWord_7321375, baseEnd_7321375] using wordTrace_append hprefix tailTrace_7321375
  have hstable : (prefixWord ++ tailWord_7321375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321375).length < 2 ^ (prefixWord ++ tailWord_7321375).sum := by decide
  have hdescent : baseEnd_7321375 < baseStart_7321375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321396 : List Nat := [2, 5, 1, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_7321396 : Nat := 118140960795 + 7321396 * 2 ^ 59
def prefixEnd_7321396 : Nat := 4983230072969 + 3 ^ 40 * 7321396 * 2
def baseEnd_7321396 : Nat := 3759395209905142238179519

theorem tailTrace_7321396 : CollatzResearch.WordTrace tailWord_7321396 prefixEnd_7321396 3759395209905142238179519 := by
  unfold tailWord_7321396
  simp only [CollatzResearch.WordTrace]
  refine ⟨133516624891920080866444021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178022166522560107821925361 133516624891920080866444021)
  ·
    refine ⟨12517183583617507581229127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133516624891920080866444021 12517183583617507581229127)
    ·
      refine ⟨18775775375426261371843691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12517183583617507581229127 18775775375426261371843691)
      ·
        refine ⟨28163663063139392057765537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18775775375426261371843691 28163663063139392057765537)
        ·
          refine ⟨21122747297354544043324153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28163663063139392057765537 21122747297354544043324153)
          ·
            refine ⟨15842060473015908032493115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21122747297354544043324153 15842060473015908032493115)
            ·
              refine ⟨23763090709523862048739673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15842060473015908032493115 23763090709523862048739673)
              ·
                refine ⟨17822318032142896536554755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23763090709523862048739673 17822318032142896536554755)
                ·
                  refine ⟨26733477048214344804832133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17822318032142896536554755 26733477048214344804832133)
                  ·
                    refine ⟨5012526946540189650906025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26733477048214344804832133 5012526946540189650906025)
                    ·
                      refine ⟨3759395209905142238179519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5012526946540189650906025 3759395209905142238179519)
                      ·
                        rfl

theorem cell23_7321396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_7321396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321396 prefixEnd_7321396 := by exact prefixLift 7321396
  have htrace : WordTrace (prefixWord ++ tailWord_7321396) baseStart_7321396 baseEnd_7321396 := by
    simpa [prefixWord, tailWord_7321396, baseEnd_7321396] using wordTrace_append hprefix tailTrace_7321396
  have hstable : (prefixWord ++ tailWord_7321396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321396).length < 2 ^ (prefixWord ++ tailWord_7321396).sum := by decide
  have hdescent : baseEnd_7321396 < baseStart_7321396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321452 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 4]
def baseStart_7321452 : Nat := 118140960795 + 7321452 * 2 ^ 59
def prefixEnd_7321452 : Nat := 4983230072969 + 3 ^ 40 * 7321452 * 2
def baseEnd_7321452 : Nat := 3759423964821794019079261

theorem tailTrace_7321452 : CollatzResearch.WordTrace tailWord_7321452 prefixEnd_7321452 3759423964821794019079261 := by
  unfold tailWord_7321452
  simp only [CollatzResearch.WordTrace]
  refine ⟨133517646135818641648463305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178023528181091522197951073 133517646135818641648463305)
  ·
    refine ⟨100138234601863981236347479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133517646135818641648463305 100138234601863981236347479)
    ·
      refine ⟨150207351902795971854521219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100138234601863981236347479 150207351902795971854521219)
      ·
        refine ⟨225311027854193957781781829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150207351902795971854521219 225311027854193957781781829)
        ·
          refine ⟨42245817722661367084084093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225311027854193957781781829 42245817722661367084084093)
          ·
            refine ⟨15842181645998012656531535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42245817722661367084084093 15842181645998012656531535)
            ·
              refine ⟨23763272468997018984797303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15842181645998012656531535 23763272468997018984797303)
              ·
                refine ⟨35644908703495528477195955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23763272468997018984797303 35644908703495528477195955)
                ·
                  refine ⟨53467363055243292715793933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35644908703495528477195955 53467363055243292715793933)
                  ·
                    refine ⟨20050261145716234768422725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53467363055243292715793933 20050261145716234768422725)
                    ·
                      refine ⟨3759423964821794019079261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20050261145716234768422725 3759423964821794019079261)
                      ·
                        rfl

theorem cell23_7321452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_7321452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321452 prefixEnd_7321452 := by exact prefixLift 7321452
  have htrace : WordTrace (prefixWord ++ tailWord_7321452) baseStart_7321452 baseEnd_7321452 := by
    simpa [prefixWord, tailWord_7321452, baseEnd_7321452] using wordTrace_append hprefix tailTrace_7321452
  have hstable : (prefixWord ++ tailWord_7321452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321452).length < 2 ^ (prefixWord ++ tailWord_7321452).sum := by decide
  have hdescent : baseEnd_7321452 < baseStart_7321452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321465 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 1, 3, 6]
def baseStart_7321465 : Nat := 118140960795 + 7321465 * 2 ^ 59
def prefixEnd_7321465 : Nat := 4983230072969 + 3 ^ 40 * 7321465 * 2
def baseEnd_7321465 : Nat := 3759430640070302468216701

theorem tailTrace_7321465 : CollatzResearch.WordTrace tailWord_7321465 prefixEnd_7321465 3759430640070302468216701 := by
  unfold tailWord_7321465
  simp only [CollatzResearch.WordTrace]
  refine ⟨267035766420590186517149849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178023844280393457678099899 267035766420590186517149849)
  ·
    refine ⟨200276824815442639887862387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267035766420590186517149849 200276824815442639887862387)
    ·
      refine ⟨300415237223163959831793581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200276824815442639887862387 300415237223163959831793581)
      ·
        refine ⟨112655713958686484936922593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300415237223163959831793581 112655713958686484936922593)
        ·
          refine ⟨84491785469014863702691945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112655713958686484936922593 84491785469014863702691945)
          ·
            refine ⟨63368839101761147777018959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84491785469014863702691945 63368839101761147777018959)
            ·
              refine ⟨95053258652641721665528439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63368839101761147777018959 95053258652641721665528439)
              ·
                refine ⟨142579887978962582498292659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95053258652641721665528439 142579887978962582498292659)
                ·
                  refine ⟨213869831968443873747438989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142579887978962582498292659 213869831968443873747438989)
                  ·
                    refine ⟨80201186988166452655289621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213869831968443873747438989 80201186988166452655289621)
                    ·
                      refine ⟨3759430640070302468216701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80201186988166452655289621 3759430640070302468216701)
                      ·
                        rfl

theorem cell23_7321465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_7321465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321465 prefixEnd_7321465 := by exact prefixLift 7321465
  have htrace : WordTrace (prefixWord ++ tailWord_7321465) baseStart_7321465 baseEnd_7321465 := by
    simpa [prefixWord, tailWord_7321465, baseEnd_7321465] using wordTrace_append hprefix tailTrace_7321465
  have hstable : (prefixWord ++ tailWord_7321465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321465).length < 2 ^ (prefixWord ++ tailWord_7321465).sum := by decide
  have hdescent : baseEnd_7321465 < baseStart_7321465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321472 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 3]
def baseStart_7321472 : Nat := 118140960795 + 7321472 * 2 ^ 59
def prefixEnd_7321472 : Nat := 4983230072969 + 3 ^ 40 * 7321472 * 2
def baseEnd_7321472 : Nat := 3759434234434883940829169

theorem tailTrace_7321472 : CollatzResearch.WordTrace tailWord_7321472 prefixEnd_7321472 3759434234434883940829169 := by
  unfold tailWord_7321472
  simp only [CollatzResearch.WordTrace]
  refine ⟨133518010865782413356327335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178024014487709884475103113 133518010865782413356327335)
  ·
    refine ⟨200277016298673620034491003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133518010865782413356327335 200277016298673620034491003)
    ·
      refine ⟨300415524448010430051736505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200277016298673620034491003 300415524448010430051736505)
      ·
        refine ⟨225311643336007822538802379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300415524448010430051736505 225311643336007822538802379)
        ·
          refine ⟨337967465004011733808203569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225311643336007822538802379 337967465004011733808203569)
          ·
            refine ⟨253475598753008800356152677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337967465004011733808203569 253475598753008800356152677)
            ·
              refine ⟨47526674766189150066778627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253475598753008800356152677 47526674766189150066778627)
              ·
                refine ⟨71290012149283725100167941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47526674766189150066778627 71290012149283725100167941)
                ·
                  refine ⟨13366877277990698456281489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71290012149283725100167941 13366877277990698456281489)
                  ·
                    refine ⟨10025157958493023842211117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13366877277990698456281489 10025157958493023842211117)
                    ·
                      refine ⟨3759434234434883940829169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10025157958493023842211117 3759434234434883940829169)
                      ·
                        rfl

theorem cell23_7321472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_7321472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321472 prefixEnd_7321472 := by exact prefixLift 7321472
  have htrace : WordTrace (prefixWord ++ tailWord_7321472) baseStart_7321472 baseEnd_7321472 := by
    simpa [prefixWord, tailWord_7321472, baseEnd_7321472] using wordTrace_append hprefix tailTrace_7321472
  have hstable : (prefixWord ++ tailWord_7321472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321472).length < 2 ^ (prefixWord ++ tailWord_7321472).sum := by decide
  have hdescent : baseEnd_7321472 < baseStart_7321472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321515 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 5]
def baseStart_7321515 : Nat := 118140960795 + 7321515 * 2 ^ 59
def prefixEnd_7321515 : Nat := 4983230072969 + 3 ^ 40 * 7321515 * 2
def baseEnd_7321515 : Nat := 3759456314103027272591471

theorem tailTrace_7321515 : CollatzResearch.WordTrace tailWord_7321515 prefixEnd_7321515 3759456314103027272591471 := by
  unfold tailWord_7321515
  simp only [CollatzResearch.WordTrace]
  refine ⟨267037590070409045056469999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178025060046939363370979999 267037590070409045056469999)
  ·
    refine ⟨400556385105613567584704999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267037590070409045056469999 400556385105613567584704999)
    ·
      refine ⟨600834577658420351377057499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400556385105613567584704999 600834577658420351377057499)
      ·
        refine ⟨901251866487630527065586249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600834577658420351377057499 901251866487630527065586249)
        ·
          refine ⟨675938899865722895299189687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 901251866487630527065586249 675938899865722895299189687)
          ·
            refine ⟨1013908349798584342948784531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675938899865722895299189687 1013908349798584342948784531)
            ·
              refine ⟨1520862524697876514423176797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013908349798584342948784531 1520862524697876514423176797)
              ·
                refine ⟨570323446761703692908691299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1520862524697876514423176797 570323446761703692908691299)
                ·
                  refine ⟨855485170142555539363036949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570323446761703692908691299 855485170142555539363036949)
                  ·
                    refine ⟨40100867350432290907642357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 855485170142555539363036949 40100867350432290907642357)
                    ·
                      refine ⟨3759456314103027272591471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40100867350432290907642357 3759456314103027272591471)
                      ·
                        rfl

theorem cell23_7321515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 5].length) (baseStart_7321515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321515 prefixEnd_7321515 := by exact prefixLift 7321515
  have htrace : WordTrace (prefixWord ++ tailWord_7321515) baseStart_7321515 baseEnd_7321515 := by
    simpa [prefixWord, tailWord_7321515, baseEnd_7321515] using wordTrace_append hprefix tailTrace_7321515
  have hstable : (prefixWord ++ tailWord_7321515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321515).length < 2 ^ (prefixWord ++ tailWord_7321515).sum := by decide
  have hdescent : baseEnd_7321515 < baseStart_7321515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321579 : List Nat := [1, 1, 1, 1, 2, 3, 1, 7, 1, 2, 3]
def baseStart_7321579 : Nat := 118140960795 + 7321579 * 2 ^ 59
def prefixEnd_7321579 : Nat := 4983230072969 + 3 ^ 40 * 7321579 * 2
def baseEnd_7321579 : Nat := 3759489176864915022191177

theorem tailTrace_7321579 : CollatzResearch.WordTrace tailWord_7321579 prefixEnd_7321579 3759489176864915022191177 := by
  unfold tailWord_7321579
  simp only [CollatzResearch.WordTrace]
  refine ⟨267039924342177183986799791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178026616228118122657866527 267039924342177183986799791)
  ·
    refine ⟨400559886513265775980199687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267039924342177183986799791 400559886513265775980199687)
    ·
      refine ⟨600839829769898663970299531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400559886513265775980199687 600839829769898663970299531)
      ·
        refine ⟨901259744654847995955449297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600839829769898663970299531 901259744654847995955449297)
        ·
          refine ⟨675944808491135996966586973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 901259744654847995955449297 675944808491135996966586973)
          ·
            refine ⟨253479303184175998862470115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 675944808491135996966586973 253479303184175998862470115)
            ·
              refine ⟨380218954776263998293705173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253479303184175998862470115 380218954776263998293705173)
              ·
                refine ⟨8911381752568687460008715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 380218954776263998293705173 8911381752568687460008715)
                ·
                  refine ⟨13367072628853031190013073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8911381752568687460008715 13367072628853031190013073)
                  ·
                    refine ⟨10025304471639773392509805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13367072628853031190013073 10025304471639773392509805)
                    ·
                      refine ⟨3759489176864915022191177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10025304471639773392509805 3759489176864915022191177)
                      ·
                        rfl

theorem cell23_7321579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 2, 3].length) (baseStart_7321579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321579 prefixEnd_7321579 := by exact prefixLift 7321579
  have htrace : WordTrace (prefixWord ++ tailWord_7321579) baseStart_7321579 baseEnd_7321579 := by
    simpa [prefixWord, tailWord_7321579, baseEnd_7321579] using wordTrace_append hprefix tailTrace_7321579
  have hstable : (prefixWord ++ tailWord_7321579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321579).length < 2 ^ (prefixWord ++ tailWord_7321579).sum := by decide
  have hdescent : baseEnd_7321579 < baseStart_7321579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321582 : List Nat := [4, 1, 2, 1, 3, 12]
def baseStart_7321582 : Nat := 118140960795 + 7321582 * 2 ^ 59
def prefixEnd_7321582 : Nat := 4983230072969 + 3 ^ 40 * 7321582 * 2
def baseEnd_7321582 : Nat := 15471155215254644075941

theorem tailTrace_7321582 : CollatzResearch.WordTrace tailWord_7321582 prefixEnd_7321582 15471155215254644075941 := by
  unfold tailWord_7321582
  simp only [CollatzResearch.WordTrace]
  refine ⟨33380004220145789437394875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178026689174110876999439333 33380004220145789437394875)
  ·
    refine ⟨50070006330218684156092313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33380004220145789437394875 50070006330218684156092313)
    ·
      refine ⟨37552504747664013117069235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50070006330218684156092313 37552504747664013117069235)
      ·
        refine ⟨56328757121496019675603853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37552504747664013117069235 56328757121496019675603853)
        ·
          refine ⟨21123283920561007378351445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56328757121496019675603853 21123283920561007378351445)
          ·
            refine ⟨15471155215254644075941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 21123283920561007378351445 15471155215254644075941)
            ·
              rfl

theorem cell23_7321582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 12].length) (baseStart_7321582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321582 prefixEnd_7321582 := by exact prefixLift 7321582
  have htrace : WordTrace (prefixWord ++ tailWord_7321582) baseStart_7321582 baseEnd_7321582 := by
    simpa [prefixWord, tailWord_7321582, baseEnd_7321582] using wordTrace_append hprefix tailTrace_7321582
  have hstable : (prefixWord ++ tailWord_7321582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321582).length < 2 ^ (prefixWord ++ tailWord_7321582).sum := by decide
  have hdescent : baseEnd_7321582 < baseStart_7321582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321609 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 8, 1, 3]
def baseStart_7321609 : Nat := 118140960795 + 7321609 * 2 ^ 59
def prefixEnd_7321609 : Nat := 4983230072969 + 3 ^ 40 * 7321609 * 2
def baseEnd_7321609 : Nat := 3759504581284549904816039

theorem tailTrace_7321609 : CollatzResearch.WordTrace tailWord_7321609 prefixEnd_7321609 3759504581284549904816039 := by
  unfold tailWord_7321609
  simp only [CollatzResearch.WordTrace]
  refine ⟨267041018532068499110391881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178027345688045666073594587 267041018532068499110391881)
  ·
    refine ⟨200280763899051374332793911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267041018532068499110391881 200280763899051374332793911)
    ·
      refine ⟨300421145848577061499190867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200280763899051374332793911 300421145848577061499190867)
      ·
        refine ⟨450631718772865592248786301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300421145848577061499190867 450631718772865592248786301)
        ·
          refine ⟨168986894539824597093294863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 450631718772865592248786301 168986894539824597093294863)
          ·
            refine ⟨253480341809736895639942295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168986894539824597093294863 253480341809736895639942295)
            ·
              refine ⟨380220512714605343459913443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253480341809736895639942295 380220512714605343459913443)
              ·
                refine ⟨570330769071908015189870165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380220512714605343459913443 570330769071908015189870165)
                ·
                  refine ⟨6683563700061422053006291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 570330769071908015189870165 6683563700061422053006291)
                  ·
                    refine ⟨10025345550092133079509437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6683563700061422053006291 10025345550092133079509437)
                    ·
                      refine ⟨3759504581284549904816039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10025345550092133079509437 3759504581284549904816039)
                      ·
                        rfl

theorem cell23_7321609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 1, 3].length) (baseStart_7321609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321609 prefixEnd_7321609 := by exact prefixLift 7321609
  have htrace : WordTrace (prefixWord ++ tailWord_7321609) baseStart_7321609 baseEnd_7321609 := by
    simpa [prefixWord, tailWord_7321609, baseEnd_7321609] using wordTrace_append hprefix tailTrace_7321609
  have hstable : (prefixWord ++ tailWord_7321609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321609).length < 2 ^ (prefixWord ++ tailWord_7321609).sum := by decide
  have hdescent : baseEnd_7321609 < baseStart_7321609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321612 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 2, 7]
def baseStart_7321612 : Nat := 118140960795 + 7321612 * 2 ^ 59
def prefixEnd_7321612 : Nat := 4983230072969 + 3 ^ 40 * 7321612 * 2
def baseEnd_7321612 : Nat := 1253168707242171131026175

theorem tailTrace_7321612 : CollatzResearch.WordTrace tailWord_7321612 prefixEnd_7321612 1253168707242171131026175 := by
  unfold tailWord_7321612
  simp only [CollatzResearch.WordTrace]
  refine ⟨133520563975528815311375545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178027418634038420415167393 133520563975528815311375545)
  ·
    refine ⟨100140422981646611483531659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133520563975528815311375545 100140422981646611483531659)
    ·
      refine ⟨150210634472469917225297489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100140422981646611483531659 150210634472469917225297489)
      ·
        refine ⟨112657975854352437918973117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150210634472469917225297489 112657975854352437918973117)
        ·
          refine ⟨42246740945382164219614919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112657975854352437918973117 42246740945382164219614919)
          ·
            refine ⟨63370111418073246329422379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42246740945382164219614919 63370111418073246329422379)
            ·
              refine ⟨95055167127109869494133569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63370111418073246329422379 95055167127109869494133569)
              ·
                refine ⟨71291375345332402120600177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95055167127109869494133569 71291375345332402120600177)
                ·
                  refine ⟨53468531508999301590450133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71291375345332402120600177 53468531508999301590450133)
                  ·
                    refine ⟨1253168707242171131026175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53468531508999301590450133 1253168707242171131026175)
                    ·
                      rfl

theorem cell23_7321612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_7321612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321612 prefixEnd_7321612 := by exact prefixLift 7321612
  have htrace : WordTrace (prefixWord ++ tailWord_7321612) baseStart_7321612 baseEnd_7321612 := by
    simpa [prefixWord, tailWord_7321612, baseEnd_7321612] using wordTrace_append hprefix tailTrace_7321612
  have hstable : (prefixWord ++ tailWord_7321612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321612).length < 2 ^ (prefixWord ++ tailWord_7321612).sum := by decide
  have hdescent : baseEnd_7321612 < baseStart_7321612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321672 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 9]
def baseStart_7321672 : Nat := 118140960795 + 7321672 * 2 ^ 59
def prefixEnd_7321672 : Nat := 4983230072969 + 3 ^ 40 * 7321672 * 2
def baseEnd_7321672 : Nat := 417726325618420350925361

theorem tailTrace_7321672 : CollatzResearch.WordTrace tailWord_7321672 prefixEnd_7321672 417726325618420350925361 := by
  unfold tailWord_7321672
  simp only [CollatzResearch.WordTrace]
  refine ⟨133521658165420130434967635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178028877553893507246623513 133521658165420130434967635)
  ·
    refine ⟨200282487248130195652451453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133521658165420130434967635 200282487248130195652451453)
    ·
      refine ⟨75105932718048823369669295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200282487248130195652451453 75105932718048823369669295)
      ·
        refine ⟨112658899077073235054503943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75105932718048823369669295 112658899077073235054503943)
        ·
          refine ⟨168988348615609852581755915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112658899077073235054503943 168988348615609852581755915)
          ·
            refine ⟨253482522923414778872633873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168988348615609852581755915 253482522923414778872633873)
            ·
              refine ⟨190111892192561084154475405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253482522923414778872633873 190111892192561084154475405)
              ·
                refine ⟨71291959572210406557928277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190111892192561084154475405 71291959572210406557928277)
                ·
                  refine ⟨417726325618420350925361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71291959572210406557928277 417726325618420350925361)
                  ·
                    rfl

theorem cell23_7321672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 9].length) (baseStart_7321672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321672 prefixEnd_7321672 := by exact prefixLift 7321672
  have htrace : WordTrace (prefixWord ++ tailWord_7321672) baseStart_7321672 baseEnd_7321672 := by
    simpa [prefixWord, tailWord_7321672, baseEnd_7321672] using wordTrace_append hprefix tailTrace_7321672
  have hstable : (prefixWord ++ tailWord_7321672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321672).length < 2 ^ (prefixWord ++ tailWord_7321672).sum := by decide
  have hdescent : baseEnd_7321672 < baseStart_7321672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321699 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 3]
def baseStart_7321699 : Nat := 118140960795 + 7321699 * 2 ^ 59
def prefixEnd_7321699 : Nat := 4983230072969 + 3 ^ 40 * 7321699 * 2
def baseEnd_7321699 : Nat := 3759550794543454552690625

theorem tailTrace_7321699 : CollatzResearch.WordTrace tailWord_7321699 prefixEnd_7321699 3759550794543454552690625 := by
  unfold tailWord_7321699
  simp only [CollatzResearch.WordTrace]
  refine ⟨267044301101742444481168151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178029534067828296320778767 267044301101742444481168151)
  ·
    refine ⟨400566451652613666721752227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267044301101742444481168151 400566451652613666721752227)
    ·
      refine ⟨600849677478920500082628341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400566451652613666721752227 600849677478920500082628341)
      ·
        refine ⟨56329657263648796882746407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 600849677478920500082628341 56329657263648796882746407)
        ·
          refine ⟨84494485895473195324119611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56329657263648796882746407 84494485895473195324119611)
          ·
            refine ⟨126741728843209792986179417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84494485895473195324119611 126741728843209792986179417)
            ·
              refine ⟨95056296632407344739634563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126741728843209792986179417 95056296632407344739634563)
              ·
                refine ⟨142584444948611017109451845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95056296632407344739634563 142584444948611017109451845)
                ·
                  refine ⟨26734583427864565708022221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142584444948611017109451845 26734583427864565708022221)
                  ·
                    refine ⟨10025468785449212140508333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26734583427864565708022221 10025468785449212140508333)
                    ·
                      refine ⟨3759550794543454552690625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10025468785449212140508333 3759550794543454552690625)
                      ·
                        rfl

theorem cell23_7321699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_7321699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321699 prefixEnd_7321699 := by exact prefixLift 7321699
  have htrace : WordTrace (prefixWord ++ tailWord_7321699) baseStart_7321699 baseEnd_7321699 := by
    simpa [prefixWord, tailWord_7321699, baseEnd_7321699] using wordTrace_append hprefix tailTrace_7321699
  have hstable : (prefixWord ++ tailWord_7321699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321699).length < 2 ^ (prefixWord ++ tailWord_7321699).sum := by decide
  have hdescent : baseEnd_7321699 < baseStart_7321699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321736 : List Nat := [2, 1, 3, 4, 1, 1, 1, 3, 2, 5]
def baseStart_7321736 : Nat := 118140960795 + 7321736 * 2 ^ 59
def prefixEnd_7321736 : Nat := 4983230072969 + 3 ^ 40 * 7321736 * 2
def baseEnd_7321736 : Nat := 1253189931109223635975985

theorem tailTrace_7321736 : CollatzResearch.WordTrace tailWord_7321736 prefixEnd_7321736 1253189931109223635975985 := by
  unfold tailWord_7321736
  simp only [CollatzResearch.WordTrace]
  refine ⟨133522825301304199900132531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178030433735072266533510041 133522825301304199900132531)
  ·
    refine ⟨200284237951956299850198797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133522825301304199900132531 200284237951956299850198797)
    ·
      refine ⟨75106589231983612443824549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200284237951956299850198797 75106589231983612443824549)
      ·
        refine ⟨14082485480996927333217103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75106589231983612443824549 14082485480996927333217103)
        ·
          refine ⟨21123728221495390999825655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14082485480996927333217103 21123728221495390999825655)
          ·
            refine ⟨31685592332243086499738483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21123728221495390999825655 31685592332243086499738483)
            ·
              refine ⟨47528388498364629749607725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31685592332243086499738483 47528388498364629749607725)
              ·
                refine ⟨17823145686886736156102897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47528388498364629749607725 17823145686886736156102897)
                ·
                  refine ⟨13367359265165052117077173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17823145686886736156102897 13367359265165052117077173)
                  ·
                    refine ⟨1253189931109223635975985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13367359265165052117077173 1253189931109223635975985)
                    ·
                      rfl

theorem cell23_7321736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_7321736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321736 prefixEnd_7321736 := by exact prefixLift 7321736
  have htrace : WordTrace (prefixWord ++ tailWord_7321736) baseStart_7321736 baseEnd_7321736 := by
    simpa [prefixWord, tailWord_7321736, baseEnd_7321736] using wordTrace_append hprefix tailTrace_7321736
  have hstable : (prefixWord ++ tailWord_7321736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321736).length < 2 ^ (prefixWord ++ tailWord_7321736).sum := by decide
  have hdescent : baseEnd_7321736 < baseStart_7321736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321756 : List Nat := [2, 2, 3, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_7321756 : Nat := 118140960795 + 7321756 * 2 ^ 59
def prefixEnd_7321756 : Nat := 4983230072969 + 3 ^ 40 * 7321756 * 2
def baseEnd_7321756 : Nat := 3759580062940760829677863

theorem tailTrace_7321756 : CollatzResearch.WordTrace tailWord_7321756 prefixEnd_7321756 3759580062940760829677863 := by
  unfold tailWord_7321756
  simp only [CollatzResearch.WordTrace]
  refine ⟨133523190031267971607996561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178030920041690628810662081 133523190031267971607996561)
  ·
    refine ⟨100142392523450978705997421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133523190031267971607996561 100142392523450978705997421)
    ·
      refine ⟨37553397196294117014749033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100142392523450978705997421 37553397196294117014749033)
      ·
        refine ⟨28165047897220587761061775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37553397196294117014749033 28165047897220587761061775)
        ·
          refine ⟨42247571845830881641592663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28165047897220587761061775 42247571845830881641592663)
          ·
            refine ⟨63371357768746322462388995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42247571845830881641592663 63371357768746322462388995)
            ·
              refine ⟨95057036653119483693583493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63371357768746322462388995 95057036653119483693583493)
              ·
                refine ⟨17823194372459903192546905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95057036653119483693583493 17823194372459903192546905)
                ·
                  refine ⟨13367395779344927394410179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17823194372459903192546905 13367395779344927394410179)
                  ·
                    refine ⟨20051093669017391091615269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13367395779344927394410179 20051093669017391091615269)
                    ·
                      refine ⟨3759580062940760829677863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20051093669017391091615269 3759580062940760829677863)
                      ·
                        rfl

theorem cell23_7321756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_7321756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321756 prefixEnd_7321756 := by exact prefixLift 7321756
  have htrace : WordTrace (prefixWord ++ tailWord_7321756) baseStart_7321756 baseEnd_7321756 := by
    simpa [prefixWord, tailWord_7321756, baseEnd_7321756] using wordTrace_append hprefix tailTrace_7321756
  have hstable : (prefixWord ++ tailWord_7321756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321756).length < 2 ^ (prefixWord ++ tailWord_7321756).sum := by decide
  have hdescent : baseEnd_7321756 < baseStart_7321756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321773 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_7321773 : Nat := 118140960795 + 7321773 * 2 ^ 59
def prefixEnd_7321773 : Nat := 4983230072969 + 3 ^ 40 * 7321773 * 2
def baseEnd_7321773 : Nat := 3759588792111887263165285

theorem tailTrace_7321773 : CollatzResearch.WordTrace tailWord_7321773 prefixEnd_7321773 3759588792111887263165285 := by
  unfold tailWord_7321773
  simp only [CollatzResearch.WordTrace]
  refine ⟨267047000103474355119361973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178031333402316236746241315 267047000103474355119361973)
  ·
    refine ⟨25035656259700720792440185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267047000103474355119361973 25035656259700720792440185)
    ·
      refine ⟨18776742194775540594330139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25035656259700720792440185 18776742194775540594330139)
      ·
        refine ⟨28165113292163310891495209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18776742194775540594330139 28165113292163310891495209)
        ·
          refine ⟨21123834969122483168621407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28165113292163310891495209 21123834969122483168621407)
          ·
            refine ⟨31685752453683724752932111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21123834969122483168621407 31685752453683724752932111)
            ·
              refine ⟨47528628680525587129398167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31685752453683724752932111 47528628680525587129398167)
              ·
                refine ⟨71292943020788380694097251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47528628680525587129398167 71292943020788380694097251)
                ·
                  refine ⟨106939414531182571041145877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71292943020788380694097251 106939414531182571041145877)
                  ·
                    refine ⟨5012785056149183017553713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106939414531182571041145877 5012785056149183017553713)
                    ·
                      refine ⟨3759588792111887263165285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5012785056149183017553713 3759588792111887263165285)
                      ·
                        rfl

theorem cell23_7321773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_7321773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321773 prefixEnd_7321773 := by exact prefixLift 7321773
  have htrace : WordTrace (prefixWord ++ tailWord_7321773) baseStart_7321773 baseEnd_7321773 := by
    simpa [prefixWord, tailWord_7321773, baseEnd_7321773] using wordTrace_append hprefix tailTrace_7321773
  have hstable : (prefixWord ++ tailWord_7321773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321773).length < 2 ^ (prefixWord ++ tailWord_7321773).sum := by decide
  have hdescent : baseEnd_7321773 < baseStart_7321773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321790 : List Nat := [4, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_7321790 : Nat := 118140960795 + 7321790 * 2 ^ 59
def prefixEnd_7321790 : Nat := 4983230072969 + 3 ^ 40 * 7321790 * 2
def baseEnd_7321790 : Nat := 3759597521283013696652707

theorem tailTrace_7321790 : CollatzResearch.WordTrace tailWord_7321790 prefixEnd_7321790 3759597521283013696652707 := by
  unfold tailWord_7321790
  simp only [CollatzResearch.WordTrace]
  refine ⟨33380952518051595877841353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178031746762941844681820549 33380952518051595877841353)
  ·
    refine ⟨25035714388538696908381015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33380952518051595877841353 25035714388538696908381015)
    ·
      refine ⟨37553571582808045362571523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25035714388538696908381015 37553571582808045362571523)
      ·
        refine ⟨56330357374212068043857285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37553571582808045362571523 56330357374212068043857285)
        ·
          refine ⟨10561942007664762758223241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56330357374212068043857285 10561942007664762758223241)
          ·
            refine ⟨7921456505748572068667431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10561942007664762758223241 7921456505748572068667431)
            ·
              refine ⟨11882184758622858103001147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7921456505748572068667431 11882184758622858103001147)
              ·
                refine ⟨17823277137934287154501721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11882184758622858103001147 17823277137934287154501721)
                ·
                  refine ⟨13367457853450715365876291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17823277137934287154501721 13367457853450715365876291)
                  ·
                    refine ⟨20051186780176073048814437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13367457853450715365876291 20051186780176073048814437)
                    ·
                      refine ⟨3759597521283013696652707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20051186780176073048814437 3759597521283013696652707)
                      ·
                        rfl

theorem cell23_7321790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_7321790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321790 prefixEnd_7321790 := by exact prefixLift 7321790
  have htrace : WordTrace (prefixWord ++ tailWord_7321790) baseStart_7321790 baseEnd_7321790 := by
    simpa [prefixWord, tailWord_7321790, baseEnd_7321790] using wordTrace_append hprefix tailTrace_7321790
  have hstable : (prefixWord ++ tailWord_7321790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321790).length < 2 ^ (prefixWord ++ tailWord_7321790).sum := by decide
  have hdescent : baseEnd_7321790 < baseStart_7321790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321856 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 4, 4]
def baseStart_7321856 : Nat := 118140960795 + 7321856 * 2 ^ 59
def prefixEnd_7321856 : Nat := 4983230072969 + 3 ^ 40 * 7321856 * 2
def baseEnd_7321856 : Nat := 1253210470335403479475801

theorem tailTrace_7321856 : CollatzResearch.WordTrace tailWord_7321856 prefixEnd_7321856 1253210470335403479475801 := by
  unfold tailWord_7321856
  simp only [CollatzResearch.WordTrace]
  refine ⟨133525013681086830147316711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178033351574782440196422281 133525013681086830147316711)
  ·
    refine ⟨200287520521630245220975067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133525013681086830147316711 200287520521630245220975067)
    ·
      refine ⟨300431280782445367831462601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200287520521630245220975067 300431280782445367831462601)
      ·
        refine ⟨225323460586834025873596951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300431280782445367831462601 225323460586834025873596951)
        ·
          refine ⟨337985190880251038810395427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225323460586834025873596951 337985190880251038810395427)
          ·
            refine ⟨506977786320376558215593141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337985190880251038810395427 506977786320376558215593141)
            ·
              refine ⟨47529167467535302332711857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 506977786320376558215593141 47529167467535302332711857)
              ·
                refine ⟨35646875600651476749533893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47529167467535302332711857 35646875600651476749533893)
                ·
                  refine ⟨6683789175122151890537605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35646875600651476749533893 6683789175122151890537605)
                  ·
                    refine ⟨1253210470335403479475801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6683789175122151890537605 1253210470335403479475801)
                    ·
                      rfl

theorem cell23_7321856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 4, 4].length) (baseStart_7321856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321856 prefixEnd_7321856 := by exact prefixLift 7321856
  have htrace : WordTrace (prefixWord ++ tailWord_7321856) baseStart_7321856 baseEnd_7321856 := by
    simpa [prefixWord, tailWord_7321856, baseEnd_7321856] using wordTrace_append hprefix tailTrace_7321856
  have hstable : (prefixWord ++ tailWord_7321856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321856).length < 2 ^ (prefixWord ++ tailWord_7321856).sum := by decide
  have hdescent : baseEnd_7321856 < baseStart_7321856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321866 : List Nat := [3, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_7321866 : Nat := 118140960795 + 7321866 * 2 ^ 59
def prefixEnd_7321866 : Nat := 4983230072969 + 3 ^ 40 * 7321866 * 2
def baseEnd_7321866 : Nat := 3759636545812755399302357

theorem tailTrace_7321866 : CollatzResearch.WordTrace tailWord_7321866 prefixEnd_7321866 3759636545812755399302357 := by
  unfold tailWord_7321866
  simp only [CollatzResearch.WordTrace]
  refine ⟨66762598023034358000624363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178033594728091621334998301 66762598023034358000624363)
  ·
    refine ⟨100143897034551537000936545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66762598023034358000624363 100143897034551537000936545)
    ·
      refine ⟨75107922775913652750702409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100143897034551537000936545 75107922775913652750702409)
      ·
        refine ⟨56330942081935239563026807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75107922775913652750702409 56330942081935239563026807)
        ·
          refine ⟨84496413122902859344540211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56330942081935239563026807 84496413122902859344540211)
          ·
            refine ⟨126744619684354289016810317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84496413122902859344540211 126744619684354289016810317)
            ·
              refine ⟨47529232381632858381303869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126744619684354289016810317 47529232381632858381303869)
              ·
                refine ⟨17823462143112321892988951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47529232381632858381303869 17823462143112321892988951)
                ·
                  refine ⟨26735193214668482839483427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17823462143112321892988951 26735193214668482839483427)
                  ·
                    refine ⟨40102789822002724259225141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26735193214668482839483427 40102789822002724259225141)
                    ·
                      refine ⟨3759636545812755399302357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40102789822002724259225141 3759636545812755399302357)
                      ·
                        rfl

theorem cell23_7321866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_7321866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321866 prefixEnd_7321866 := by exact prefixLift 7321866
  have htrace : WordTrace (prefixWord ++ tailWord_7321866) baseStart_7321866 baseEnd_7321866 := by
    simpa [prefixWord, tailWord_7321866, baseEnd_7321866] using wordTrace_append hprefix tailTrace_7321866
  have hstable : (prefixWord ++ tailWord_7321866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321866).length < 2 ^ (prefixWord ++ tailWord_7321866).sum := by decide
  have hdescent : baseEnd_7321866 < baseStart_7321866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321890 : List Nat := [3, 3, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_7321890 : Nat := 118140960795 + 7321890 * 2 ^ 59
def prefixEnd_7321890 : Nat := 4983230072969 + 3 ^ 40 * 7321890 * 2
def baseEnd_7321890 : Nat := 1253216289782821101800749

theorem tailTrace_7321890 : CollatzResearch.WordTrace tailWord_7321890 prefixEnd_7321890 1253216289782821101800749 := by
  unfold tailWord_7321890
  simp only [CollatzResearch.WordTrace]
  refine ⟨66762816861012621025342781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178034178296033656067580749 66762816861012621025342781)
  ·
    refine ⟨25036056322879732884503543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66762816861012621025342781 25036056322879732884503543)
    ·
      refine ⟨37554084484319599326755315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25036056322879732884503543 37554084484319599326755315)
      ·
        refine ⟨56331126726479398990132973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37554084484319599326755315 56331126726479398990132973)
        ·
          refine ⟨21124172522429774621299865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56331126726479398990132973 21124172522429774621299865)
          ·
            refine ⟨15843129391822330965974899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21124172522429774621299865 15843129391822330965974899)
            ·
              refine ⟨23764694087733496448962349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15843129391822330965974899 23764694087733496448962349)
              ·
                refine ⟨8911760282900061168360881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23764694087733496448962349 8911760282900061168360881)
                ·
                  refine ⟨6683820212175045876270661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8911760282900061168360881 6683820212175045876270661)
                  ·
                    refine ⟨1253216289782821101800749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6683820212175045876270661 1253216289782821101800749)
                    ·
                      rfl

theorem cell23_7321890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_7321890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321890 prefixEnd_7321890 := by exact prefixLift 7321890
  have htrace : WordTrace (prefixWord ++ tailWord_7321890) baseStart_7321890 baseEnd_7321890 := by
    simpa [prefixWord, tailWord_7321890, baseEnd_7321890] using wordTrace_append hprefix tailTrace_7321890
  have hstable : (prefixWord ++ tailWord_7321890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321890).length < 2 ^ (prefixWord ++ tailWord_7321890).sum := by decide
  have hdescent : baseEnd_7321890 < baseStart_7321890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321913 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 3, 3, 3]
def baseStart_7321913 : Nat := 118140960795 + 7321913 * 2 ^ 59
def prefixEnd_7321913 : Nat := 4983230072969 + 3 ^ 40 * 7321913 * 2
def baseEnd_7321913 : Nat := 3759660679403516715414641

theorem tailTrace_7321913 : CollatzResearch.WordTrace tailWord_7321913 prefixEnd_7321913 3759660679403516715414641 := by
  unfold tailWord_7321913
  simp only [CollatzResearch.WordTrace]
  refine ⟨267052106322967159029458393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178034737548644772686305595 267052106322967159029458393)
  ·
    refine ⟨200289079742225369272093795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267052106322967159029458393 200289079742225369272093795)
    ·
      refine ⟨300433619613338053908140693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200289079742225369272093795 300433619613338053908140693)
      ·
        refine ⟨14082825919375221276944095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 300433619613338053908140693 14082825919375221276944095)
        ·
          refine ⟨21124238879062831915416143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14082825919375221276944095 21124238879062831915416143)
          ·
            refine ⟨31686358318594247873124215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21124238879062831915416143 31686358318594247873124215)
            ·
              refine ⟨47529537477891371809686323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31686358318594247873124215 47529537477891371809686323)
              ·
                refine ⟨71294306216837057714529485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47529537477891371809686323 71294306216837057714529485)
                ·
                  refine ⟨26735364831313896642948557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71294306216837057714529485 26735364831313896642948557)
                  ·
                    refine ⟨10025761811742711241105709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26735364831313896642948557 10025761811742711241105709)
                    ·
                      refine ⟨3759660679403516715414641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10025761811742711241105709 3759660679403516715414641)
                      ·
                        rfl

theorem cell23_7321913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_7321913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321913 prefixEnd_7321913 := by exact prefixLift 7321913
  have htrace : WordTrace (prefixWord ++ tailWord_7321913) baseStart_7321913 baseEnd_7321913 := by
    simpa [prefixWord, tailWord_7321913, baseEnd_7321913] using wordTrace_append hprefix tailTrace_7321913
  have hstable : (prefixWord ++ tailWord_7321913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321913).length < 2 ^ (prefixWord ++ tailWord_7321913).sum := by decide
  have hdescent : baseEnd_7321913 < baseStart_7321913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321936 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 4]
def baseStart_7321936 : Nat := 118140960795 + 7321936 * 2 ^ 59
def prefixEnd_7321936 : Nat := 4983230072969 + 3 ^ 40 * 7321936 * 2
def baseEnd_7321936 : Nat := 3759672489458570125427035

theorem tailTrace_7321936 : CollatzResearch.WordTrace tailWord_7321936 prefixEnd_7321936 3759672489458570125427035 := by
  unfold tailWord_7321936
  simp only [CollatzResearch.WordTrace]
  refine ⟨133526472600941916978772831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178035296801255889305030441 133526472600941916978772831)
  ·
    refine ⟨200289708901412875468159247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133526472600941916978772831 200289708901412875468159247)
    ·
      refine ⟨300434563352119313202238871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200289708901412875468159247 300434563352119313202238871)
      ·
        refine ⟨450651845028178969803358307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300434563352119313202238871 450651845028178969803358307)
        ·
          refine ⟨675977767542268454705037461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450651845028178969803358307 675977767542268454705037461)
          ·
            refine ⟨31686457853543833814298631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 675977767542268454705037461 31686457853543833814298631)
            ·
              refine ⟨47529686780315750721447947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31686457853543833814298631 47529686780315750721447947)
              ·
                refine ⟨71294530170473626082171921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47529686780315750721447947 71294530170473626082171921)
                ·
                  refine ⟨53470897627855219561628941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71294530170473626082171921 53470897627855219561628941)
                  ·
                    refine ⟨20051586610445707335610853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53470897627855219561628941 20051586610445707335610853)
                    ·
                      refine ⟨3759672489458570125427035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20051586610445707335610853 3759672489458570125427035)
                      ·
                        rfl

theorem cell23_7321936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_7321936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321936 prefixEnd_7321936 := by exact prefixLift 7321936
  have htrace : WordTrace (prefixWord ++ tailWord_7321936) baseStart_7321936 baseEnd_7321936 := by
    simpa [prefixWord, tailWord_7321936, baseEnd_7321936] using wordTrace_append hprefix tailTrace_7321936
  have hstable : (prefixWord ++ tailWord_7321936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321936).length < 2 ^ (prefixWord ++ tailWord_7321936).sum := by decide
  have hdescent : baseEnd_7321936 < baseStart_7321936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321940 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 3, 3, 2]
def baseStart_7321940 : Nat := 118140960795 + 7321940 * 2 ^ 59
def prefixEnd_7321940 : Nat := 4983230072969 + 3 ^ 40 * 7321940 * 2
def baseEnd_7321940 : Nat := 3759674543381188109777017

theorem tailTrace_7321940 : CollatzResearch.WordTrace tailWord_7321940 prefixEnd_7321940 3759674543381188109777017 := by
  unfold tailWord_7321940
  simp only [CollatzResearch.WordTrace]
  refine ⟨133526545546934671320345637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178035394062579561760460849 133526545546934671320345637)
  ·
    refine ⟨25036227290050250872564807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133526545546934671320345637 25036227290050250872564807)
    ·
      refine ⟨37554340935075376308847211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25036227290050250872564807 37554340935075376308847211)
      ·
        refine ⟨56331511402613064463270817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37554340935075376308847211 56331511402613064463270817)
        ·
          refine ⟨42248633551959798347453113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56331511402613064463270817 42248633551959798347453113)
          ·
            refine ⟨31686475163969848760589835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42248633551959798347453113 31686475163969848760589835)
            ·
              refine ⟨47529712745954773140884753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31686475163969848760589835 47529712745954773140884753)
              ·
                refine ⟨35647284559466079855663565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47529712745954773140884753 35647284559466079855663565)
                ·
                  refine ⟨13367731709799779945873837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35647284559466079855663565 13367731709799779945873837)
                  ·
                    refine ⟨5012899391174917479702689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13367731709799779945873837 5012899391174917479702689)
                    ·
                      refine ⟨3759674543381188109777017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5012899391174917479702689 3759674543381188109777017)
                      ·
                        rfl

theorem cell23_7321940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_7321940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321940 prefixEnd_7321940 := by exact prefixLift 7321940
  have htrace : WordTrace (prefixWord ++ tailWord_7321940) baseStart_7321940 baseEnd_7321940 := by
    simpa [prefixWord, tailWord_7321940, baseEnd_7321940] using wordTrace_append hprefix tailTrace_7321940
  have hstable : (prefixWord ++ tailWord_7321940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321940).length < 2 ^ (prefixWord ++ tailWord_7321940).sum := by decide
  have hdescent : baseEnd_7321940 < baseStart_7321940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321970 : List Nat := [3, 2, 1, 2, 1, 3, 2, 2, 1, 4, 2]
def baseStart_7321970 : Nat := 118140960795 + 7321970 * 2 ^ 59
def prefixEnd_7321970 : Nat := 4983230072969 + 3 ^ 40 * 7321970 * 2
def baseEnd_7321970 : Nat := 3759689947800822992401879

theorem tailTrace_7321970 : CollatzResearch.WordTrace tailWord_7321970 prefixEnd_7321970 3759689947800822992401879 := by
  unfold tailWord_7321970
  simp only [CollatzResearch.WordTrace]
  refine ⟨66763546320940164441070841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178036123522507105176188909 66763546320940164441070841)
  ·
    refine ⟨50072659740705123330803131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66763546320940164441070841 50072659740705123330803131)
    ·
      refine ⟨75108989611057684996204697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50072659740705123330803131 75108989611057684996204697)
      ·
        refine ⟨56331742208293263747153523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75108989611057684996204697 56331742208293263747153523)
        ·
          refine ⟨84497613312439895620730285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56331742208293263747153523 84497613312439895620730285)
          ·
            refine ⟨31686604992164960857773857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84497613312439895620730285 31686604992164960857773857)
            ·
              refine ⟨23764953744123720643330393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31686604992164960857773857 23764953744123720643330393)
              ·
                refine ⟨17823715308092790482497795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23764953744123720643330393 17823715308092790482497795)
                ·
                  refine ⟨26735572962139185723746693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17823715308092790482497795 26735572962139185723746693)
                  ·
                    refine ⟨5012919930401097323202505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26735572962139185723746693 5012919930401097323202505)
                    ·
                      refine ⟨3759689947800822992401879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5012919930401097323202505 3759689947800822992401879)
                      ·
                        rfl

theorem cell23_7321970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_7321970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321970 prefixEnd_7321970 := by exact prefixLift 7321970
  have htrace : WordTrace (prefixWord ++ tailWord_7321970) baseStart_7321970 baseEnd_7321970 := by
    simpa [prefixWord, tailWord_7321970, baseEnd_7321970] using wordTrace_append hprefix tailTrace_7321970
  have hstable : (prefixWord ++ tailWord_7321970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321970).length < 2 ^ (prefixWord ++ tailWord_7321970).sum := by decide
  have hdescent : baseEnd_7321970 < baseStart_7321970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321987 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 4, 2, 2]
def baseStart_7321987 : Nat := 118140960795 + 7321987 * 2 ^ 59
def prefixEnd_7321987 : Nat := 4983230072969 + 3 ^ 40 * 7321987 * 2
def baseEnd_7321987 : Nat := 3759698676971949425889301

theorem tailTrace_7321987 : CollatzResearch.WordTrace tailWord_7321987 prefixEnd_7321987 3759698676971949425889301 := by
  unfold tailWord_7321987
  simp only [CollatzResearch.WordTrace]
  refine ⟨267054805324699069667652215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178036536883132713111768143 267054805324699069667652215)
  ·
    refine ⟨400582207987048604501478323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267054805324699069667652215 400582207987048604501478323)
    ·
      refine ⟨600873311980572906752217485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400582207987048604501478323 600873311980572906752217485)
      ·
        refine ⟨225327491992714840032081557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 600873311980572906752217485 225327491992714840032081557)
        ·
          refine ⟨10562226187158508126503823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 225327491992714840032081557 10562226187158508126503823)
          ·
            refine ⟨15843339280737762189755735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10562226187158508126503823 15843339280737762189755735)
            ·
              refine ⟨23765008921106643284633603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15843339280737762189755735 23765008921106643284633603)
              ·
                refine ⟨35647513381659964926950405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23765008921106643284633603 35647513381659964926950405)
                ·
                  refine ⟨6683908759061243423803201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35647513381659964926950405 6683908759061243423803201)
                  ·
                    refine ⟨5012931569295932567852401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6683908759061243423803201 5012931569295932567852401)
                    ·
                      refine ⟨3759698676971949425889301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5012931569295932567852401 3759698676971949425889301)
                      ·
                        rfl

theorem cell23_7321987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 2, 2].length) (baseStart_7321987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321987 prefixEnd_7321987 := by exact prefixLift 7321987
  have htrace : WordTrace (prefixWord ++ tailWord_7321987) baseStart_7321987 baseEnd_7321987 := by
    simpa [prefixWord, tailWord_7321987, baseEnd_7321987] using wordTrace_append hprefix tailTrace_7321987
  have hstable : (prefixWord ++ tailWord_7321987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321987).length < 2 ^ (prefixWord ++ tailWord_7321987).sum := by decide
  have hdescent : baseEnd_7321987 < baseStart_7321987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7321993 : List Nat := [1, 2, 1, 1, 6, 2, 2, 1, 7]
def baseStart_7321993 : Nat := 118140960795 + 7321993 * 2 ^ 59
def prefixEnd_7321993 : Nat := 4983230072969 + 3 ^ 40 * 7321993 * 2
def baseEnd_7321993 : Nat := 417744639761764044712697

theorem tailTrace_7321993 : CollatzResearch.WordTrace tailWord_7321993 prefixEnd_7321993 417744639761764044712697 := by
  unfold tailWord_7321993
  simp only [CollatzResearch.WordTrace]
  refine ⟨267055024162677332692370633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178036682775118221794913755 267055024162677332692370633)
  ·
    refine ⟨200291268122007999519277975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267055024162677332692370633 200291268122007999519277975)
    ·
      refine ⟨300436902183011999278916963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200291268122007999519277975 300436902183011999278916963)
      ·
        refine ⟨450655353274517998918375445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300436902183011999278916963 450655353274517998918375445)
        ·
          refine ⟨21124469684743031199298849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 450655353274517998918375445 21124469684743031199298849)
          ·
            refine ⟨15843352263557273399474137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21124469684743031199298849 15843352263557273399474137)
            ·
              refine ⟨11882514197667955049605603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15843352263557273399474137 11882514197667955049605603)
              ·
                refine ⟨17823771296501932574408405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11882514197667955049605603 17823771296501932574408405)
                ·
                  refine ⟨417744639761764044712697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17823771296501932574408405 417744639761764044712697)
                  ·
                    rfl

theorem cell23_7321993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 7].length) (baseStart_7321993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7321993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7321993 prefixEnd_7321993 := by exact prefixLift 7321993
  have htrace : WordTrace (prefixWord ++ tailWord_7321993) baseStart_7321993 baseEnd_7321993 := by
    simpa [prefixWord, tailWord_7321993, baseEnd_7321993] using wordTrace_append hprefix tailTrace_7321993
  have hstable : (prefixWord ++ tailWord_7321993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7321993).length < 2 ^ (prefixWord ++ tailWord_7321993).sum := by decide
  have hdescent : baseEnd_7321993 < baseStart_7321993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7321993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322004 : List Nat := [2, 4, 2, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_7322004 : Nat := 118140960795 + 7322004 * 2 ^ 59
def prefixEnd_7322004 : Nat := 4983230072969 + 3 ^ 40 * 7322004 * 2
def baseEnd_7322004 : Nat := 3759707406143075859376723

theorem tailTrace_7322004 : CollatzResearch.WordTrace tailWord_7322004 prefixEnd_7322004 3759707406143075859376723 := by
  unfold tailWord_7322004
  simp only [CollatzResearch.WordTrace]
  refine ⟨133527712682818740785510533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178036950243758321047347377 133527712682818740785510533)
  ·
    refine ⟨25036446128028513897283225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133527712682818740785510533 25036446128028513897283225)
    ·
      refine ⟨18777334596021385422962419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25036446128028513897283225 18777334596021385422962419)
      ·
        refine ⟨28166001894032078134443629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18777334596021385422962419 28166001894032078134443629)
        ·
          refine ⟨10562250710262029300416361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28166001894032078134443629 10562250710262029300416361)
          ·
            refine ⟨7921688032696521975312271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10562250710262029300416361 7921688032696521975312271)
            ·
              refine ⟨11882532049044782962968407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7921688032696521975312271 11882532049044782962968407)
              ·
                refine ⟨17823798073567174444452611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11882532049044782962968407 17823798073567174444452611)
                ·
                  refine ⟨26735697110350761666678917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17823798073567174444452611 26735697110350761666678917)
                  ·
                    refine ⟨5012943208190767812502297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26735697110350761666678917 5012943208190767812502297)
                    ·
                      refine ⟨3759707406143075859376723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5012943208190767812502297 3759707406143075859376723)
                      ·
                        rfl

theorem cell23_7322004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_7322004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322004 prefixEnd_7322004 := by exact prefixLift 7322004
  have htrace : WordTrace (prefixWord ++ tailWord_7322004) baseStart_7322004 baseEnd_7322004 := by
    simpa [prefixWord, tailWord_7322004, baseEnd_7322004] using wordTrace_append hprefix tailTrace_7322004
  have hstable : (prefixWord ++ tailWord_7322004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322004).length < 2 ^ (prefixWord ++ tailWord_7322004).sum := by decide
  have hdescent : baseEnd_7322004 < baseStart_7322004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322023 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 1, 7]
def baseStart_7322023 : Nat := 118140960795 + 7322023 * 2 ^ 59
def prefixEnd_7322023 : Nat := 4983230072969 + 3 ^ 40 * 7322023 * 2
def baseEnd_7322023 : Nat := 1253239054091837095013045

theorem tailTrace_7322023 : CollatzResearch.WordTrace tailWord_7322023 prefixEnd_7322023 1253239054091837095013045 := by
  unfold tailWord_7322023
  simp only [CollatzResearch.WordTrace]
  refine ⟨267056118352568647815962723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178037412235045765210641815 267056118352568647815962723)
  ·
    refine ⟨400584177528852971723944085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267056118352568647815962723 400584177528852971723944085)
    ·
      refine ⟨18777383321664983049559879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 400584177528852971723944085 18777383321664983049559879)
      ·
        refine ⟨28166074982497474574339819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18777383321664983049559879 28166074982497474574339819)
        ·
          refine ⟨42249112473746211861509729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28166074982497474574339819 42249112473746211861509729)
          ·
            refine ⟨31686834355309658896132297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42249112473746211861509729 31686834355309658896132297)
            ·
              refine ⟨23765125766482244172099223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31686834355309658896132297 23765125766482244172099223)
              ·
                refine ⟨35647688649723366258148835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23765125766482244172099223 35647688649723366258148835)
                ·
                  refine ⟨53471532974585049387223253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35647688649723366258148835 53471532974585049387223253)
                  ·
                    refine ⟨1253239054091837095013045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53471532974585049387223253 1253239054091837095013045)
                    ·
                      rfl

theorem cell23_7322023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_7322023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322023 prefixEnd_7322023 := by exact prefixLift 7322023
  have htrace : WordTrace (prefixWord ++ tailWord_7322023) baseStart_7322023 baseEnd_7322023 := by
    simpa [prefixWord, tailWord_7322023, baseEnd_7322023] using wordTrace_append hprefix tailTrace_7322023
  have hstable : (prefixWord ++ tailWord_7322023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322023).length < 2 ^ (prefixWord ++ tailWord_7322023).sum := by decide
  have hdescent : baseEnd_7322023 < baseStart_7322023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322043 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 5, 6, 2]
def baseStart_7322043 : Nat := 118140960795 + 7322043 * 2 ^ 59
def prefixEnd_7322043 : Nat := 4983230072969 + 3 ^ 40 * 7322043 * 2
def baseEnd_7322043 : Nat := 3759727431888601206789043

theorem tailTrace_7322043 : CollatzResearch.WordTrace tailWord_7322043 prefixEnd_7322043 3759727431888601206789043 := by
  unfold tailWord_7322043
  simp only [CollatzResearch.WordTrace]
  refine ⟨267056847812496191231690783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178037898541664127487793855 267056847812496191231690783)
  ·
    refine ⟨400585271718744286847536175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267056847812496191231690783 400585271718744286847536175)
    ·
      refine ⟨600877907578116430271304263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400585271718744286847536175 600877907578116430271304263)
      ·
        refine ⟨901316861367174645406956395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600877907578116430271304263 901316861367174645406956395)
        ·
          refine ⟨1351975292050761968110434593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901316861367174645406956395 1351975292050761968110434593)
          ·
            refine ⟨1013981469038071476082825945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1351975292050761968110434593 1013981469038071476082825945)
            ·
              refine ⟨760486101778553607062119459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1013981469038071476082825945 760486101778553607062119459)
              ·
                refine ⟨1140729152667830410593179189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760486101778553607062119459 1140729152667830410593179189)
                ·
                  refine ⟨106943358062609100993110549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1140729152667830410593179189 106943358062609100993110549)
                  ·
                    refine ⟨5012969909184801609052057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106943358062609100993110549 5012969909184801609052057)
                    ·
                      refine ⟨3759727431888601206789043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5012969909184801609052057 3759727431888601206789043)
                      ·
                        rfl

theorem cell23_7322043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 6, 2].length) (baseStart_7322043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322043 prefixEnd_7322043 := by exact prefixLift 7322043
  have htrace : WordTrace (prefixWord ++ tailWord_7322043) baseStart_7322043 baseEnd_7322043 := by
    simpa [prefixWord, tailWord_7322043, baseEnd_7322043] using wordTrace_append hprefix tailTrace_7322043
  have hstable : (prefixWord ++ tailWord_7322043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322043).length < 2 ^ (prefixWord ++ tailWord_7322043).sum := by decide
  have hdescent : baseEnd_7322043 < baseStart_7322043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322063 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 3]
def baseStart_7322063 : Nat := 118140960795 + 7322063 * 2 ^ 59
def prefixEnd_7322063 : Nat := 4983230072969 + 3 ^ 40 * 7322063 * 2
def baseEnd_7322063 : Nat := 3759737701501691128538951

theorem tailTrace_7322063 : CollatzResearch.WordTrace tailWord_7322063 prefixEnd_7322063 3759737701501691128538951 := by
  unfold tailWord_7322063
  simp only [CollatzResearch.WordTrace]
  refine ⟨267057577272423734647418843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178038384848282489764945895 267057577272423734647418843)
  ·
    refine ⟨400586365908635601971128265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267057577272423734647418843 400586365908635601971128265)
    ·
      refine ⟨300439774431476701478346199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400586365908635601971128265 300439774431476701478346199)
      ·
        refine ⟨450659661647215052217519299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300439774431476701478346199 450659661647215052217519299)
        ·
          refine ⟨675989492470822578326278949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450659661647215052217519299 675989492470822578326278949)
          ·
            refine ⟨126748029838279233436177303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 675989492470822578326278949 126748029838279233436177303)
            ·
              refine ⟨190122044757418850154265955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126748029838279233436177303 190122044757418850154265955)
              ·
                refine ⟨285183067136128275231398933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190122044757418850154265955 285183067136128275231398933)
                ·
                  refine ⟨13367956272006012901471825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 285183067136128275231398933 13367956272006012901471825)
                  ·
                    refine ⟨10025967204004509676103869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13367956272006012901471825 10025967204004509676103869)
                    ·
                      refine ⟨3759737701501691128538951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10025967204004509676103869 3759737701501691128538951)
                      ·
                        rfl

theorem cell23_7322063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 3].length) (baseStart_7322063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322063 prefixEnd_7322063 := by exact prefixLift 7322063
  have htrace : WordTrace (prefixWord ++ tailWord_7322063) baseStart_7322063 baseEnd_7322063 := by
    simpa [prefixWord, tailWord_7322063, baseEnd_7322063] using wordTrace_append hprefix tailTrace_7322063
  have hstable : (prefixWord ++ tailWord_7322063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322063).length < 2 ^ (prefixWord ++ tailWord_7322063).sum := by decide
  have hdescent : baseEnd_7322063 < baseStart_7322063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322080 : List Nat := [2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 3]
def baseStart_7322080 : Nat := 118140960795 + 7322080 * 2 ^ 59
def prefixEnd_7322080 : Nat := 4983230072969 + 3 ^ 40 * 7322080 * 2
def baseEnd_7322080 : Nat := 3759746430672817562026373

theorem tailTrace_7322080 : CollatzResearch.WordTrace tailWord_7322080 prefixEnd_7322080 3759746430672817562026373 := by
  unfold tailWord_7322080
  simp only [CollatzResearch.WordTrace]
  refine ⟨133529098656681073275393847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178038798208908097700525129 133529098656681073275393847)
  ·
    refine ⟨200293647985021609913090771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133529098656681073275393847 200293647985021609913090771)
    ·
      refine ⟨300440471977532414869636157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200293647985021609913090771 300440471977532414869636157)
      ·
        refine ⟨112665176991574655576113559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300440471977532414869636157 112665176991574655576113559)
        ·
          refine ⟨168997765487361983364170339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112665176991574655576113559 168997765487361983364170339)
          ·
            refine ⟨253496648231042975046255509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168997765487361983364170339 253496648231042975046255509)
            ·
              refine ⟨11882655385830139455293227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 253496648231042975046255509 11882655385830139455293227)
              ·
                refine ⟨17823983078745209182939841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11882655385830139455293227 17823983078745209182939841)
                ·
                  refine ⟨13367987309058906887204881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17823983078745209182939841 13367987309058906887204881)
                  ·
                    refine ⟨10025990481794180165403661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13367987309058906887204881 10025990481794180165403661)
                    ·
                      refine ⟨3759746430672817562026373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10025990481794180165403661 3759746430672817562026373)
                      ·
                        rfl

theorem cell23_7322080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_7322080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322080 prefixEnd_7322080 := by exact prefixLift 7322080
  have htrace : WordTrace (prefixWord ++ tailWord_7322080) baseStart_7322080 baseEnd_7322080 := by
    simpa [prefixWord, tailWord_7322080, baseEnd_7322080] using wordTrace_append hprefix tailTrace_7322080
  have hstable : (prefixWord ++ tailWord_7322080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322080).length < 2 ^ (prefixWord ++ tailWord_7322080).sum := by decide
  have hdescent : baseEnd_7322080 < baseStart_7322080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322087 : List Nat := [1, 1, 5, 2, 1, 1, 2, 5, 1, 4]
def baseStart_7322087 : Nat := 118140960795 + 7322087 * 2 ^ 59
def prefixEnd_7322087 : Nat := 4983230072969 + 3 ^ 40 * 7322087 * 2
def baseEnd_7322087 : Nat := 1253250008345799678212947

theorem tailTrace_7322087 : CollatzResearch.WordTrace tailWord_7322087 prefixEnd_7322087 1253250008345799678212947 := by
  unfold tailWord_7322087
  simp only [CollatzResearch.WordTrace]
  refine ⟨267058452624336786746292515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178038968416224524497528343 267058452624336786746292515)
  ·
    refine ⟨400587678936505180119438773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267058452624336786746292515 400587678936505180119438773)
    ·
      refine ⟨37555094900297360636197385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 400587678936505180119438773 37555094900297360636197385)
      ·
        refine ⟨28166321175223020477148039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37555094900297360636197385 28166321175223020477148039)
        ·
          refine ⟨42249481762834530715722059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28166321175223020477148039 42249481762834530715722059)
          ·
            refine ⟨63374222644251796073583089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42249481762834530715722059 63374222644251796073583089)
            ·
              refine ⟨47530666983188847055187317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63374222644251796073583089 47530666983188847055187317)
              ·
                refine ⟨4456000029673954411423811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47530666983188847055187317 4456000029673954411423811)
                ·
                  refine ⟨6684000044510931617135717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4456000029673954411423811 6684000044510931617135717)
                  ·
                    refine ⟨1253250008345799678212947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6684000044510931617135717 1253250008345799678212947)
                    ·
                      rfl

theorem cell23_7322087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_7322087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322087 prefixEnd_7322087 := by exact prefixLift 7322087
  have htrace : WordTrace (prefixWord ++ tailWord_7322087) baseStart_7322087 baseEnd_7322087 := by
    simpa [prefixWord, tailWord_7322087, baseEnd_7322087] using wordTrace_append hprefix tailTrace_7322087
  have hstable : (prefixWord ++ tailWord_7322087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322087).length < 2 ^ (prefixWord ++ tailWord_7322087).sum := by decide
  have hdescent : baseEnd_7322087 < baseStart_7322087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322120 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 1, 5, 2]
def baseStart_7322120 : Nat := 118140960795 + 7322120 * 2 ^ 59
def prefixEnd_7322120 : Nat := 4983230072969 + 3 ^ 40 * 7322120 * 2
def baseEnd_7322120 : Nat := 3759766969898997405526189

theorem tailTrace_7322120 : CollatzResearch.WordTrace tailWord_7322120 prefixEnd_7322120 3759766969898997405526189 := by
  unfold tailWord_7322120
  simp only [CollatzResearch.WordTrace]
  refine ⟨133529828116608616691121907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178039770822144822254829209 133529828116608616691121907)
  ·
    refine ⟨200294742174912925036682861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133529828116608616691121907 200294742174912925036682861)
    ·
      refine ⟨75110528315592346888756073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200294742174912925036682861 75110528315592346888756073)
      ·
        refine ⟨56332896236694260166567055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75110528315592346888756073 56332896236694260166567055)
        ·
          refine ⟨84499344355041390249850583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56332896236694260166567055 84499344355041390249850583)
          ·
            refine ⟨126749016532562085374775875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84499344355041390249850583 126749016532562085374775875)
            ·
              refine ⟨190123524798843128062163813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126749016532562085374775875 190123524798843128062163813)
              ·
                refine ⟨35648160899783086511655715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190123524798843128062163813 35648160899783086511655715)
                ·
                  refine ⟨53472241349674629767483573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35648160899783086511655715 53472241349674629767483573)
                  ·
                    refine ⟨5013022626531996540701585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53472241349674629767483573 5013022626531996540701585)
                    ·
                      refine ⟨3759766969898997405526189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5013022626531996540701585 3759766969898997405526189)
                      ·
                        rfl

theorem cell23_7322120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_7322120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322120 prefixEnd_7322120 := by exact prefixLift 7322120
  have htrace : WordTrace (prefixWord ++ tailWord_7322120) baseStart_7322120 baseEnd_7322120 := by
    simpa [prefixWord, tailWord_7322120, baseEnd_7322120] using wordTrace_append hprefix tailTrace_7322120
  have hstable : (prefixWord ++ tailWord_7322120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322120).length < 2 ^ (prefixWord ++ tailWord_7322120).sum := by decide
  have hdescent : baseEnd_7322120 < baseStart_7322120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322147 : List Nat := [1, 1, 1, 4, 4, 1, 4, 1, 1, 5]
def baseStart_7322147 : Nat := 118140960795 + 7322147 * 2 ^ 59
def prefixEnd_7322147 : Nat := 4983230072969 + 3 ^ 40 * 7322147 * 2
def baseEnd_7322147 : Nat := 1253260277958889599962855

theorem tailTrace_7322147 : CollatzResearch.WordTrace tailWord_7322147 prefixEnd_7322147 1253260277958889599962855 := by
  unfold tailWord_7322147
  simp only [CollatzResearch.WordTrace]
  refine ⟨267060641004119416993476695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178040427336079611328984463 267060641004119416993476695)
  ·
    refine ⟨400590961506179125490215043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267060641004119416993476695 400590961506179125490215043)
    ·
      refine ⟨600886442259268688235322565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400590961506179125490215043 600886442259268688235322565)
      ·
        refine ⟨112666207923612879044122981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 600886442259268688235322565 112666207923612879044122981)
        ·
          refine ⟨21124913985677414820773059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112666207923612879044122981 21124913985677414820773059)
          ·
            refine ⟨31687370978516122231159589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21124913985677414820773059 31687370978516122231159589)
            ·
              refine ⟨5941382058471772918342423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31687370978516122231159589 5941382058471772918342423)
              ·
                refine ⟨8912073087707659377513635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5941382058471772918342423 8912073087707659377513635)
                ·
                  refine ⟨13368109631561489066270453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8912073087707659377513635 13368109631561489066270453)
                  ·
                    refine ⟨1253260277958889599962855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13368109631561489066270453 1253260277958889599962855)
                    ·
                      rfl

theorem cell23_7322147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 1, 5].length) (baseStart_7322147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322147 prefixEnd_7322147 := by exact prefixLift 7322147
  have htrace : WordTrace (prefixWord ++ tailWord_7322147) baseStart_7322147 baseEnd_7322147 := by
    simpa [prefixWord, tailWord_7322147, baseEnd_7322147] using wordTrace_append hprefix tailTrace_7322147
  have hstable : (prefixWord ++ tailWord_7322147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322147).length < 2 ^ (prefixWord ++ tailWord_7322147).sum := by decide
  have hdescent : baseEnd_7322147 < baseStart_7322147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322151 : List Nat := [1, 1, 7, 2, 2, 1, 1, 2, 6]
def baseStart_7322151 : Nat := 118140960795 + 7322151 * 2 ^ 59
def prefixEnd_7322151 : Nat := 4983230072969 + 3 ^ 40 * 7322151 * 2
def baseEnd_7322151 : Nat := 417753654199920753804283

theorem tailTrace_7322151 : CollatzResearch.WordTrace tailWord_7322151 prefixEnd_7322151 417753654199920753804283 := by
  unfold tailWord_7322151
  simp only [CollatzResearch.WordTrace]
  refine ⟨267060786896104925676622307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178040524597403283784414871 267060786896104925676622307)
  ·
    refine ⟨400591180344157388514933461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267060786896104925676622307 400591180344157388514933461)
    ·
      refine ⟨9388855789316188793318753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 400591180344157388514933461 9388855789316188793318753)
      ·
        refine ⟨7041641841987141594989065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9388855789316188793318753 7041641841987141594989065)
        ·
          refine ⟨5281231381490356196241799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7041641841987141594989065 5281231381490356196241799)
          ·
            refine ⟨7921847072235534294362699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5281231381490356196241799 7921847072235534294362699)
            ·
              refine ⟨11882770608353301441544049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7921847072235534294362699 11882770608353301441544049)
              ·
                refine ⟨8912077956264976081158037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11882770608353301441544049 8912077956264976081158037)
                ·
                  refine ⟨417753654199920753804283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8912077956264976081158037 417753654199920753804283)
                  ·
                    rfl

theorem cell23_7322151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 6].length) (baseStart_7322151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322151 prefixEnd_7322151 := by exact prefixLift 7322151
  have htrace : WordTrace (prefixWord ++ tailWord_7322151) baseStart_7322151 baseEnd_7322151 := by
    simpa [prefixWord, tailWord_7322151, baseEnd_7322151] using wordTrace_append hprefix tailTrace_7322151
  have hstable : (prefixWord ++ tailWord_7322151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322151).length < 2 ^ (prefixWord ++ tailWord_7322151).sum := by decide
  have hdescent : baseEnd_7322151 < baseStart_7322151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322163 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 6]
def baseStart_7322163 : Nat := 118140960795 + 7322163 * 2 ^ 59
def prefixEnd_7322163 : Nat := 4983230072969 + 3 ^ 40 * 7322163 * 2
def baseEnd_7322163 : Nat := 3759789049567140737288491

theorem tailTrace_7322163 : CollatzResearch.WordTrace tailWord_7322163 prefixEnd_7322163 3759789049567140737288491 := by
  unfold tailWord_7322163
  simp only [CollatzResearch.WordTrace]
  refine ⟨267061224572061451726059143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178040816381374301150706095 267061224572061451726059143)
  ·
    refine ⟨400591836858092177589088715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267061224572061451726059143 400591836858092177589088715)
    ·
      refine ⟨600887755287138266383633073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400591836858092177589088715 600887755287138266383633073)
      ·
        refine ⟨450665816465353699787724805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600887755287138266383633073 450665816465353699787724805)
        ·
          refine ⟨84499840587253818710198401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 450665816465353699787724805 84499840587253818710198401)
          ·
            refine ⟨63374880440440364032648801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84499840587253818710198401 63374880440440364032648801)
            ·
              refine ⟨47531160330330273024486601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63374880440440364032648801 47531160330330273024486601)
              ·
                refine ⟨35648370247747704768364951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47531160330330273024486601 35648370247747704768364951)
                ·
                  refine ⟨53472555371621557152547427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35648370247747704768364951 53472555371621557152547427)
                  ·
                    refine ⟨80208833057432335728821141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53472555371621557152547427 80208833057432335728821141)
                    ·
                      refine ⟨3759789049567140737288491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80208833057432335728821141 3759789049567140737288491)
                      ·
                        rfl

theorem cell23_7322163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_7322163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322163 prefixEnd_7322163 := by exact prefixLift 7322163
  have htrace : WordTrace (prefixWord ++ tailWord_7322163) baseStart_7322163 baseEnd_7322163 := by
    simpa [prefixWord, tailWord_7322163, baseEnd_7322163] using wordTrace_append hprefix tailTrace_7322163
  have hstable : (prefixWord ++ tailWord_7322163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322163).length < 2 ^ (prefixWord ++ tailWord_7322163).sum := by decide
  have hdescent : baseEnd_7322163 < baseStart_7322163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322170 : List Nat := [3, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5]
def baseStart_7322170 : Nat := 118140960795 + 7322170 * 2 ^ 59
def prefixEnd_7322170 : Nat := 4983230072969 + 3 ^ 40 * 7322170 * 2
def baseEnd_7322170 : Nat := 3759792643931722209900959

theorem tailTrace_7322170 : CollatzResearch.WordTrace tailWord_7322170 prefixEnd_7322170 3759792643931722209900959 := by
  unfold tailWord_7322170
  simp only [CollatzResearch.WordTrace]
  refine ⟨66765369970759022980390991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178040986588690727947709309 66765369970759022980390991)
  ·
    refine ⟨100148054956138534470586487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66765369970759022980390991 100148054956138534470586487)
    ·
      refine ⟨150222082434207801705879731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100148054956138534470586487 150222082434207801705879731)
      ·
        refine ⟨225333123651311702558819597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150222082434207801705879731 225333123651311702558819597)
        ·
          refine ⟨84499921369241888459557349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225333123651311702558819597 84499921369241888459557349)
          ·
            refine ⟨15843735256732854086167003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84499921369241888459557349 15843735256732854086167003)
            ·
              refine ⟨23765602885099281129250505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15843735256732854086167003 23765602885099281129250505)
              ·
                refine ⟨17824202163824460846937879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23765602885099281129250505 17824202163824460846937879)
                ·
                  refine ⟨26736303245736691270406819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17824202163824460846937879 26736303245736691270406819)
                  ·
                    refine ⟨40104454868605036905610229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26736303245736691270406819 40104454868605036905610229)
                    ·
                      refine ⟨3759792643931722209900959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40104454868605036905610229 3759792643931722209900959)
                      ·
                        rfl

theorem cell23_7322170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_7322170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322170 prefixEnd_7322170 := by exact prefixLift 7322170
  have htrace : WordTrace (prefixWord ++ tailWord_7322170) baseStart_7322170 baseEnd_7322170 := by
    simpa [prefixWord, tailWord_7322170, baseEnd_7322170] using wordTrace_append hprefix tailTrace_7322170
  have hstable : (prefixWord ++ tailWord_7322170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322170).length < 2 ^ (prefixWord ++ tailWord_7322170).sum := by decide
  have hdescent : baseEnd_7322170 < baseStart_7322170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322177 : List Nat := [1, 2, 5, 1, 1, 4, 1, 1, 1, 6]
def baseStart_7322177 : Nat := 118140960795 + 7322177 * 2 ^ 59
def prefixEnd_7322177 : Nat := 4983230072969 + 3 ^ 40 * 7322177 * 2
def baseEnd_7322177 : Nat := 1253265412765434560837809

theorem tailTrace_7322177 : CollatzResearch.WordTrace tailWord_7322177 prefixEnd_7322177 1253265412765434560837809 := by
  unfold tailWord_7322177
  simp only [CollatzResearch.WordTrace]
  refine ⟨267061735194010732117068785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178041156796007154744712523 267061735194010732117068785)
  ·
    refine ⟨200296301395508049087801589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267061735194010732117068785 200296301395508049087801589)
    ·
      refine ⟨18777778255828879601981399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200296301395508049087801589 18777778255828879601981399)
      ·
        refine ⟨28166667383743319402972099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18777778255828879601981399 28166667383743319402972099)
        ·
          refine ⟨42250001075614979104458149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28166667383743319402972099 42250001075614979104458149)
          ·
            refine ⟨7921875201677808582085903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42250001075614979104458149 7921875201677808582085903)
            ·
              refine ⟨11882812802516712873128855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7921875201677808582085903 11882812802516712873128855)
              ·
                refine ⟨17824219203775069309693283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11882812802516712873128855 17824219203775069309693283)
                ·
                  refine ⟨26736328805662603964539925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17824219203775069309693283 26736328805662603964539925)
                  ·
                    refine ⟨1253265412765434560837809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26736328805662603964539925 1253265412765434560837809)
                    ·
                      rfl

theorem cell23_7322177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_7322177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322177 prefixEnd_7322177 := by exact prefixLift 7322177
  have htrace : WordTrace (prefixWord ++ tailWord_7322177) baseStart_7322177 baseEnd_7322177 := by
    simpa [prefixWord, tailWord_7322177, baseEnd_7322177] using wordTrace_append hprefix tailTrace_7322177
  have hstable : (prefixWord ++ tailWord_7322177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322177).length < 2 ^ (prefixWord ++ tailWord_7322177).sum := by decide
  have hdescent : baseEnd_7322177 < baseStart_7322177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322190 : List Nat := [4, 1, 1, 1, 1, 2, 6, 7]
def baseStart_7322190 : Nat := 118140960795 + 7322190 * 2 ^ 59
def prefixEnd_7322190 : Nat := 4983230072969 + 3 ^ 40 * 7322190 * 2
def baseEnd_7322190 : Nat := 139251959760918967838921

theorem tailTrace_7322190 : CollatzResearch.WordTrace tailWord_7322190 prefixEnd_7322190 139251959760918967838921 := by
  unfold tailWord_7322190
  simp only [CollatzResearch.WordTrace]
  refine ⟨33382776167870454417161503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178041472895309090224861349 33382776167870454417161503)
  ·
    refine ⟨50074164251805681625742255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33382776167870454417161503 50074164251805681625742255)
    ·
      refine ⟨75111246377708522438613383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50074164251805681625742255 75111246377708522438613383)
      ·
        refine ⟨112666869566562783657920075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75111246377708522438613383 112666869566562783657920075)
        ·
          refine ⟨169000304349844175486880113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112666869566562783657920075 169000304349844175486880113)
          ·
            refine ⟨126750228262383131615160085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169000304349844175486880113 126750228262383131615160085)
            ·
              refine ⟨5941416949799209294460629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126750228262383131615160085 5941416949799209294460629)
              ·
                refine ⟨139251959760918967838921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5941416949799209294460629 139251959760918967838921)
                ·
                  rfl

theorem cell23_7322190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 7].length) (baseStart_7322190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322190 prefixEnd_7322190 := by exact prefixLift 7322190
  have htrace : WordTrace (prefixWord ++ tailWord_7322190) baseStart_7322190 baseEnd_7322190 := by
    simpa [prefixWord, tailWord_7322190, baseEnd_7322190] using wordTrace_append hprefix tailTrace_7322190
  have hstable : (prefixWord ++ tailWord_7322190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322190).length < 2 ^ (prefixWord ++ tailWord_7322190).sum := by decide
  have hdescent : baseEnd_7322190 < baseStart_7322190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322200 : List Nat := [2, 1, 2, 2, 1, 2, 2, 4, 1, 3, 3]
def baseStart_7322200 : Nat := 118140960795 + 7322200 * 2 ^ 59
def prefixEnd_7322200 : Nat := 4983230072969 + 3 ^ 40 * 7322200 * 2
def baseEnd_7322200 : Nat := 3759808048351357092525821

theorem tailTrace_7322200 : CollatzResearch.WordTrace tailWord_7322200 prefixEnd_7322200 3759808048351357092525821 := by
  unfold tailWord_7322200
  simp only [CollatzResearch.WordTrace]
  refine ⟨133531287036463703522578027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178041716048618271363437369 133531287036463703522578027)
  ·
    refine ⟨200296930554695555283867041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133531287036463703522578027 200296930554695555283867041)
    ·
      refine ⟨150222697916021666462900281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200296930554695555283867041 150222697916021666462900281)
      ·
        refine ⟨112667023437016249847175211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150222697916021666462900281 112667023437016249847175211)
        ·
          refine ⟨169000535155524374770762817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112667023437016249847175211 169000535155524374770762817)
          ·
            refine ⟨126750401366643281078072113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169000535155524374770762817 126750401366643281078072113)
            ·
              refine ⟨95062801024982460808554085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126750401366643281078072113 95062801024982460808554085)
              ·
                refine ⟨17824275192184211401603891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95062801024982460808554085 17824275192184211401603891)
                ·
                  refine ⟨26736412788276317102405837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17824275192184211401603891 26736412788276317102405837)
                  ·
                    refine ⟨10026154795603618913402189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26736412788276317102405837 10026154795603618913402189)
                    ·
                      refine ⟨3759808048351357092525821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10026154795603618913402189 3759808048351357092525821)
                      ·
                        rfl

theorem cell23_7322200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_7322200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322200 prefixEnd_7322200 := by exact prefixLift 7322200
  have htrace : WordTrace (prefixWord ++ tailWord_7322200) baseStart_7322200 baseEnd_7322200 := by
    simpa [prefixWord, tailWord_7322200, baseEnd_7322200] using wordTrace_append hprefix tailTrace_7322200
  have hstable : (prefixWord ++ tailWord_7322200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322200).length < 2 ^ (prefixWord ++ tailWord_7322200).sum := by decide
  have hdescent : baseEnd_7322200 < baseStart_7322200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322217 : List Nat := [1, 2, 1, 1, 1, 4, 1, 6, 2, 1, 3]
def baseStart_7322217 : Nat := 118140960795 + 7322217 * 2 ^ 59
def prefixEnd_7322217 : Nat := 4983230072969 + 3 ^ 40 * 7322217 * 2
def baseEnd_7322217 : Nat := 3759816777522483526013243

theorem tailTrace_7322217 : CollatzResearch.WordTrace tailWord_7322217 prefixEnd_7322217 3759816777522483526013243 := by
  unfold tailWord_7322217
  simp only [CollatzResearch.WordTrace]
  refine ⟨267063194113865818948524905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178042129409243879299016603 267063194113865818948524905)
  ·
    refine ⟨200297395585399364211393679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267063194113865818948524905 200297395585399364211393679)
    ·
      refine ⟨300446093378099046317090519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200297395585399364211393679 300446093378099046317090519)
      ·
        refine ⟨450669140067148569475635779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300446093378099046317090519 450669140067148569475635779)
        ·
          refine ⟨676003710100722854213453669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450669140067148569475635779 676003710100722854213453669)
          ·
            refine ⟨126750695643885535165022563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 676003710100722854213453669 126750695643885535165022563)
            ·
              refine ⟨190126043465828302747533845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126750695643885535165022563 190126043465828302747533845)
              ·
                refine ⟨8912158287460701691290649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 190126043465828302747533845 8912158287460701691290649)
                ·
                  refine ⟨6684118715595526268467987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8912158287460701691290649 6684118715595526268467987)
                  ·
                    refine ⟨10026178073393289402701981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6684118715595526268467987 10026178073393289402701981)
                    ·
                      refine ⟨3759816777522483526013243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10026178073393289402701981 3759816777522483526013243)
                      ·
                        rfl

theorem cell23_7322217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 1, 3].length) (baseStart_7322217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322217 prefixEnd_7322217 := by exact prefixLift 7322217
  have htrace : WordTrace (prefixWord ++ tailWord_7322217) baseStart_7322217 baseEnd_7322217 := by
    simpa [prefixWord, tailWord_7322217, baseEnd_7322217] using wordTrace_append hprefix tailTrace_7322217
  have hstable : (prefixWord ++ tailWord_7322217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322217).length < 2 ^ (prefixWord ++ tailWord_7322217).sum := by decide
  have hdescent : baseEnd_7322217 < baseStart_7322217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322218 : List Nat := [3, 1, 3, 2, 1, 1, 5, 2, 1, 2, 2]
def baseStart_7322218 : Nat := 118140960795 + 7322218 * 2 ^ 59
def prefixEnd_7322218 : Nat := 4983230072969 + 3 ^ 40 * 7322218 * 2
def baseEnd_7322218 : Nat := 3759817291003138022100739

theorem tailTrace_7322218 : CollatzResearch.WordTrace tailWord_7322218 prefixEnd_7322218 3759817291003138022100739 := by
  unfold tailWord_7322218
  simp only [CollatzResearch.WordTrace]
  refine ⟨66765807646715549029827827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178042153724574797412874205 66765807646715549029827827)
  ·
    refine ⟨100148711470073323544741741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66765807646715549029827827 100148711470073323544741741)
    ·
      refine ⟨37555766801277496329278153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100148711470073323544741741 37555766801277496329278153)
      ·
        refine ⟨28166825100958122246958615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37555766801277496329278153 28166825100958122246958615)
        ·
          refine ⟨42250237651437183370437923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28166825100958122246958615 42250237651437183370437923)
          ·
            refine ⟨63375356477155775055656885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42250237651437183370437923 63375356477155775055656885)
            ·
              refine ⟨5941439669733353911467833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63375356477155775055656885 5941439669733353911467833)
              ·
                refine ⟨4456079752300015433600875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5941439669733353911467833 4456079752300015433600875)
                ·
                  refine ⟨6684119628450023150401313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4456079752300015433600875 6684119628450023150401313)
                  ·
                    refine ⟨5013089721337517362800985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6684119628450023150401313 5013089721337517362800985)
                    ·
                      refine ⟨3759817291003138022100739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5013089721337517362800985 3759817291003138022100739)
                      ·
                        rfl

theorem cell23_7322218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_7322218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322218 prefixEnd_7322218 := by exact prefixLift 7322218
  have htrace : WordTrace (prefixWord ++ tailWord_7322218) baseStart_7322218 baseEnd_7322218 := by
    simpa [prefixWord, tailWord_7322218, baseEnd_7322218] using wordTrace_append hprefix tailTrace_7322218
  have hstable : (prefixWord ++ tailWord_7322218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322218).length < 2 ^ (prefixWord ++ tailWord_7322218).sum := by decide
  have hdescent : baseEnd_7322218 < baseStart_7322218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322244 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 3, 3, 2]
def baseStart_7322244 : Nat := 118140960795 + 7322244 * 2 ^ 59
def prefixEnd_7322244 : Nat := 4983230072969 + 3 ^ 40 * 7322244 * 2
def baseEnd_7322244 : Nat := 3759830641500154920375619

theorem tailTrace_7322244 : CollatzResearch.WordTrace tailWord_7322244 prefixEnd_7322244 3759830641500154920375619 := by
  unfold tailWord_7322244
  simp only [CollatzResearch.WordTrace]
  refine ⟨133532089442384001279878893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178042785923178668373171857 133532089442384001279878893)
  ·
    refine ⟨50074533540894000479954585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133532089442384001279878893 50074533540894000479954585)
    ·
      refine ⟨37555900155670500359965939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50074533540894000479954585 37555900155670500359965939)
      ·
        refine ⟨56333850233505750539948909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37555900155670500359965939 56333850233505750539948909)
        ·
          refine ⟨21125193837564656452480841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56333850233505750539948909 21125193837564656452480841)
          ·
            refine ⟨15843895378173492339360631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21125193837564656452480841 15843895378173492339360631)
            ·
              refine ⟨23765843067260238509040947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15843895378173492339360631 23765843067260238509040947)
              ·
                refine ⟨35648764600890357763561421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23765843067260238509040947 35648764600890357763561421)
                ·
                  refine ⟨13368286725333884161335533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35648764600890357763561421 13368286725333884161335533)
                  ·
                    refine ⟨5013107522000206560500825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13368286725333884161335533 5013107522000206560500825)
                    ·
                      refine ⟨3759830641500154920375619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5013107522000206560500825 3759830641500154920375619)
                      ·
                        rfl

theorem cell23_7322244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_7322244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322244 prefixEnd_7322244 := by exact prefixLift 7322244
  have htrace : WordTrace (prefixWord ++ tailWord_7322244) baseStart_7322244 baseEnd_7322244 := by
    simpa [prefixWord, tailWord_7322244, baseEnd_7322244] using wordTrace_append hprefix tailTrace_7322244
  have hstable : (prefixWord ++ tailWord_7322244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322244).length < 2 ^ (prefixWord ++ tailWord_7322244).sum := by decide
  have hdescent : baseEnd_7322244 < baseStart_7322244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322314 : List Nat := [3, 1, 2, 1, 4, 2, 2, 3, 5]
def baseStart_7322314 : Nat := 118140960795 + 7322314 * 2 ^ 59
def prefixEnd_7322314 : Nat := 4983230072969 + 3 ^ 40 * 7322314 * 2
def baseEnd_7322314 : Nat := 417762953905107738500033

theorem tailTrace_7322314 : CollatzResearch.WordTrace tailWord_7322314 prefixEnd_7322314 417762953905107738500033 := by
  unfold tailWord_7322314
  simp only [CollatzResearch.WordTrace]
  refine ⟨66766682998628601128701499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178044487996342936343203997 66766682998628601128701499)
  ·
    refine ⟨100150024497942901693052249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66766682998628601128701499 100150024497942901693052249)
    ·
      refine ⟨75112518373457176269789187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100150024497942901693052249 75112518373457176269789187)
      ·
        refine ⟨112668777560185764404683781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75112518373457176269789187 112668777560185764404683781)
        ·
          refine ⟨21125395792534830825878209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112668777560185764404683781 21125395792534830825878209)
          ·
            refine ⟨15844046844401123119408657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21125395792534830825878209 15844046844401123119408657)
            ·
              refine ⟨11883035133300842339556493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15844046844401123119408657 11883035133300842339556493)
              ·
                refine ⟨4456138174987815877333685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11883035133300842339556493 4456138174987815877333685)
                ·
                  refine ⟨417762953905107738500033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4456138174987815877333685 417762953905107738500033)
                  ·
                    rfl

theorem cell23_7322314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 5].length) (baseStart_7322314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322314 prefixEnd_7322314 := by exact prefixLift 7322314
  have htrace : WordTrace (prefixWord ++ tailWord_7322314) baseStart_7322314 baseEnd_7322314 := by
    simpa [prefixWord, tailWord_7322314, baseEnd_7322314] using wordTrace_append hprefix tailTrace_7322314
  have hstable : (prefixWord ++ tailWord_7322314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322314).length < 2 ^ (prefixWord ++ tailWord_7322314).sum := by decide
  have hdescent : baseEnd_7322314 < baseStart_7322314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322325 : List Nat := [1, 3, 2, 5, 1, 2, 1, 2, 2, 2, 2]
def baseStart_7322325 : Nat := 118140960795 + 7322325 * 2 ^ 59
def prefixEnd_7322325 : Nat := 4983230072969 + 3 ^ 40 * 7322325 * 2
def baseEnd_7322325 : Nat := 3759872233433169103462747

theorem tailTrace_7322325 : CollatzResearch.WordTrace tailWord_7322325 prefixEnd_7322325 3759872233433169103462747 := by
  unfold tailWord_7322325
  simp only [CollatzResearch.WordTrace]
  refine ⟨267067133197474553393456429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178044755464983035595637619 267067133197474553393456429)
  ·
    refine ⟨100150174949052957522546161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267067133197474553393456429 100150174949052957522546161)
    ·
      refine ⟨75112631211789718141909621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100150174949052957522546161 75112631211789718141909621)
      ·
        refine ⟨7041809176105286075804027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75112631211789718141909621 7041809176105286075804027)
        ·
          refine ⟨10562713764157929113706041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7041809176105286075804027 10562713764157929113706041)
          ·
            refine ⟨7922035323118446835279531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10562713764157929113706041 7922035323118446835279531)
            ·
              refine ⟨11883052984677670252919297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7922035323118446835279531 11883052984677670252919297)
              ·
                refine ⟨8912289738508252689689473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11883052984677670252919297 8912289738508252689689473)
                ·
                  refine ⟨6684217303881189517267105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8912289738508252689689473 6684217303881189517267105)
                  ·
                    refine ⟨5013162977910892137950329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6684217303881189517267105 5013162977910892137950329)
                    ·
                      refine ⟨3759872233433169103462747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5013162977910892137950329 3759872233433169103462747)
                      ·
                        rfl

theorem cell23_7322325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_7322325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322325 prefixEnd_7322325 := by exact prefixLift 7322325
  have htrace : WordTrace (prefixWord ++ tailWord_7322325) baseStart_7322325 baseEnd_7322325 := by
    simpa [prefixWord, tailWord_7322325, baseEnd_7322325] using wordTrace_append hprefix tailTrace_7322325
  have hstable : (prefixWord ++ tailWord_7322325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322325).length < 2 ^ (prefixWord ++ tailWord_7322325).sum := by decide
  have hdescent : baseEnd_7322325 < baseStart_7322325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322360 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 2, 4, 4]
def baseStart_7322360 : Nat := 118140960795 + 7322360 * 2 ^ 59
def prefixEnd_7322360 : Nat := 4983230072969 + 3 ^ 40 * 7322360 * 2
def baseEnd_7322360 : Nat := 3759890205256076466525085

theorem tailTrace_7322360 : CollatzResearch.WordTrace tailWord_7322360 prefixEnd_7322360 3759890205256076466525085 := by
  unfold tailWord_7322360
  simp only [CollatzResearch.WordTrace]
  refine ⟨133534204876173877185490267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178045606501565169580653689 133534204876173877185490267)
  ·
    refine ⟨200301307314260815778235401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133534204876173877185490267 200301307314260815778235401)
    ·
      refine ⟨150225980485695611833676551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200301307314260815778235401 150225980485695611833676551)
      ·
        refine ⟨225338970728543417750514827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150225980485695611833676551 225338970728543417750514827)
        ·
          refine ⟨338008456092815126625772241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225338970728543417750514827 338008456092815126625772241)
          ·
            refine ⟨253506342069611344969329181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338008456092815126625772241 253506342069611344969329181)
            ·
              refine ⟨95064878276104254363498443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253506342069611344969329181 95064878276104254363498443)
              ·
                refine ⟨142597317414156381545247665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95064878276104254363498443 142597317414156381545247665)
                ·
                  refine ⟨106947988060617286158935749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142597317414156381545247665 106947988060617286158935749)
                  ·
                    refine ⟨20052747761365741154800453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106947988060617286158935749 20052747761365741154800453)
                    ·
                      refine ⟨3759890205256076466525085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20052747761365741154800453 3759890205256076466525085)
                      ·
                        rfl

theorem cell23_7322360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_7322360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322360 prefixEnd_7322360 := by exact prefixLift 7322360
  have htrace : WordTrace (prefixWord ++ tailWord_7322360) baseStart_7322360 baseEnd_7322360 := by
    simpa [prefixWord, tailWord_7322360, baseEnd_7322360] using wordTrace_append hprefix tailTrace_7322360
  have hstable : (prefixWord ++ tailWord_7322360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322360).length < 2 ^ (prefixWord ++ tailWord_7322360).sum := by decide
  have hdescent : baseEnd_7322360 < baseStart_7322360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322367 : List Nat := [1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 3]
def baseStart_7322367 : Nat := 118140960795 + 7322367 * 2 ^ 59
def prefixEnd_7322367 : Nat := 4983230072969 + 3 ^ 40 * 7322367 * 2
def baseEnd_7322367 : Nat := 3759893799620657939137553

theorem tailTrace_7322367 : CollatzResearch.WordTrace tailWord_7322367 prefixEnd_7322367 3759893799620657939137553 := by
  unfold tailWord_7322367
  simp only [CollatzResearch.WordTrace]
  refine ⟨267068665063322394566485355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178045776708881596377656903 267068665063322394566485355)
  ·
    refine ⟨400602997594983591849728033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267068665063322394566485355 400602997594983591849728033)
    ·
      refine ⟨300452248196237693887296025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400602997594983591849728033 300452248196237693887296025)
      ·
        refine ⟨225339186147178270415472019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300452248196237693887296025 225339186147178270415472019)
        ·
          refine ⟨338008779220767405623208029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225339186147178270415472019 338008779220767405623208029)
          ·
            refine ⟨126753292207787777108703011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338008779220767405623208029 126753292207787777108703011)
            ·
              refine ⟨190129938311681665663054517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126753292207787777108703011 190129938311681665663054517)
              ·
                refine ⟨17824681716720156155911361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190129938311681665663054517 17824681716720156155911361)
                ·
                  refine ⟨13368511287540117116933521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17824681716720156155911361 13368511287540117116933521)
                  ·
                    refine ⟨10026383465655087837700141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13368511287540117116933521 10026383465655087837700141)
                    ·
                      refine ⟨3759893799620657939137553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10026383465655087837700141 3759893799620657939137553)
                      ·
                        rfl

theorem cell23_7322367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_7322367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322367 prefixEnd_7322367 := by exact prefixLift 7322367
  have htrace : WordTrace (prefixWord ++ tailWord_7322367) baseStart_7322367 baseEnd_7322367 := by
    simpa [prefixWord, tailWord_7322367, baseEnd_7322367] using wordTrace_append hprefix tailTrace_7322367
  have hstable : (prefixWord ++ tailWord_7322367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322367).length < 2 ^ (prefixWord ++ tailWord_7322367).sum := by decide
  have hdescent : baseEnd_7322367 < baseStart_7322367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322391 : List Nat := [1, 1, 3, 4, 3, 2, 1, 1, 3, 4]
def baseStart_7322391 : Nat := 118140960795 + 7322391 * 2 ^ 59
def prefixEnd_7322391 : Nat := 4983230072969 + 3 ^ 40 * 7322391 * 2
def baseEnd_7322391 : Nat := 1253302041052121948412481

theorem tailTrace_7322391 : CollatzResearch.WordTrace tailWord_7322391 prefixEnd_7322391 1253302041052121948412481 := by
  unfold tailWord_7322391
  simp only [CollatzResearch.WordTrace]
  refine ⟨267069540415235446665359027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178046360276823631110239351 267069540415235446665359027)
  ·
    refine ⟨400604310622853169998038541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267069540415235446665359027 400604310622853169998038541)
    ·
      refine ⟨150226616483569938749264453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400604310622853169998038541 150226616483569938749264453)
      ·
        refine ⟨28167490590669363515487085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150226616483569938749264453 28167490590669363515487085)
        ·
          refine ⟨10562808971501011318307657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28167490590669363515487085 10562808971501011318307657)
          ·
            refine ⟨7922106728625758488730743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10562808971501011318307657 7922106728625758488730743)
            ·
              refine ⟨11883160092938637733096115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7922106728625758488730743 11883160092938637733096115)
              ·
                refine ⟨17824740139407956599644173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11883160092938637733096115 17824740139407956599644173)
                ·
                  refine ⟨6684277552277983724866565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17824740139407956599644173 6684277552277983724866565)
                  ·
                    refine ⟨1253302041052121948412481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6684277552277983724866565 1253302041052121948412481)
                    ·
                      rfl

theorem cell23_7322391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_7322391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322391 prefixEnd_7322391 := by exact prefixLift 7322391
  have htrace : WordTrace (prefixWord ++ tailWord_7322391) baseStart_7322391 baseEnd_7322391 := by
    simpa [prefixWord, tailWord_7322391, baseEnd_7322391] using wordTrace_append hprefix tailTrace_7322391
  have hstable : (prefixWord ++ tailWord_7322391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322391).length < 2 ^ (prefixWord ++ tailWord_7322391).sum := by decide
  have hdescent : baseEnd_7322391 < baseStart_7322391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322404 : List Nat := [2, 3, 1, 3, 3, 1, 1, 3, 6]
def baseStart_7322404 : Nat := 118140960795 + 7322404 * 2 ^ 59
def prefixEnd_7322404 : Nat := 4983230072969 + 3 ^ 40 * 7322404 * 2
def baseEnd_7322404 : Nat := 417768088711652699374987

theorem tailTrace_7322404 : CollatzResearch.WordTrace tailWord_7322404 prefixEnd_7322404 417768088711652699374987 := by
  unfold tailWord_7322404
  simp only [CollatzResearch.WordTrace]
  refine ⟨133535007282094174942791133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178046676376125566590388177 133535007282094174942791133)
  ·
    refine ⟨50075627730785315603546675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133535007282094174942791133 50075627730785315603546675)
    ·
      refine ⟨75113441596177973405320013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50075627730785315603546675 75113441596177973405320013)
      ·
        refine ⟨28167540598566740026995005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75113441596177973405320013 28167540598566740026995005)
        ·
          refine ⟨10562827724462527510123127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28167540598566740026995005 10562827724462527510123127)
          ·
            refine ⟨15844241586693791265184691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10562827724462527510123127 15844241586693791265184691)
            ·
              refine ⟨23766362380040686897777037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15844241586693791265184691 23766362380040686897777037)
              ·
                refine ⟨8912385892515257586666389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23766362380040686897777037 8912385892515257586666389)
                ·
                  refine ⟨417768088711652699374987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8912385892515257586666389 417768088711652699374987)
                  ·
                    rfl

theorem cell23_7322404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_7322404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322404 prefixEnd_7322404 := by exact prefixLift 7322404
  have htrace : WordTrace (prefixWord ++ tailWord_7322404) baseStart_7322404 baseEnd_7322404 := by
    simpa [prefixWord, tailWord_7322404, baseEnd_7322404] using wordTrace_append hprefix tailTrace_7322404
  have hstable : (prefixWord ++ tailWord_7322404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322404).length < 2 ^ (prefixWord ++ tailWord_7322404).sum := by decide
  have hdescent : baseEnd_7322404 < baseStart_7322404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322417 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 3, 5]
def baseStart_7322417 : Nat := 118140960795 + 7322417 * 2 ^ 59
def prefixEnd_7322417 : Nat := 4983230072969 + 3 ^ 40 * 7322417 * 2
def baseEnd_7322417 : Nat := 1253306491217794247837441

theorem tailTrace_7322417 : CollatzResearch.WordTrace tailWord_7322417 prefixEnd_7322417 1253306491217794247837441 := by
  unfold tailWord_7322417
  simp only [CollatzResearch.WordTrace]
  refine ⟨267070488713141253105805505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178046992475427502070537003 267070488713141253105805505)
  ·
    refine ⟨200302866534855939829354129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267070488713141253105805505 200302866534855939829354129)
    ·
      refine ⟨150227149901141954872015597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200302866534855939829354129 150227149901141954872015597)
      ·
        refine ⟨56335181212928233077005849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150227149901141954872015597 56335181212928233077005849)
        ·
          refine ⟨42251385909696174807754387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56335181212928233077005849 42251385909696174807754387)
          ·
            refine ⟨63377078864544262211631581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42251385909696174807754387 63377078864544262211631581)
            ·
              refine ⟨23766404574204098329361843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63377078864544262211631581 23766404574204098329361843)
              ·
                refine ⟨35649606861306147494042765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23766404574204098329361843 35649606861306147494042765)
                ·
                  refine ⟨13368602572989805310266037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35649606861306147494042765 13368602572989805310266037)
                  ·
                    refine ⟨1253306491217794247837441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13368602572989805310266037 1253306491217794247837441)
                    ·
                      rfl

theorem cell23_7322417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_7322417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322417 prefixEnd_7322417 := by exact prefixLift 7322417
  have htrace : WordTrace (prefixWord ++ tailWord_7322417) baseStart_7322417 baseEnd_7322417 := by
    simpa [prefixWord, tailWord_7322417, baseEnd_7322417] using wordTrace_append hprefix tailTrace_7322417
  have hstable : (prefixWord ++ tailWord_7322417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322417).length < 2 ^ (prefixWord ++ tailWord_7322417).sum := by decide
  have hdescent : baseEnd_7322417 < baseStart_7322417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322438 : List Nat := [6, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_7322438 : Nat := 118140960795 + 7322438 * 2 ^ 59
def prefixEnd_7322438 : Nat := 4983230072969 + 3 ^ 40 * 7322438 * 2
def baseEnd_7322438 : Nat := 417770028527458573483303

theorem tailTrace_7322438 : CollatzResearch.WordTrace tailWord_7322438 prefixEnd_7322438 417770028527458573483303 := by
  unfold tailWord_7322438
  simp only [CollatzResearch.WordTrace]
  refine ⟨8345976707689536677884999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 178047503097376782461546645 8345976707689536677884999)
  ·
    refine ⟨12518965061534305016827499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8345976707689536677884999 12518965061534305016827499)
    ·
      refine ⟨18778447592301457525241249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12518965061534305016827499 18778447592301457525241249)
      ·
        refine ⟨14083835694226093143930937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18778447592301457525241249 14083835694226093143930937)
        ·
          refine ⟨10562876770669569857948203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14083835694226093143930937 10562876770669569857948203)
          ·
            refine ⟨15844315156004354786922305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10562876770669569857948203 15844315156004354786922305)
            ·
              refine ⟨11883236367003266090191729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15844315156004354786922305 11883236367003266090191729)
              ·
                refine ⟨8912427275252449567643797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11883236367003266090191729 8912427275252449567643797)
                ·
                  refine ⟨417770028527458573483303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8912427275252449567643797 417770028527458573483303)
                  ·
                    rfl

theorem cell23_7322438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_7322438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322438 prefixEnd_7322438 := by exact prefixLift 7322438
  have htrace : WordTrace (prefixWord ++ tailWord_7322438) baseStart_7322438 baseEnd_7322438 := by
    simpa [prefixWord, tailWord_7322438, baseEnd_7322438] using wordTrace_append hprefix tailTrace_7322438
  have hstable : (prefixWord ++ tailWord_7322438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322438).length < 2 ^ (prefixWord ++ tailWord_7322438).sum := by decide
  have hdescent : baseEnd_7322438 < baseStart_7322438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322448 : List Nat := [2, 1, 1, 1, 1, 4, 6, 2, 1, 1, 3]
def baseStart_7322448 : Nat := 118140960795 + 7322448 * 2 ^ 59
def prefixEnd_7322448 : Nat := 4983230072969 + 3 ^ 40 * 7322448 * 2
def baseEnd_7322448 : Nat := 3759935391553672122224681

theorem tailTrace_7322448 : CollatzResearch.WordTrace tailWord_7322448 prefixEnd_7322448 3759935391553672122224681 := by
  unfold tailWord_7322448
  simp only [CollatzResearch.WordTrace]
  refine ⟨133535809688014472700091999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178047746250685963600122665 133535809688014472700091999)
  ·
    refine ⟨200303714532021709050137999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133535809688014472700091999 200303714532021709050137999)
    ·
      refine ⟨300455571798032563575206999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200303714532021709050137999 300455571798032563575206999)
      ·
        refine ⟨450683357697048845362810499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300455571798032563575206999 450683357697048845362810499)
        ·
          refine ⟨676025036545573268044215749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450683357697048845362810499 676025036545573268044215749)
          ·
            refine ⟨126754694352294987758290453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 676025036545573268044215749 126754694352294987758290453)
            ·
              refine ⟨5941626297763827551169865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126754694352294987758290453 5941626297763827551169865)
              ·
                refine ⟨4456219723322870663377399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5941626297763827551169865 4456219723322870663377399)
                ·
                  refine ⟨6684329584984305995066099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4456219723322870663377399 6684329584984305995066099)
                  ·
                    refine ⟨10026494377476458992599149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6684329584984305995066099 10026494377476458992599149)
                    ·
                      refine ⟨3759935391553672122224681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10026494377476458992599149 3759935391553672122224681)
                      ·
                        rfl

theorem cell23_7322448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 1, 1, 3].length) (baseStart_7322448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322448 prefixEnd_7322448 := by exact prefixLift 7322448
  have htrace : WordTrace (prefixWord ++ tailWord_7322448) baseStart_7322448 baseEnd_7322448 := by
    simpa [prefixWord, tailWord_7322448, baseEnd_7322448] using wordTrace_append hprefix tailTrace_7322448
  have hstable : (prefixWord ++ tailWord_7322448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322448).length < 2 ^ (prefixWord ++ tailWord_7322448).sum := by decide
  have hdescent : baseEnd_7322448 < baseStart_7322448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322464 : List Nat := [2, 1, 1, 3, 3, 1, 1, 5, 2, 4]
def baseStart_7322464 : Nat := 118140960795 + 7322464 * 2 ^ 59
def prefixEnd_7322464 : Nat := 4983230072969 + 3 ^ 40 * 7322464 * 2
def baseEnd_7322464 : Nat := 1253314535748048019874869

theorem tailTrace_7322464 : CollatzResearch.WordTrace tailWord_7322464 prefixEnd_7322464 1253314535748048019874869 := by
  unfold tailWord_7322464
  simp only [CollatzResearch.WordTrace]
  refine ⟨133536101471985490066383223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178048135295980653421844297 133536101471985490066383223)
  ·
    refine ⟨200304152207978235099574835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133536101471985490066383223 200304152207978235099574835)
    ·
      refine ⟨300456228311967352649362253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200304152207978235099574835 300456228311967352649362253)
      ·
        refine ⟨112671085616987757243510845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300456228311967352649362253 112671085616987757243510845)
        ·
          refine ⟨42251657106370408966316567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112671085616987757243510845 42251657106370408966316567)
          ·
            refine ⟨63377485659555613449474851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42251657106370408966316567 63377485659555613449474851)
            ·
              refine ⟨95066228489333420174212277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63377485659555613449474851 95066228489333420174212277)
              ·
                refine ⟨8912458920875008141332401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95066228489333420174212277 8912458920875008141332401)
                ·
                  refine ⟨6684344190656256105999301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8912458920875008141332401 6684344190656256105999301)
                  ·
                    refine ⟨1253314535748048019874869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6684344190656256105999301 1253314535748048019874869)
                    ·
                      rfl

theorem cell23_7322464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 2, 4].length) (baseStart_7322464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322464 prefixEnd_7322464 := by exact prefixLift 7322464
  have htrace : WordTrace (prefixWord ++ tailWord_7322464) baseStart_7322464 baseEnd_7322464 := by
    simpa [prefixWord, tailWord_7322464, baseEnd_7322464] using wordTrace_append hprefix tailTrace_7322464
  have hstable : (prefixWord ++ tailWord_7322464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322464).length < 2 ^ (prefixWord ++ tailWord_7322464).sum := by decide
  have hdescent : baseEnd_7322464 < baseStart_7322464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322471 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 5, 2, 2]
def baseStart_7322471 : Nat := 118140960795 + 7322471 * 2 ^ 59
def prefixEnd_7322471 : Nat := 4983230072969 + 3 ^ 40 * 7322471 * 2
def baseEnd_7322471 : Nat := 3759947201608725532237075

theorem tailTrace_7322471 : CollatzResearch.WordTrace tailWord_7322471 prefixEnd_7322471 3759947201608725532237075 := by
  unfold tailWord_7322471
  simp only [CollatzResearch.WordTrace]
  refine ⟨267072458254945620328271267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178048305503297080218847511 267072458254945620328271267)
  ·
    refine ⟨400608687382418430492406901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267072458254945620328271267 400608687382418430492406901)
    ·
      refine ⟨37557064442101727858663147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 400608687382418430492406901 37557064442101727858663147)
      ·
        refine ⟨56335596663152591787994721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37557064442101727858663147 56335596663152591787994721)
        ·
          refine ⟨42251697497364443840996041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56335596663152591787994721 42251697497364443840996041)
          ·
            refine ⟨31688773123023332880747031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42251697497364443840996041 31688773123023332880747031)
            ·
              refine ⟨47533159684534999321120547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31688773123023332880747031 47533159684534999321120547)
              ·
                refine ⟨71299739526802498981680821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47533159684534999321120547 71299739526802498981680821)
                ·
                  refine ⟨6684350580637734279532577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71299739526802498981680821 6684350580637734279532577)
                  ·
                    refine ⟨5013262935478300709649433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6684350580637734279532577 5013262935478300709649433)
                    ·
                      refine ⟨3759947201608725532237075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5013262935478300709649433 3759947201608725532237075)
                      ·
                        rfl

theorem cell23_7322471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_7322471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322471 prefixEnd_7322471 := by exact prefixLift 7322471
  have htrace : WordTrace (prefixWord ++ tailWord_7322471) baseStart_7322471 baseEnd_7322471 := by
    simpa [prefixWord, tailWord_7322471, baseEnd_7322471] using wordTrace_append hprefix tailTrace_7322471
  have hstable : (prefixWord ++ tailWord_7322471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322471).length < 2 ^ (prefixWord ++ tailWord_7322471).sum := by decide
  have hdescent : baseEnd_7322471 < baseStart_7322471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322491 : List Nat := [1, 1, 1, 1, 1, 5, 6, 1, 1, 2, 3]
def baseStart_7322491 : Nat := 118140960795 + 7322491 * 2 ^ 59
def prefixEnd_7322491 : Nat := 4983230072969 + 3 ^ 40 * 7322491 * 2
def baseEnd_7322491 : Nat := 3759957471221815453986983

theorem tailTrace_7322491 : CollatzResearch.WordTrace tailWord_7322491 prefixEnd_7322491 3759957471221815453986983 := by
  unfold tailWord_7322491
  simp only [CollatzResearch.WordTrace]
  refine ⟨267073187714873163743999327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178048791809915442495999551 267073187714873163743999327)
  ·
    refine ⟨400609781572309745615998991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267073187714873163743999327 400609781572309745615998991)
    ·
      refine ⟨600914672358464618423998487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400609781572309745615998991 600914672358464618423998487)
      ·
        refine ⟨901372008537696927635997731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600914672358464618423998487 901372008537696927635997731)
        ·
          refine ⟨1352058012806545391453996597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901372008537696927635997731 1352058012806545391453996597)
          ·
            refine ⟨126755438700613630448812181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1352058012806545391453996597 126755438700613630448812181)
            ·
              refine ⟨5941661189091263927288071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126755438700613630448812181 5941661189091263927288071)
              ·
                refine ⟨8912491783636895890932107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5941661189091263927288071 8912491783636895890932107)
                ·
                  refine ⟨13368737675455343836398161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8912491783636895890932107 13368737675455343836398161)
                  ·
                    refine ⟨10026553256591507877298621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13368737675455343836398161 10026553256591507877298621)
                    ·
                      refine ⟨3759957471221815453986983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10026553256591507877298621 3759957471221815453986983)
                      ·
                        rfl

theorem cell23_7322491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 1, 2, 3].length) (baseStart_7322491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322491 prefixEnd_7322491 := by exact prefixLift 7322491
  have htrace : WordTrace (prefixWord ++ tailWord_7322491) baseStart_7322491 baseEnd_7322491 := by
    simpa [prefixWord, tailWord_7322491, baseEnd_7322491] using wordTrace_append hprefix tailTrace_7322491
  have hstable : (prefixWord ++ tailWord_7322491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322491).length < 2 ^ (prefixWord ++ tailWord_7322491).sum := by decide
  have hdescent : baseEnd_7322491 < baseStart_7322491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322518 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_7322518 : Nat := 118140960795 + 7322518 * 2 ^ 59
def prefixEnd_7322518 : Nat := 4983230072969 + 3 ^ 40 * 7322518 * 2
def baseEnd_7322518 : Nat := 3759971335199486848349359

theorem tailTrace_7322518 : CollatzResearch.WordTrace tailWord_7322518 prefixEnd_7322518 3759971335199486848349359 := by
  unfold tailWord_7322518
  simp only [CollatzResearch.WordTrace]
  refine ⟨16692135780360959209702013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178049448323850231570154805 16692135780360959209702013)
  ·
    refine ⟨6259550917635359703638255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16692135780360959209702013 6259550917635359703638255)
    ·
      refine ⟨9389326376453039555457383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6259550917635359703638255 9389326376453039555457383)
      ·
        refine ⟨14083989564679559333186075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9389326376453039555457383 14083989564679559333186075)
        ·
          refine ⟨21125984347019338999779113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14083989564679559333186075 21125984347019338999779113)
          ·
            refine ⟨15844488260264504249834335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21125984347019338999779113 15844488260264504249834335)
            ·
              refine ⟨23766732390396756374751503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15844488260264504249834335 23766732390396756374751503)
              ·
                refine ⟨35650098585595134562127255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23766732390396756374751503 35650098585595134562127255)
                ·
                  refine ⟨53475147878392701843190883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35650098585595134562127255 53475147878392701843190883)
                  ·
                    refine ⟨80212721817589052764786325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53475147878392701843190883 80212721817589052764786325)
                    ·
                      refine ⟨3759971335199486848349359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80212721817589052764786325 3759971335199486848349359)
                      ·
                        rfl

theorem cell23_7322518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_7322518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322518 prefixEnd_7322518 := by exact prefixLift 7322518
  have htrace : WordTrace (prefixWord ++ tailWord_7322518) baseStart_7322518 baseEnd_7322518 := by
    simpa [prefixWord, tailWord_7322518, baseEnd_7322518] using wordTrace_append hprefix tailTrace_7322518
  have hstable : (prefixWord ++ tailWord_7322518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322518).length < 2 ^ (prefixWord ++ tailWord_7322518).sum := by decide
  have hdescent : baseEnd_7322518 < baseStart_7322518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322531 : List Nat := [1, 1, 1, 4, 1, 2, 3, 4, 1, 3, 2]
def baseStart_7322531 : Nat := 118140960795 + 7322531 * 2 ^ 59
def prefixEnd_7322531 : Nat := 4983230072969 + 3 ^ 40 * 7322531 * 2
def baseEnd_7322531 : Nat := 3759978010447995297486799

theorem tailTrace_7322531 : CollatzResearch.WordTrace tailWord_7322531 prefixEnd_7322531 3759978010447995297486799 := by
  unfold tailWord_7322531
  simp only [CollatzResearch.WordTrace]
  refine ⟨267074646634728250575455447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178049764423152167050303631 267074646634728250575455447)
  ·
    refine ⟨400611969952092375863183171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267074646634728250575455447 400611969952092375863183171)
    ·
      refine ⟨600917954928138563794774757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400611969952092375863183171 600917954928138563794774757)
      ·
        refine ⟨112672116549025980711520267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 600917954928138563794774757 112672116549025980711520267)
        ·
          refine ⟨169008174823538971067280401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112672116549025980711520267 169008174823538971067280401)
          ·
            refine ⟨126756131117654228300460301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169008174823538971067280401 126756131117654228300460301)
            ·
              refine ⟨47533549169120335612672613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126756131117654228300460301 47533549169120335612672613)
              ·
                refine ⟨8912540469210062927376115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47533549169120335612672613 8912540469210062927376115)
                ·
                  refine ⟨13368810703815094391064173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8912540469210062927376115 13368810703815094391064173)
                  ·
                    refine ⟨5013304013930660396649065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13368810703815094391064173 5013304013930660396649065)
                    ·
                      refine ⟨3759978010447995297486799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5013304013930660396649065 3759978010447995297486799)
                      ·
                        rfl

theorem cell23_7322531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_7322531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322531 prefixEnd_7322531 := by exact prefixLift 7322531
  have htrace : WordTrace (prefixWord ++ tailWord_7322531) baseStart_7322531 baseEnd_7322531 := by
    simpa [prefixWord, tailWord_7322531, baseEnd_7322531] using wordTrace_append hprefix tailTrace_7322531
  have hstable : (prefixWord ++ tailWord_7322531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322531).length < 2 ^ (prefixWord ++ tailWord_7322531).sum := by decide
  have hdescent : baseEnd_7322531 < baseStart_7322531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322566 : List Nat := [6, 1, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_7322566 : Nat := 118140960795 + 7322566 * 2 ^ 59
def prefixEnd_7322566 : Nat := 4983230072969 + 3 ^ 40 * 7322566 * 2
def baseEnd_7322566 : Nat := 1253331994090300886849713

theorem tailTrace_7322566 : CollatzResearch.WordTrace tailWord_7322566 prefixEnd_7322566 1253331994090300886849713 := by
  unfold tailWord_7322566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8346122599675045361030611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 178050615459734301035319701 8346122599675045361030611)
  ·
    refine ⟨12519183899512568041545917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8346122599675045361030611 12519183899512568041545917)
    ·
      refine ⟨4694693962317213015579719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12519183899512568041545917 4694693962317213015579719)
      ·
        refine ⟨7042040943475819523369579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4694693962317213015579719 7042040943475819523369579)
        ·
          refine ⟨10563061415213729285054369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7042040943475819523369579 10563061415213729285054369)
          ·
            refine ⟨7922296061410296963790777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10563061415213729285054369 7922296061410296963790777)
            ·
              refine ⟨5941722046057722722843083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7922296061410296963790777 5941722046057722722843083)
              ·
                refine ⟨8912583069086584084264625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5941722046057722722843083 8912583069086584084264625)
                ·
                  refine ⟨6684437301814938063198469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8912583069086584084264625 6684437301814938063198469)
                  ·
                    refine ⟨1253331994090300886849713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6684437301814938063198469 1253331994090300886849713)
                    ·
                      rfl

theorem cell23_7322566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_7322566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322566 prefixEnd_7322566 := by exact prefixLift 7322566
  have htrace : WordTrace (prefixWord ++ tailWord_7322566) baseStart_7322566 baseEnd_7322566 := by
    simpa [prefixWord, tailWord_7322566, baseEnd_7322566] using wordTrace_append hprefix tailTrace_7322566
  have hstable : (prefixWord ++ tailWord_7322566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322566).length < 2 ^ (prefixWord ++ tailWord_7322566).sum := by decide
  have hdescent : baseEnd_7322566 < baseStart_7322566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322582 : List Nat := [5, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_7322582 : Nat := 118140960795 + 7322582 * 2 ^ 59
def prefixEnd_7322582 : Nat := 4983230072969 + 3 ^ 40 * 7322582 * 2
def baseEnd_7322582 : Nat := 3760004197961374597949065

theorem tailTrace_7322582 : CollatzResearch.WordTrace tailWord_7322582 prefixEnd_7322582 3760004197961374597949065 := by
  unfold tailWord_7322582
  simp only [CollatzResearch.WordTrace]
  refine ⟨16692281672346467892847625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178051004505028990857041333 16692281672346467892847625)
  ·
    refine ⟨12519211254259850919635719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16692281672346467892847625 12519211254259850919635719)
    ·
      refine ⟨18778816881389776379453579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12519211254259850919635719 18778816881389776379453579)
      ·
        refine ⟨28168225322084664569180369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18778816881389776379453579 28168225322084664569180369)
        ·
          refine ⟨21126168991563498426885277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28168225322084664569180369 21126168991563498426885277)
          ·
            refine ⟨7922313371836311910081979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21126168991563498426885277 7922313371836311910081979)
            ·
              refine ⟨11883470057754467865122969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7922313371836311910081979 11883470057754467865122969)
              ·
                refine ⟨8912602543315850898842227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11883470057754467865122969 8912602543315850898842227)
                ·
                  refine ⟨13368903814973776348263341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8912602543315850898842227 13368903814973776348263341)
                  ·
                    refine ⟨5013338930615166130598753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13368903814973776348263341 5013338930615166130598753)
                    ·
                      refine ⟨3760004197961374597949065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5013338930615166130598753 3760004197961374597949065)
                      ·
                        rfl

theorem cell23_7322582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_7322582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322582 prefixEnd_7322582 := by exact prefixLift 7322582
  have htrace : WordTrace (prefixWord ++ tailWord_7322582) baseStart_7322582 baseEnd_7322582 := by
    simpa [prefixWord, tailWord_7322582, baseEnd_7322582] using wordTrace_append hprefix tailTrace_7322582
  have hstable : (prefixWord ++ tailWord_7322582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322582).length < 2 ^ (prefixWord ++ tailWord_7322582).sum := by decide
  have hdescent : baseEnd_7322582 < baseStart_7322582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322627 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 4, 8]
def baseStart_7322627 : Nat := 118140960795 + 7322627 * 2 ^ 59
def prefixEnd_7322627 : Nat := 4983230072969 + 3 ^ 40 * 7322627 * 2
def baseEnd_7322627 : Nat := 1253342434863608973962119

theorem tailTrace_7322627 : CollatzResearch.WordTrace tailWord_7322627 prefixEnd_7322627 1253342434863608973962119 := by
  unfold tailWord_7322627
  simp only [CollatzResearch.WordTrace]
  refine ⟨267078148042380458970950135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178052098694920305980633423 267078148042380458970950135)
  ·
    refine ⟨400617222063570688456425203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267078148042380458970950135 400617222063570688456425203)
    ·
      refine ⟨600925833095356032684637805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400617222063570688456425203 600925833095356032684637805)
      ·
        refine ⟨225347187410758512256739177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 600925833095356032684637805 225347187410758512256739177)
        ·
          refine ⟨169010390558068884192554383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225347187410758512256739177 169010390558068884192554383)
          ·
            refine ⟨253515585837103326288831575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169010390558068884192554383 253515585837103326288831575)
            ·
              refine ⟨380273378755654989433247363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253515585837103326288831575 380273378755654989433247363)
              ·
                refine ⟨570410068133482484149871045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380273378755654989433247363 570410068133482484149871045)
                ·
                  refine ⟨106951887775027965778100821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 570410068133482484149871045 106951887775027965778100821)
                  ·
                    refine ⟨1253342434863608973962119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106951887775027965778100821 1253342434863608973962119)
                    ·
                      rfl

theorem cell23_7322627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 8].length) (baseStart_7322627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322627 prefixEnd_7322627 := by exact prefixLift 7322627
  have htrace : WordTrace (prefixWord ++ tailWord_7322627) baseStart_7322627 baseEnd_7322627 := by
    simpa [prefixWord, tailWord_7322627, baseEnd_7322627] using wordTrace_append hprefix tailTrace_7322627
  have hstable : (prefixWord ++ tailWord_7322627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322627).length < 2 ^ (prefixWord ++ tailWord_7322627).sum := by decide
  have hdescent : baseEnd_7322627 < baseStart_7322627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322674 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 8]
def baseStart_7322674 : Nat := 118140960795 + 7322674 * 2 ^ 59
def prefixEnd_7322674 : Nat := 4983230072969 + 3 ^ 40 * 7322674 * 2
def baseEnd_7322674 : Nat := 417783493131287581999849

theorem tailTrace_7322674 : CollatzResearch.WordTrace tailWord_7322674 prefixEnd_7322674 417783493131287581999849 := by
  unfold tailWord_7322674
  simp only [CollatzResearch.WordTrace]
  refine ⟨66769965568302546499477769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178053241515473457331940717 66769965568302546499477769)
  ·
    refine ⟨50077474176226909874608327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66769965568302546499477769 50077474176226909874608327)
    ·
      refine ⟨75116211264340364811912491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50077474176226909874608327 75116211264340364811912491)
      ·
        refine ⟨112674316896510547217868737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75116211264340364811912491 112674316896510547217868737)
        ·
          refine ⟨84505737672382910413401553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112674316896510547217868737 84505737672382910413401553)
          ·
            refine ⟨63379303254287182810051165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84505737672382910413401553 63379303254287182810051165)
            ·
              refine ⟨23767238720357693553769187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63379303254287182810051165 23767238720357693553769187)
              ·
                refine ⟨35650858080536540330653781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23767238720357693553769187 35650858080536540330653781)
                ·
                  refine ⟨417783493131287581999849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35650858080536540330653781 417783493131287581999849)
                  ·
                    rfl

theorem cell23_7322674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_7322674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322674 prefixEnd_7322674 := by exact prefixLift 7322674
  have htrace : WordTrace (prefixWord ++ tailWord_7322674) baseStart_7322674 baseEnd_7322674 := by
    simpa [prefixWord, tailWord_7322674, baseEnd_7322674] using wordTrace_append hprefix tailTrace_7322674
  have hstable : (prefixWord ++ tailWord_7322674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322674).length < 2 ^ (prefixWord ++ tailWord_7322674).sum := by decide
  have hdescent : baseEnd_7322674 < baseStart_7322674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322678 : List Nat := [5, 1, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_7322678 : Nat := 118140960795 + 7322678 * 2 ^ 59
def prefixEnd_7322678 : Nat := 4983230072969 + 3 ^ 40 * 7322678 * 2
def baseEnd_7322678 : Nat := 1253351164034735407449541

theorem tailTrace_7322678 : CollatzResearch.WordTrace tailWord_7322678 prefixEnd_7322678 1253351164034735407449541 := by
  unfold tailWord_7322678
  simp only [CollatzResearch.WordTrace]
  refine ⟨16692500510324730917566043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178053338776797129787371125 16692500510324730917566043)
  ·
    refine ⟨25038750765487096376349065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16692500510324730917566043 25038750765487096376349065)
    ·
      refine ⟨18779063074115322282261799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25038750765487096376349065 18779063074115322282261799)
      ·
        refine ⟨28168594611172983423392699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18779063074115322282261799 28168594611172983423392699)
        ·
          refine ⟨42252891916759475135089049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28168594611172983423392699 42252891916759475135089049)
          ·
            refine ⟨31689668937569606351316787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42252891916759475135089049 31689668937569606351316787)
            ·
              refine ⟨47534503406354409526975181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31689668937569606351316787 47534503406354409526975181)
              ·
                refine ⟨17825438777382903572615693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47534503406354409526975181 17825438777382903572615693)
                ·
                  refine ⟨6684539541518588839730885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17825438777382903572615693 6684539541518588839730885)
                  ·
                    refine ⟨1253351164034735407449541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6684539541518588839730885 1253351164034735407449541)
                    ·
                      rfl

theorem cell23_7322678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_7322678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322678 prefixEnd_7322678 := by exact prefixLift 7322678
  have htrace : WordTrace (prefixWord ++ tailWord_7322678) baseStart_7322678 baseEnd_7322678 := by
    simpa [prefixWord, tailWord_7322678, baseEnd_7322678] using wordTrace_append hprefix tailTrace_7322678
  have hstable : (prefixWord ++ tailWord_7322678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322678).length < 2 ^ (prefixWord ++ tailWord_7322678).sum := by decide
  have hdescent : baseEnd_7322678 < baseStart_7322678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322691 : List Nat := [1, 1, 1, 3, 1, 2, 7, 1, 6]
def baseStart_7322691 : Nat := 118140960795 + 7322691 * 2 ^ 59
def prefixEnd_7322691 : Nat := 4983230072969 + 3 ^ 40 * 7322691 * 2
def baseEnd_7322691 : Nat := 417784463039190519054007

theorem tailTrace_7322691 : CollatzResearch.WordTrace tailWord_7322691 prefixEnd_7322691 417784463039190519054007 := by
  unfold tailWord_7322691
  simp only [CollatzResearch.WordTrace]
  refine ⟨267080482314148597901279927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178053654876099065267519951 267080482314148597901279927)
  ·
    refine ⟨400620723471222896851919891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267080482314148597901279927 400620723471222896851919891)
    ·
      refine ⟨600931085206834345277879837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400620723471222896851919891 600931085206834345277879837)
      ·
        refine ⟨225349156952562879479204939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 600931085206834345277879837 225349156952562879479204939)
        ·
          refine ⟨338023735428844319218807409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225349156952562879479204939 338023735428844319218807409)
          ·
            refine ⟨253517801571633239414105557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338023735428844319218807409 253517801571633239414105557)
            ·
              refine ⟨5941823474335154048768099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 253517801571633239414105557 5941823474335154048768099)
              ·
                refine ⟨8912735211502731073152149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5941823474335154048768099 8912735211502731073152149)
                ·
                  refine ⟨417784463039190519054007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8912735211502731073152149 417784463039190519054007)
                  ·
                    rfl

theorem cell23_7322691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 6].length) (baseStart_7322691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322691 prefixEnd_7322691 := by exact prefixLift 7322691
  have htrace : WordTrace (prefixWord ++ tailWord_7322691) baseStart_7322691 baseEnd_7322691 := by
    simpa [prefixWord, tailWord_7322691, baseEnd_7322691] using wordTrace_append hprefix tailTrace_7322691
  have hstable : (prefixWord ++ tailWord_7322691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322691).length < 2 ^ (prefixWord ++ tailWord_7322691).sum := by decide
  have hdescent : baseEnd_7322691 < baseStart_7322691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322704 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 3, 5]
def baseStart_7322704 : Nat := 118140960795 + 7322704 * 2 ^ 59
def prefixEnd_7322704 : Nat := 4983230072969 + 3 ^ 40 * 7322704 * 2
def baseEnd_7322704 : Nat := 1253355614200407706874501

theorem tailTrace_7322704 : CollatzResearch.WordTrace tailWord_7322704 prefixEnd_7322704 1253355614200407706874501 := by
  unfold tailWord_7322704
  simp only [CollatzResearch.WordTrace]
  refine ⟨133540478231550750560751583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178053970975401000747668777 133540478231550750560751583)
  ·
    refine ⟨200310717347326125841127375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133540478231550750560751583 200310717347326125841127375)
    ·
      refine ⟨300466076020989188761691063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200310717347326125841127375 300466076020989188761691063)
      ·
        refine ⟨450699114031483783142536595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300466076020989188761691063 450699114031483783142536595)
        ·
          refine ⟨676048671047225674713804893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450699114031483783142536595 676048671047225674713804893)
          ·
            refine ⟨253518251642709628017676835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 676048671047225674713804893 253518251642709628017676835)
            ·
              refine ⟨380277377464064442026515253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253518251642709628017676835 380277377464064442026515253)
              ·
                refine ⟨35651004137256041439985805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 380277377464064442026515253 35651004137256041439985805)
                ·
                  refine ⟨13369126551471015539994677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35651004137256041439985805 13369126551471015539994677)
                  ·
                    refine ⟨1253355614200407706874501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13369126551471015539994677 1253355614200407706874501)
                    ·
                      rfl

theorem cell23_7322704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 3, 5].length) (baseStart_7322704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322704 prefixEnd_7322704 := by exact prefixLift 7322704
  have htrace : WordTrace (prefixWord ++ tailWord_7322704) baseStart_7322704 baseEnd_7322704 := by
    simpa [prefixWord, tailWord_7322704, baseEnd_7322704] using wordTrace_append hprefix tailTrace_7322704
  have hstable : (prefixWord ++ tailWord_7322704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322704).length < 2 ^ (prefixWord ++ tailWord_7322704).sum := by decide
  have hdescent : baseEnd_7322704 < baseStart_7322704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322721 : List Nat := [1, 2, 3, 1, 1, 2, 4, 3, 1, 5]
def baseStart_7322721 : Nat := 118140960795 + 7322721 * 2 ^ 59
def prefixEnd_7322721 : Nat := 4983230072969 + 3 ^ 40 * 7322721 * 2
def baseEnd_7322721 : Nat := 1253358523924116518036975

theorem tailTrace_7322721 : CollatzResearch.WordTrace tailWord_7322721 prefixEnd_7322721 1253358523924116518036975 := by
  unfold tailWord_7322721
  simp only [CollatzResearch.WordTrace]
  refine ⟨267081576504039913024872017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178054384336026608683248011 267081576504039913024872017)
  ·
    refine ⟨200311182378029934768654013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267081576504039913024872017 200311182378029934768654013)
    ·
      refine ⟨75116693391761225538245255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200311182378029934768654013 75116693391761225538245255)
      ·
        refine ⟨112675040087641838307367883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75116693391761225538245255 112675040087641838307367883)
        ·
          refine ⟨169012560131462757461051825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112675040087641838307367883 169012560131462757461051825)
          ·
            refine ⟨126759420098597068095788869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169012560131462757461051825 126759420098597068095788869)
            ·
              refine ⟨23767391268486950267960413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126759420098597068095788869 23767391268486950267960413)
              ·
                refine ⟨8912771725682606350485155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23767391268486950267960413 8912771725682606350485155)
                ·
                  refine ⟨13369157588523909525727733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8912771725682606350485155 13369157588523909525727733)
                  ·
                    refine ⟨1253358523924116518036975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13369157588523909525727733 1253358523924116518036975)
                    ·
                      rfl

theorem cell23_7322721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_7322721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322721 prefixEnd_7322721 := by exact prefixLift 7322721
  have htrace : WordTrace (prefixWord ++ tailWord_7322721) baseStart_7322721 baseEnd_7322721 := by
    simpa [prefixWord, tailWord_7322721, baseEnd_7322721] using wordTrace_append hprefix tailTrace_7322721
  have hstable : (prefixWord ++ tailWord_7322721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322721).length < 2 ^ (prefixWord ++ tailWord_7322721).sum := by decide
  have hdescent : baseEnd_7322721 < baseStart_7322721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322775 : List Nat := [1, 1, 3, 3, 3, 2, 3, 1, 1, 1, 4]
def baseStart_7322775 : Nat := 118140960795 + 7322775 * 2 ^ 59
def prefixEnd_7322775 : Nat := 4983230072969 + 3 ^ 40 * 7322775 * 2
def baseEnd_7322775 : Nat := 3760103299727692342835677

theorem tailTrace_7322775 : CollatzResearch.WordTrace tailWord_7322775 prefixEnd_7322775 3760103299727692342835677 := by
  unfold tailWord_7322775
  simp only [CollatzResearch.WordTrace]
  refine ⟨267083546045844280247337779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178055697363896186831558519 267083546045844280247337779)
  ·
    refine ⟨400625319068766420371006669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267083546045844280247337779 400625319068766420371006669)
    ·
      refine ⟨150234494650787407639127501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400625319068766420371006669 150234494650787407639127501)
      ·
        refine ⟨56337935494045277864672813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150234494650787407639127501 56337935494045277864672813)
        ·
          refine ⟨21126725810266979199252305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56337935494045277864672813 21126725810266979199252305)
          ·
            refine ⟨15845044357700234399439229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21126725810266979199252305 15845044357700234399439229)
            ·
              refine ⟨5941891634137587899789711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15845044357700234399439229 5941891634137587899789711)
              ·
                refine ⟨8912837451206381849684567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5941891634137587899789711 8912837451206381849684567)
                ·
                  refine ⟨13369256176809572774526851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8912837451206381849684567 13369256176809572774526851)
                  ·
                    refine ⟨20053884265214359161790277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13369256176809572774526851 20053884265214359161790277)
                    ·
                      refine ⟨3760103299727692342835677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20053884265214359161790277 3760103299727692342835677)
                      ·
                        rfl

theorem cell23_7322775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_7322775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322775 prefixEnd_7322775 := by exact prefixLift 7322775
  have htrace : WordTrace (prefixWord ++ tailWord_7322775) baseStart_7322775 baseEnd_7322775 := by
    simpa [prefixWord, tailWord_7322775, baseEnd_7322775] using wordTrace_append hprefix tailTrace_7322775
  have hstable : (prefixWord ++ tailWord_7322775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322775).length < 2 ^ (prefixWord ++ tailWord_7322775).sum := by decide
  have hdescent : baseEnd_7322775 < baseStart_7322775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322778 : List Nat := [3, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5]
def baseStart_7322778 : Nat := 118140960795 + 7322778 * 2 ^ 59
def prefixEnd_7322778 : Nat := 4983230072969 + 3 ^ 40 * 7322778 * 2
def baseEnd_7322778 : Nat := 3760104840169655831098163

theorem tailTrace_7322778 : CollatzResearch.WordTrace tailWord_7322778 prefixEnd_7322778 3760104840169655831098163 := by
  unfold tailWord_7322778
  simp only [CollatzResearch.WordTrace]
  refine ⟨66770913866208352939924247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178055770309888941173131325 66770913866208352939924247)
  ·
    refine ⟨100156370799312529409886371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66770913866208352939924247 100156370799312529409886371)
    ·
      refine ⟨150234556198968794114829557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100156370799312529409886371 150234556198968794114829557)
      ·
        refine ⟨14084489643653324448265271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150234556198968794114829557 14084489643653324448265271)
        ·
          refine ⟨21126734465479986672397907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14084489643653324448265271 21126734465479986672397907)
          ·
            refine ⟨31690101698219980008596861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21126734465479986672397907 31690101698219980008596861)
            ·
              refine ⟨11883788136832492503223823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31690101698219980008596861 11883788136832492503223823)
              ·
                refine ⟨17825682205248738754835735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11883788136832492503223823 17825682205248738754835735)
                ·
                  refine ⟨26738523307873108132253603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17825682205248738754835735 26738523307873108132253603)
                  ·
                    refine ⟨40107784961809662198380405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26738523307873108132253603 40107784961809662198380405)
                    ·
                      refine ⟨3760104840169655831098163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40107784961809662198380405 3760104840169655831098163)
                      ·
                        rfl

theorem cell23_7322778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_7322778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322778 prefixEnd_7322778 := by exact prefixLift 7322778
  have htrace : WordTrace (prefixWord ++ tailWord_7322778) baseStart_7322778 baseEnd_7322778 := by
    simpa [prefixWord, tailWord_7322778, baseEnd_7322778] using wordTrace_append hprefix tailTrace_7322778
  have hstable : (prefixWord ++ tailWord_7322778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322778).length < 2 ^ (prefixWord ++ tailWord_7322778).sum := by decide
  have hdescent : baseEnd_7322778 < baseStart_7322778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322786 : List Nat := [3, 3, 1, 3, 2, 2, 2, 2, 1, 1, 3]
def baseStart_7322786 : Nat := 118140960795 + 7322786 * 2 ^ 59
def prefixEnd_7322786 : Nat := 4983230072969 + 3 ^ 40 * 7322786 * 2
def baseEnd_7322786 : Nat := 3760108948014891799798127

theorem tailTrace_7322786 : CollatzResearch.WordTrace tailWord_7322786 prefixEnd_7322786 3760108948014891799798127 := by
  unfold tailWord_7322786
  simp only [CollatzResearch.WordTrace]
  refine ⟨66770986812201107281497053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178055964832536286083992141 66770986812201107281497053)
  ·
    refine ⟨25039120054575415230561395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66770986812201107281497053 25039120054575415230561395)
    ·
      refine ⟨37558680081863122845842093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25039120054575415230561395 37558680081863122845842093)
      ·
        refine ⟨14084505030698671067190785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37558680081863122845842093 14084505030698671067190785)
        ·
          refine ⟨10563378773024003300393089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14084505030698671067190785 10563378773024003300393089)
          ·
            refine ⟨7922534079768002475294817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10563378773024003300393089 7922534079768002475294817)
            ·
              refine ⟨5941900559826001856471113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7922534079768002475294817 5941900559826001856471113)
              ·
                refine ⟨4456425419869501392353335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5941900559826001856471113 4456425419869501392353335)
                ·
                  refine ⟨6684638129804252088530003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4456425419869501392353335 6684638129804252088530003)
                  ·
                    refine ⟨10026957194706378132795005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6684638129804252088530003 10026957194706378132795005)
                    ·
                      refine ⟨3760108948014891799798127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10026957194706378132795005 3760108948014891799798127)
                      ·
                        rfl

theorem cell23_7322786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_7322786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322786 prefixEnd_7322786 := by exact prefixLift 7322786
  have htrace : WordTrace (prefixWord ++ tailWord_7322786) baseStart_7322786 baseEnd_7322786 := by
    simpa [prefixWord, tailWord_7322786, baseEnd_7322786] using wordTrace_append hprefix tailTrace_7322786
  have hstable : (prefixWord ++ tailWord_7322786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322786).length < 2 ^ (prefixWord ++ tailWord_7322786).sum := by decide
  have hdescent : baseEnd_7322786 < baseStart_7322786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
