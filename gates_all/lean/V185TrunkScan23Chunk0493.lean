import V185TrunkScan23Chunk0492

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2917108 : List Nat := [2, 6, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_2917108 : Nat := 118140960795 + 2917108 * 2 ^ 59
def prefixEnd_2917108 : Nat := 4983230072969 + 3 ^ 40 * 2917108 * 2
def baseEnd_2917108 : Nat := 499292841691959345078157

theorem tailTrace_2917108 : CollatzResearch.WordTrace tailWord_2917108 prefixEnd_2917108 499292841691959345078157 := by
  unfold tailWord_2917108
  simp only [CollatzResearch.WordTrace]
  refine ⟨53197834757911696613795989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70930446343882262151727985 53197834757911696613795989)
  ·
    refine ⟨2493648504277110778771687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53197834757911696613795989 2493648504277110778771687)
    ·
      refine ⟨3740472756415666168157531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2493648504277110778771687 3740472756415666168157531)
      ·
        refine ⟨5610709134623499252236297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3740472756415666168157531 5610709134623499252236297)
        ·
          refine ⟨4208031850967624439177223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5610709134623499252236297 4208031850967624439177223)
          ·
            refine ⟨6312047776451436658765835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4208031850967624439177223 6312047776451436658765835)
            ·
              refine ⟨9468071664677154988148753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6312047776451436658765835 9468071664677154988148753)
              ·
                refine ⟨7101053748507866241111565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9468071664677154988148753 7101053748507866241111565)
                ·
                  refine ⟨2662895155690449840416837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7101053748507866241111565 2662895155690449840416837)
                  ·
                    refine ⟨499292841691959345078157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2662895155690449840416837 499292841691959345078157)
                    ·
                      rfl

theorem cell23_2917108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_2917108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917108 prefixEnd_2917108 := by exact prefixLift 2917108
  have htrace : WordTrace (prefixWord ++ tailWord_2917108) baseStart_2917108 baseEnd_2917108 := by
    simpa [prefixWord, tailWord_2917108, baseEnd_2917108] using wordTrace_append hprefix tailTrace_2917108
  have hstable : (prefixWord ++ tailWord_2917108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917108).length < 2 ^ (prefixWord ++ tailWord_2917108).sum := by decide
  have hdescent : baseEnd_2917108 < baseStart_2917108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917117 : List Nat := [1, 4, 1, 1, 1, 1, 4, 4, 1, 5]
def baseStart_2917117 : Nat := 118140960795 + 2917117 * 2 ^ 59
def prefixEnd_2917117 : Nat := 4983230072969 + 3 ^ 40 * 2917117 * 2
def baseEnd_2917117 : Nat := 499294382133922833340643

theorem tailTrace_2917117 : CollatzResearch.WordTrace tailWord_2917117 prefixEnd_2917117 499294382133922833340643 := by
  unfold tailWord_2917117
  simp only [CollatzResearch.WordTrace]
  refine ⟨106395997772790787764669605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70930665181860525176446403 106395997772790787764669605)
  ·
    refine ⟨19949249582398272705875551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106395997772790787764669605 19949249582398272705875551)
    ·
      refine ⟨29923874373597409058813327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19949249582398272705875551 29923874373597409058813327)
      ·
        refine ⟨44885811560396113588219991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29923874373597409058813327 44885811560396113588219991)
        ·
          refine ⟨67328717340594170382329987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44885811560396113588219991 67328717340594170382329987)
          ·
            refine ⟨100993076010891255573494981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67328717340594170382329987 100993076010891255573494981)
            ·
              refine ⟨18936201752042110420030309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100993076010891255573494981 18936201752042110420030309)
              ·
                refine ⟨3550537828507895703755683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18936201752042110420030309 3550537828507895703755683)
                ·
                  refine ⟨5325806742761843555633525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3550537828507895703755683 5325806742761843555633525)
                  ·
                    refine ⟨499294382133922833340643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5325806742761843555633525 499294382133922833340643)
                    ·
                      rfl

theorem cell23_2917117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_2917117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917117 prefixEnd_2917117 := by exact prefixLift 2917117
  have htrace : WordTrace (prefixWord ++ tailWord_2917117) baseStart_2917117 baseEnd_2917117 := by
    simpa [prefixWord, tailWord_2917117, baseEnd_2917117] using wordTrace_append hprefix tailTrace_2917117
  have hstable : (prefixWord ++ tailWord_2917117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917117).length < 2 ^ (prefixWord ++ tailWord_2917117).sum := by decide
  have hdescent : baseEnd_2917117 < baseStart_2917117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917124 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 1, 5, 2]
def baseStart_2917124 : Nat := 118140960795 + 2917124 * 2 ^ 59
def prefixEnd_2917124 : Nat := 4983230072969 + 3 ^ 40 * 2917124 * 2
def baseEnd_2917124 : Nat := 1497886740766349972634397

theorem tailTrace_2917124 : CollatzResearch.WordTrace tailWord_2917124 prefixEnd_2917124 1497886740766349972634397 := by
  unfold tailWord_2917124
  simp only [CollatzResearch.WordTrace]
  refine ⟨53198126541882713980087213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70930835389176951973449617 53198126541882713980087213)
  ·
    refine ⟨19949297453206017742532705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53198126541882713980087213 19949297453206017742532705)
    ·
      refine ⟨14961973089904513306899529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19949297453206017742532705 14961973089904513306899529)
      ·
        refine ⟨11221479817428384980174647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14961973089904513306899529 11221479817428384980174647)
        ·
          refine ⟨16832219726142577470261971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11221479817428384980174647 16832219726142577470261971)
          ·
            refine ⟨25248329589213866205392957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16832219726142577470261971 25248329589213866205392957)
            ·
              refine ⟨9468123595955199827022359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25248329589213866205392957 9468123595955199827022359)
              ·
                refine ⟨14202185393932799740533539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9468123595955199827022359 14202185393932799740533539)
                ·
                  refine ⟨21303278090899199610800309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14202185393932799740533539 21303278090899199610800309)
                  ·
                    refine ⟨1997182321021799963512529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21303278090899199610800309 1997182321021799963512529)
                    ·
                      refine ⟨1497886740766349972634397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1997182321021799963512529 1497886740766349972634397)
                      ·
                        rfl

theorem cell23_2917124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_2917124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917124 prefixEnd_2917124 := by exact prefixLift 2917124
  have htrace : WordTrace (prefixWord ++ tailWord_2917124) baseStart_2917124 baseEnd_2917124 := by
    simpa [prefixWord, tailWord_2917124, baseEnd_2917124] using wordTrace_append hprefix tailTrace_2917124
  have hstable : (prefixWord ++ tailWord_2917124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917124).length < 2 ^ (prefixWord ++ tailWord_2917124).sum := by decide
  have hdescent : baseEnd_2917124 < baseStart_2917124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917138 : List Nat := [3, 2, 4, 1, 3, 1, 1, 2, 6]
def baseStart_2917138 : Nat := 118140960795 + 2917138 * 2 ^ 59
def prefixEnd_2917138 : Nat := 4983230072969 + 3 ^ 40 * 2917138 * 2
def baseEnd_2917138 : Nat := 166432658832834768651037

theorem tailTrace_2917138 : CollatzResearch.WordTrace tailWord_2917138 prefixEnd_2917138 166432658832834768651037 := by
  unfold tailWord_2917138
  simp only [CollatzResearch.WordTrace]
  refine ⟨26599190926428677087796017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70931175803809805567456045 26599190926428677087796017)
  ·
    refine ⟨19949393194821507815847013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26599190926428677087796017 19949393194821507815847013)
    ·
      refine ⟨3740511224029032715471315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19949393194821507815847013 3740511224029032715471315)
      ·
        refine ⟨5610766836043549073206973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3740511224029032715471315 5610766836043549073206973)
        ·
          refine ⟨2104037563516330902452615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5610766836043549073206973 2104037563516330902452615)
          ·
            refine ⟨3156056345274496353678923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2104037563516330902452615 3156056345274496353678923)
            ·
              refine ⟨4734084517911744530518385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3156056345274496353678923 4734084517911744530518385)
              ·
                refine ⟨3550563388433808397888789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4734084517911744530518385 3550563388433808397888789)
                ·
                  refine ⟨166432658832834768651037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3550563388433808397888789 166432658832834768651037)
                  ·
                    rfl

theorem cell23_2917138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_2917138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917138 prefixEnd_2917138 := by exact prefixLift 2917138
  have htrace : WordTrace (prefixWord ++ tailWord_2917138) baseStart_2917138 baseEnd_2917138 := by
    simpa [prefixWord, tailWord_2917138, baseEnd_2917138] using wordTrace_append hprefix tailTrace_2917138
  have hstable : (prefixWord ++ tailWord_2917138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917138).length < 2 ^ (prefixWord ++ tailWord_2917138).sum := by decide
  have hdescent : baseEnd_2917138 < baseStart_2917138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917157 : List Nat := [1, 3, 1, 2, 3, 1, 3, 2, 1, 1, 5]
def baseStart_2917157 : Nat := 118140960795 + 2917157 * 2 ^ 59
def prefixEnd_2917157 : Nat := 4983230072969 + 3 ^ 40 * 2917157 * 2
def baseEnd_2917157 : Nat := 1497903685627948343521745

theorem tailTrace_2917157 : CollatzResearch.WordTrace tailWord_2917157 prefixEnd_2917157 1497903685627948343521745 := by
  unfold tailWord_2917157
  simp only [CollatzResearch.WordTrace]
  refine ⟨106397456692645874596125725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70931637795097249730750483 106397456692645874596125725)
  ·
    refine ⟨39899046259742202973547147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106397456692645874596125725 39899046259742202973547147)
    ·
      refine ⟨59848569389613304460320721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39899046259742202973547147 59848569389613304460320721)
      ·
        refine ⟨44886427042209978345240541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59848569389613304460320721 44886427042209978345240541)
        ·
          refine ⟨16832410140828741879465203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44886427042209978345240541 16832410140828741879465203)
          ·
            refine ⟨25248615211243112819197805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16832410140828741879465203 25248615211243112819197805)
            ·
              refine ⟨9468230704216167307199177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25248615211243112819197805 9468230704216167307199177)
              ·
                refine ⟨7101173028162125480399383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9468230704216167307199177 7101173028162125480399383)
                ·
                  refine ⟨10651759542243188220599075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7101173028162125480399383 10651759542243188220599075)
                  ·
                    refine ⟨15977639313364782330898613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10651759542243188220599075 15977639313364782330898613)
                    ·
                      refine ⟨1497903685627948343521745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15977639313364782330898613 1497903685627948343521745)
                      ·
                        rfl

theorem cell23_2917157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_2917157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917157 prefixEnd_2917157 := by exact prefixLift 2917157
  have htrace : WordTrace (prefixWord ++ tailWord_2917157) baseStart_2917157 baseEnd_2917157 := by
    simpa [prefixWord, tailWord_2917157, baseEnd_2917157] using wordTrace_append hprefix tailTrace_2917157
  have hstable : (prefixWord ++ tailWord_2917157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917157).length < 2 ^ (prefixWord ++ tailWord_2917157).sum := by decide
  have hdescent : baseEnd_2917157 < baseStart_2917157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917171 : List Nat := [1, 1, 1, 2, 6, 1, 2, 2, 3, 2, 2]
def baseStart_2917171 : Nat := 118140960795 + 2917171 * 2 ^ 59
def prefixEnd_2917171 : Nat := 4983230072969 + 3 ^ 40 * 2917171 * 2
def baseEnd_2917171 : Nat := 1497910874357111288746681

theorem tailTrace_2917171 : CollatzResearch.WordTrace tailWord_2917171 prefixEnd_2917171 1497910874357111288746681 := by
  unfold tailWord_2917171
  simp only [CollatzResearch.WordTrace]
  refine ⟨106397967314595154987135367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70931978209730103324756911 106397967314595154987135367)
  ·
    refine ⟨159596950971892732480703051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106397967314595154987135367 159596950971892732480703051)
    ·
      refine ⟨239395426457839098721054577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159596950971892732480703051 239395426457839098721054577)
      ·
        refine ⟨179546569843379324040790933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239395426457839098721054577 179546569843379324040790933)
        ·
          refine ⟨8416245461408405814412075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 179546569843379324040790933 8416245461408405814412075)
          ·
            refine ⟨12624368192112608721618113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8416245461408405814412075 12624368192112608721618113)
            ·
              refine ⟨9468276144084456541213585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12624368192112608721618113 9468276144084456541213585)
              ·
                refine ⟨7101207108063342405910189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9468276144084456541213585 7101207108063342405910189)
                ·
                  refine ⟨2662952665523753402216321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7101207108063342405910189 2662952665523753402216321)
                  ·
                    refine ⟨1997214499142815051662241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2662952665523753402216321 1997214499142815051662241)
                    ·
                      refine ⟨1497910874357111288746681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1997214499142815051662241 1497910874357111288746681)
                      ·
                        rfl

theorem cell23_2917171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 2, 2].length) (baseStart_2917171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917171 prefixEnd_2917171 := by exact prefixLift 2917171
  have htrace : WordTrace (prefixWord ++ tailWord_2917171) baseStart_2917171 baseEnd_2917171 := by
    simpa [prefixWord, tailWord_2917171, baseEnd_2917171] using wordTrace_append hprefix tailTrace_2917171
  have hstable : (prefixWord ++ tailWord_2917171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917171).length < 2 ^ (prefixWord ++ tailWord_2917171).sum := by decide
  have hdescent : baseEnd_2917171 < baseStart_2917171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917182 : List Nat := [4, 2, 1, 2, 4, 1, 1, 3, 1, 1, 3]
def baseStart_2917182 : Nat := 118140960795 + 2917182 * 2 ^ 59
def prefixEnd_2917182 : Nat := 4983230072969 + 3 ^ 40 * 2917182 * 2
def baseEnd_2917182 : Nat := 1497916522644310745709131

theorem tailTrace_2917182 : CollatzResearch.WordTrace tailWord_2917182 prefixEnd_2917182 1497916522644310745709131 := by
  unfold tailWord_2917182
  simp only [CollatzResearch.WordTrace]
  refine ⟨13299796064694412983223225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70932245678370202577190533 13299796064694412983223225)
  ·
    refine ⟨9974847048520809737417419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13299796064694412983223225 9974847048520809737417419)
    ·
      refine ⟨14962270572781214606126129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9974847048520809737417419 14962270572781214606126129)
      ·
        refine ⟨11221702929585910954594597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14962270572781214606126129 11221702929585910954594597)
        ·
          refine ⟨2104069299297358303986487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11221702929585910954594597 2104069299297358303986487)
          ·
            refine ⟨3156103948946037455979731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2104069299297358303986487 3156103948946037455979731)
            ·
              refine ⟨4734155923419056183969597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3156103948946037455979731 4734155923419056183969597)
              ·
                refine ⟨1775308471282146068988599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4734155923419056183969597 1775308471282146068988599)
                ·
                  refine ⟨2662962706923219103482899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1775308471282146068988599 2662962706923219103482899)
                  ·
                    refine ⟨3994444060384828655224349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2662962706923219103482899 3994444060384828655224349)
                    ·
                      refine ⟨1497916522644310745709131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3994444060384828655224349 1497916522644310745709131)
                      ·
                        rfl

theorem cell23_2917182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_2917182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917182 prefixEnd_2917182 := by exact prefixLift 2917182
  have htrace : WordTrace (prefixWord ++ tailWord_2917182) baseStart_2917182 baseEnd_2917182 := by
    simpa [prefixWord, tailWord_2917182, baseEnd_2917182] using wordTrace_append hprefix tailTrace_2917182
  have hstable : (prefixWord ++ tailWord_2917182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917182).length < 2 ^ (prefixWord ++ tailWord_2917182).sum := by decide
  have hdescent : baseEnd_2917182 < baseStart_2917182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917187 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 3]
def baseStart_2917187 : Nat := 118140960795 + 2917187 * 2 ^ 59
def prefixEnd_2917187 : Nat := 4983230072969 + 3 ^ 40 * 2917187 * 2
def baseEnd_2917187 : Nat := 1497919090047583226146607

theorem tailTrace_2917187 : CollatzResearch.WordTrace tailWord_2917187 prefixEnd_2917187 1497919090047583226146607 := by
  unfold tailWord_2917187
  simp only [CollatzResearch.WordTrace]
  refine ⟨106398550882537189719717815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70932367255024793146478543 106398550882537189719717815)
  ·
    refine ⟨159597826323805784579576723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106398550882537189719717815 159597826323805784579576723)
    ·
      refine ⟨239396739485708676869365085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159597826323805784579576723 239396739485708676869365085)
      ·
        refine ⟨89773777307140753826011907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239396739485708676869365085 89773777307140753826011907)
        ·
          refine ⟨134660665960711130739017861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89773777307140753826011907 134660665960711130739017861)
          ·
            refine ⟨25248874867633337013565849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134660665960711130739017861 25248874867633337013565849)
            ·
              refine ⟨18936656150725002760174387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25248874867633337013565849 18936656150725002760174387)
              ·
                refine ⟨28404984226087504140261581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18936656150725002760174387 28404984226087504140261581)
                ·
                  refine ⟨10651869084782814052598093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28404984226087504140261581 10651869084782814052598093)
                  ·
                    refine ⟨3994450906793555269724285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10651869084782814052598093 3994450906793555269724285)
                    ·
                      refine ⟨1497919090047583226146607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3994450906793555269724285 1497919090047583226146607)
                      ·
                        rfl

theorem cell23_2917187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_2917187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917187 prefixEnd_2917187 := by exact prefixLift 2917187
  have htrace : WordTrace (prefixWord ++ tailWord_2917187) baseStart_2917187 baseEnd_2917187 := by
    simpa [prefixWord, tailWord_2917187, baseEnd_2917187] using wordTrace_append hprefix tailTrace_2917187
  have hstable : (prefixWord ++ tailWord_2917187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917187).length < 2 ^ (prefixWord ++ tailWord_2917187).sum := by decide
  have hdescent : baseEnd_2917187 < baseStart_2917187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917205 : List Nat := [1, 3, 2, 2, 2, 1, 5, 2, 1, 2, 2]
def baseStart_2917205 : Nat := 118140960795 + 2917205 * 2 ^ 59
def prefixEnd_2917205 : Nat := 4983230072969 + 3 ^ 40 * 2917205 * 2
def baseEnd_2917205 : Nat := 1497928332699364155721525

theorem tailTrace_2917205 : CollatzResearch.WordTrace tailWord_2917205 prefixEnd_2917205 1497928332699364155721525 := by
  unfold tailWord_2917205
  simp only [CollatzResearch.WordTrace]
  refine ⟨106399207396471978793873069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70932804930981319195915379 106399207396471978793873069)
  ·
    refine ⟨39899702773676992047702401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106399207396471978793873069 39899702773676992047702401)
    ·
      refine ⟨29924777080257744035776801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39899702773676992047702401 29924777080257744035776801)
      ·
        refine ⟨22443582810193308026832601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29924777080257744035776801 22443582810193308026832601)
        ·
          refine ⟨16832687107644981020124451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22443582810193308026832601 16832687107644981020124451)
          ·
            refine ⟨25249030661467471530186677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16832687107644981020124451 25249030661467471530186677)
            ·
              refine ⟨2367096624512575455955001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25249030661467471530186677 2367096624512575455955001)
              ·
                refine ⟨1775322468384431591966251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2367096624512575455955001 1775322468384431591966251)
                ·
                  refine ⟨2662983702576647387949377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1775322468384431591966251 2662983702576647387949377)
                  ·
                    refine ⟨1997237776932485540962033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2662983702576647387949377 1997237776932485540962033)
                    ·
                      refine ⟨1497928332699364155721525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1997237776932485540962033 1497928332699364155721525)
                      ·
                        rfl

theorem cell23_2917205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_2917205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917205 prefixEnd_2917205 := by exact prefixLift 2917205
  have htrace : WordTrace (prefixWord ++ tailWord_2917205) baseStart_2917205 baseEnd_2917205 := by
    simpa [prefixWord, tailWord_2917205, baseEnd_2917205] using wordTrace_append hprefix tailTrace_2917205
  have hstable : (prefixWord ++ tailWord_2917205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917205).length < 2 ^ (prefixWord ++ tailWord_2917205).sum := by decide
  have hdescent : baseEnd_2917205 < baseStart_2917205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917247 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 5]
def baseStart_2917247 : Nat := 118140960795 + 2917247 * 2 ^ 59
def prefixEnd_2917247 : Nat := 4983230072969 + 3 ^ 40 * 2917247 * 2
def baseEnd_2917247 : Nat := 1497949898886852991396331

theorem tailTrace_2917247 : CollatzResearch.WordTrace tailWord_2917247 prefixEnd_2917247 1497949898886852991396331 := by
  unfold tailWord_2917247
  simp only [CollatzResearch.WordTrace]
  refine ⟨106400739262319819966901995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70933826174879879977934663 106400739262319819966901995)
  ·
    refine ⟨159601108893479729950352993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106400739262319819966901995 159601108893479729950352993)
    ·
      refine ⟨119700831670109797462764745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159601108893479729950352993 119700831670109797462764745)
      ·
        refine ⟨89775623752582348097073559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119700831670109797462764745 89775623752582348097073559)
        ·
          refine ⟨134663435628873522145610339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89775623752582348097073559 134663435628873522145610339)
          ·
            refine ⟨201995153443310283218415509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134663435628873522145610339 201995153443310283218415509)
            ·
              refine ⟨9468522817655169525863227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 201995153443310283218415509 9468522817655169525863227)
              ·
                refine ⟨14202784226482754288794841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9468522817655169525863227 14202784226482754288794841)
                ·
                  refine ⟨10652088169862065716596131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14202784226482754288794841 10652088169862065716596131)
                  ·
                    refine ⟨15978132254793098574894197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10652088169862065716596131 15978132254793098574894197)
                    ·
                      refine ⟨1497949898886852991396331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15978132254793098574894197 1497949898886852991396331)
                      ·
                        rfl

theorem cell23_2917247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_2917247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917247 prefixEnd_2917247 := by exact prefixLift 2917247
  have htrace : WordTrace (prefixWord ++ tailWord_2917247) baseStart_2917247 baseEnd_2917247 := by
    simpa [prefixWord, tailWord_2917247, baseEnd_2917247] using wordTrace_append hprefix tailTrace_2917247
  have hstable : (prefixWord ++ tailWord_2917247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917247).length < 2 ^ (prefixWord ++ tailWord_2917247).sum := by decide
  have hdescent : baseEnd_2917247 < baseStart_2917247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917301 : List Nat := [1, 3, 3, 2, 1, 1, 4, 3, 5]
def baseStart_2917301 : Nat := 118140960795 + 2917301 * 2 ^ 59
def prefixEnd_2917301 : Nat := 4983230072969 + 3 ^ 40 * 2917301 * 2
def baseEnd_2917301 : Nat := 166441958538021753346787

theorem tailTrace_2917301 : CollatzResearch.WordTrace tailWord_2917301 prefixEnd_2917301 166441958538021753346787 := by
  unfold tailWord_2917301
  simp only [CollatzResearch.WordTrace]
  refine ⟨106402708804124187189367757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70935139202749458126245171 106402708804124187189367757)
  ·
    refine ⟨39901015801546570196012909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106402708804124187189367757 39901015801546570196012909)
    ·
      refine ⟨14962880925579963823504841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39901015801546570196012909 14962880925579963823504841)
      ·
        refine ⟨11222160694184972867628631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14962880925579963823504841 11222160694184972867628631)
        ·
          refine ⟨16833241041277459301442947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11222160694184972867628631 16833241041277459301442947)
          ·
            refine ⟨25249861561916188952164421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16833241041277459301442947 25249861561916188952164421)
            ·
              refine ⟨4734349042859285428530829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25249861561916188952164421 4734349042859285428530829)
              ·
                refine ⟨1775380891072232035699061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4734349042859285428530829 1775380891072232035699061)
                ·
                  refine ⟨166441958538021753346787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1775380891072232035699061 166441958538021753346787)
                  ·
                    rfl

theorem cell23_2917301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 5].length) (baseStart_2917301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917301 prefixEnd_2917301 := by exact prefixLift 2917301
  have htrace : WordTrace (prefixWord ++ tailWord_2917301) baseStart_2917301 baseEnd_2917301 := by
    simpa [prefixWord, tailWord_2917301, baseEnd_2917301] using wordTrace_append hprefix tailTrace_2917301
  have hstable : (prefixWord ++ tailWord_2917301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917301).length < 2 ^ (prefixWord ++ tailWord_2917301).sum := by decide
  have hdescent : baseEnd_2917301 < baseStart_2917301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917401 : List Nat := [1, 2, 1, 2, 1, 1, 4, 4, 3, 1, 3]
def baseStart_2917401 : Nat := 118140960795 + 2917401 * 2 ^ 59
def prefixEnd_2917401 : Nat := 4983230072969 + 3 ^ 40 * 2917401 * 2
def baseEnd_2917401 : Nat := 1498028974907645388870623

theorem tailTrace_2917401 : CollatzResearch.WordTrace tailWord_2917401 prefixEnd_2917401 1498028974907645388870623 := by
  unfold tailWord_2917401
  simp only [CollatzResearch.WordTrace]
  refine ⟨106406356103761904268008057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70937570735841269512005371 106406356103761904268008057)
  ·
    refine ⟨79804767077821428201006043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106406356103761904268008057 79804767077821428201006043)
    ·
      refine ⟨119707150616732142301509065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79804767077821428201006043 119707150616732142301509065)
      ·
        refine ⟨89780362962549106726131799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119707150616732142301509065 89780362962549106726131799)
        ·
          refine ⟨134670544443823660089197699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89780362962549106726131799 134670544443823660089197699)
          ·
            refine ⟨202005816665735490133796549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134670544443823660089197699 202005816665735490133796549)
            ·
              refine ⟨37876090624825404400086853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202005816665735490133796549 37876090624825404400086853)
              ·
                refine ⟨7101766992154763325016285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37876090624825404400086853 7101766992154763325016285)
                ·
                  refine ⟨2663162622058036246881107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7101766992154763325016285 2663162622058036246881107)
                  ·
                    refine ⟨3994743933087054370321661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2663162622058036246881107 3994743933087054370321661)
                    ·
                      refine ⟨1498028974907645388870623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3994743933087054370321661 1498028974907645388870623)
                      ·
                        rfl

theorem cell23_2917401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 1, 3].length) (baseStart_2917401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917401 prefixEnd_2917401 := by exact prefixLift 2917401
  have htrace : WordTrace (prefixWord ++ tailWord_2917401) baseStart_2917401 baseEnd_2917401 := by
    simpa [prefixWord, tailWord_2917401, baseEnd_2917401] using wordTrace_append hprefix tailTrace_2917401
  have hstable : (prefixWord ++ tailWord_2917401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917401).length < 2 ^ (prefixWord ++ tailWord_2917401).sum := by decide
  have hdescent : baseEnd_2917401 < baseStart_2917401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917461 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 3, 2, 3]
def baseStart_2917461 : Nat := 118140960795 + 2917461 * 2 ^ 59
def prefixEnd_2917461 : Nat := 4983230072969 + 3 ^ 40 * 2917461 * 2
def baseEnd_2917461 : Nat := 1498059783746915154120347

theorem tailTrace_2917461 : CollatzResearch.WordTrace tailWord_2917461 prefixEnd_2917461 1498059783746915154120347 := by
  unfold tailWord_2917461
  simp only [CollatzResearch.WordTrace]
  refine ⟨106408544483544534515192237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70939029655696356343461491 106408544483544534515192237)
  ·
    refine ⟨39903204181329200443197089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106408544483544534515192237 39903204181329200443197089)
    ·
      refine ⟨29927403135996900332397817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39903204181329200443197089 29927403135996900332397817)
      ·
        refine ⟨22445552351997675249298363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29927403135996900332397817 22445552351997675249298363)
        ·
          refine ⟨33668328527996512873947545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22445552351997675249298363 33668328527996512873947545)
          ·
            refine ⟨25251246395997384655460659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33668328527996512873947545 25251246395997384655460659)
            ·
              refine ⟨37876869593996076983190989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25251246395997384655460659 37876869593996076983190989)
              ·
                refine ⟨14203826097748528868696621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37876869593996076983190989 14203826097748528868696621)
                ·
                  refine ⟨5326434786655698325761233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14203826097748528868696621 5326434786655698325761233)
                  ·
                    refine ⟨3994826089991773744320925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5326434786655698325761233 3994826089991773744320925)
                    ·
                      refine ⟨1498059783746915154120347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3994826089991773744320925 1498059783746915154120347)
                      ·
                        rfl

theorem cell23_2917461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_2917461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917461 prefixEnd_2917461 := by exact prefixLift 2917461
  have htrace : WordTrace (prefixWord ++ tailWord_2917461) baseStart_2917461 baseEnd_2917461 := by
    simpa [prefixWord, tailWord_2917461, baseEnd_2917461] using wordTrace_append hprefix tailTrace_2917461
  have hstable : (prefixWord ++ tailWord_2917461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917461).length < 2 ^ (prefixWord ++ tailWord_2917461).sum := by decide
  have hdescent : baseEnd_2917461 < baseStart_2917461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917462 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_2917462 : Nat := 118140960795 + 2917462 * 2 ^ 59
def prefixEnd_2917462 : Nat := 4983230072969 + 3 ^ 40 * 2917462 * 2
def baseEnd_2917462 : Nat := 1498060297227569650207843

theorem tailTrace_2917462 : CollatzResearch.WordTrace tailWord_2917462 prefixEnd_2917462 1498060297227569650207843 := by
  unfold tailWord_2917462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6650536309783806980373665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70939053971027274457319093 6650536309783806980373665)
  ·
    refine ⟨4987902232337855235280249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6650536309783806980373665 4987902232337855235280249)
    ·
      refine ⟨3740926674253391426460187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4987902232337855235280249 3740926674253391426460187)
      ·
        refine ⟨5611390011380087139690281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3740926674253391426460187 5611390011380087139690281)
        ·
          refine ⟨4208542508535065354767711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5611390011380087139690281 4208542508535065354767711)
          ·
            refine ⟨6312813762802598032151567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4208542508535065354767711 6312813762802598032151567)
            ·
              refine ⟨9469220644203897048227351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6312813762802598032151567 9469220644203897048227351)
              ·
                refine ⟨14203830966305845572341027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9469220644203897048227351 14203830966305845572341027)
                ·
                  refine ⟨21305746449458768358511541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14203830966305845572341027 21305746449458768358511541)
                  ·
                    refine ⟨1997413729636759533610457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21305746449458768358511541 1997413729636759533610457)
                    ·
                      refine ⟨1498060297227569650207843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1997413729636759533610457 1498060297227569650207843)
                      ·
                        rfl

theorem cell23_2917462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_2917462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917462 prefixEnd_2917462 := by exact prefixLift 2917462
  have htrace : WordTrace (prefixWord ++ tailWord_2917462) baseStart_2917462 baseEnd_2917462 := by
    simpa [prefixWord, tailWord_2917462, baseEnd_2917462] using wordTrace_append hprefix tailTrace_2917462
  have hstable : (prefixWord ++ tailWord_2917462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917462).length < 2 ^ (prefixWord ++ tailWord_2917462).sum := by decide
  have hdescent : baseEnd_2917462 < baseStart_2917462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917469 : List Nat := [1, 4, 4, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_2917469 : Nat := 118140960795 + 2917469 * 2 ^ 59
def prefixEnd_2917469 : Nat := 4983230072969 + 3 ^ 40 * 2917469 * 2
def baseEnd_2917469 : Nat := 1498063891592151122820311

theorem tailTrace_2917469 : CollatzResearch.WordTrace tailWord_2917469 prefixEnd_2917469 1498063891592151122820311 := by
  unfold tailWord_2917469
  simp only [CollatzResearch.WordTrace]
  refine ⟨106408836267515551881483461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70939224178343701254322307 106408836267515551881483461)
  ·
    refine ⟨19951656800159165977778149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106408836267515551881483461 19951656800159165977778149)
    ·
      refine ⟨3740935650029843620833403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19951656800159165977778149 3740935650029843620833403)
      ·
        refine ⟨5611403475044765431250105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3740935650029843620833403 5611403475044765431250105)
        ·
          refine ⟨4208552606283574073437579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5611403475044765431250105 4208552606283574073437579)
          ·
            refine ⟨6312828909425361110156369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4208552606283574073437579 6312828909425361110156369)
            ·
              refine ⟨4734621682069020832617277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6312828909425361110156369 4734621682069020832617277)
              ·
                refine ⟨1775483130775882812231479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4734621682069020832617277 1775483130775882812231479)
                ·
                  refine ⟨2663224696163824218347219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1775483130775882812231479 2663224696163824218347219)
                  ·
                    refine ⟨3994837044245736327520829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2663224696163824218347219 3994837044245736327520829)
                    ·
                      refine ⟨1498063891592151122820311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3994837044245736327520829 1498063891592151122820311)
                      ·
                        rfl

theorem cell23_2917469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_2917469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917469 prefixEnd_2917469 := by exact prefixLift 2917469
  have htrace : WordTrace (prefixWord ++ tailWord_2917469) baseStart_2917469 baseEnd_2917469 := by
    simpa [prefixWord, tailWord_2917469, baseEnd_2917469] using wordTrace_append hprefix tailTrace_2917469
  have hstable : (prefixWord ++ tailWord_2917469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917469).length < 2 ^ (prefixWord ++ tailWord_2917469).sum := by decide
  have hdescent : baseEnd_2917469 < baseStart_2917469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917485 : List Nat := [1, 5, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_2917485 : Nat := 118140960795 + 2917485 * 2 ^ 59
def prefixEnd_2917485 : Nat := 4983230072969 + 3 ^ 40 * 2917485 * 2
def baseEnd_2917485 : Nat := 499357369094207686740079

theorem tailTrace_2917485 : CollatzResearch.WordTrace tailWord_2917485 prefixEnd_2917485 499357369094207686740079 := by
  unfold tailWord_2917485
  simp only [CollatzResearch.WordTrace]
  refine ⟨106409419835457586614065909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70939613223638391076043939 106409419835457586614065909)
  ·
    refine ⟨9975883109574148745068679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106409419835457586614065909 9975883109574148745068679)
    ·
      refine ⟨14963824664361223117603019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9975883109574148745068679 14963824664361223117603019)
      ·
        refine ⟨22445736996541834676404529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14963824664361223117603019 22445736996541834676404529)
        ·
          refine ⟨16834302747406376007303397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22445736996541834676404529 16834302747406376007303397)
          ·
            refine ⟨3156431765138695501369387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16834302747406376007303397 3156431765138695501369387)
            ·
              refine ⟨4734647647708043252054081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3156431765138695501369387 4734647647708043252054081)
              ·
                refine ⟨3550985735781032439040561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4734647647708043252054081 3550985735781032439040561)
                ·
                  refine ⟨2663239301835774329280421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3550985735781032439040561 2663239301835774329280421)
                  ·
                    refine ⟨499357369094207686740079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2663239301835774329280421 499357369094207686740079)
                    ·
                      rfl

theorem cell23_2917485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_2917485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917485 prefixEnd_2917485 := by exact prefixLift 2917485
  have htrace : WordTrace (prefixWord ++ tailWord_2917485) baseStart_2917485 baseEnd_2917485 := by
    simpa [prefixWord, tailWord_2917485, baseEnd_2917485] using wordTrace_append hprefix tailTrace_2917485
  have hstable : (prefixWord ++ tailWord_2917485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917485).length < 2 ^ (prefixWord ++ tailWord_2917485).sum := by decide
  have hdescent : baseEnd_2917485 < baseStart_2917485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917508 : List Nat := [2, 3, 2, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_2917508 : Nat := 118140960795 + 2917508 * 2 ^ 59
def prefixEnd_2917508 : Nat := 4983230072969 + 3 ^ 40 * 2917508 * 2
def baseEnd_2917508 : Nat := 1498083917337676470232631

theorem tailTrace_2917508 : CollatzResearch.WordTrace tailWord_2917508 prefixEnd_2917508 1498083917337676470232631 := by
  unfold tailWord_2917508
  simp only [CollatzResearch.WordTrace]
  refine ⟨53205129357187130771076589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70940172476249507694768785 53205129357187130771076589)
  ·
    refine ⟨19951923508945174039153721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53205129357187130771076589 19951923508945174039153721)
    ·
      refine ⟨14963942631708880529365291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19951923508945174039153721 14963942631708880529365291)
      ·
        refine ⟨22445913947563320794047937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14963942631708880529365291 22445913947563320794047937)
        ·
          refine ⟨16834435460672490595535953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22445913947563320794047937 16834435460672490595535953)
          ·
            refine ⟨12625826595504367946651965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16834435460672490595535953 12625826595504367946651965)
            ·
              refine ⟨4734684973314137979994487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12625826595504367946651965 4734684973314137979994487)
              ·
                refine ⟨7102027459971206969991731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4734684973314137979994487 7102027459971206969991731)
                ·
                  refine ⟨10653041189956810454987597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7102027459971206969991731 10653041189956810454987597)
                  ·
                    refine ⟨3994890446233803920620349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10653041189956810454987597 3994890446233803920620349)
                    ·
                      refine ⟨1498083917337676470232631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3994890446233803920620349 1498083917337676470232631)
                      ·
                        rfl

theorem cell23_2917508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_2917508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917508 prefixEnd_2917508 := by exact prefixLift 2917508
  have htrace : WordTrace (prefixWord ++ tailWord_2917508) baseStart_2917508 baseEnd_2917508 := by
    simpa [prefixWord, tailWord_2917508, baseEnd_2917508] using wordTrace_append hprefix tailTrace_2917508
  have hstable : (prefixWord ++ tailWord_2917508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917508).length < 2 ^ (prefixWord ++ tailWord_2917508).sum := by decide
  have hdescent : baseEnd_2917508 < baseStart_2917508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917569 : List Nat := [1, 2, 6, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_2917569 : Nat := 118140960795 + 2917569 * 2 ^ 59
def prefixEnd_2917569 : Nat := 4983230072969 + 3 ^ 40 * 2917569 * 2
def baseEnd_2917569 : Nat := 1498115239657600731569851

theorem tailTrace_2917569 : CollatzResearch.WordTrace tailWord_2917569 prefixEnd_2917569 1498115239657600731569851 := by
  unfold tailWord_2917569
  simp only [CollatzResearch.WordTrace]
  refine ⟨106412483567153268960123761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70941655711435512640082507 106412483567153268960123761)
  ·
    refine ⟨79809362675364951720092821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106412483567153268960123761 79809362675364951720092821)
    ·
      refine ⟨3741063875407732111879351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79809362675364951720092821 3741063875407732111879351)
      ·
        refine ⟨5611595813111598167819027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3741063875407732111879351 5611595813111598167819027)
        ·
          refine ⟨8417393719667397251728541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5611595813111598167819027 8417393719667397251728541)
          ·
            refine ⟨3156522644875273969398203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8417393719667397251728541 3156522644875273969398203)
            ·
              refine ⟨4734783967312910954097305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3156522644875273969398203 4734783967312910954097305)
              ·
                refine ⟨3551087975484683215572979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4734783967312910954097305 3551087975484683215572979)
                ·
                  refine ⟨5326631963227024823359469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3551087975484683215572979 5326631963227024823359469)
                  ·
                    refine ⟨1997486986210134308759801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5326631963227024823359469 1997486986210134308759801)
                    ·
                      refine ⟨1498115239657600731569851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1997486986210134308759801 1498115239657600731569851)
                      ·
                        rfl

theorem cell23_2917569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_2917569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917569 prefixEnd_2917569 := by exact prefixLift 2917569
  have htrace : WordTrace (prefixWord ++ tailWord_2917569) baseStart_2917569 baseEnd_2917569 := by
    simpa [prefixWord, tailWord_2917569, baseEnd_2917569] using wordTrace_append hprefix tailTrace_2917569
  have hstable : (prefixWord ++ tailWord_2917569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917569).length < 2 ^ (prefixWord ++ tailWord_2917569).sum := by decide
  have hdescent : baseEnd_2917569 < baseStart_2917569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917605 : List Nat := [1, 3, 1, 4, 3, 1, 1, 4, 5]
def baseStart_2917605 : Nat := 118140960795 + 2917605 * 2 ^ 59
def prefixEnd_2917605 : Nat := 4983230072969 + 3 ^ 40 * 2917605 * 2
def baseEnd_2917605 : Nat := 166459302773462510079965

theorem tailTrace_2917605 : CollatzResearch.WordTrace tailWord_2917605 prefixEnd_2917605 166459302773462510079965 := by
  unfold tailWord_2917605
  simp only [CollatzResearch.WordTrace]
  refine ⟨106413796595022847108434269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70942531063348564738956179 106413796595022847108434269)
  ·
    refine ⟨39905173723133567665662851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106413796595022847108434269 39905173723133567665662851)
    ·
      refine ⟨59857760584700351498494277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39905173723133567665662851 59857760584700351498494277)
      ·
        refine ⟨11223330109631315905967677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59857760584700351498494277 11223330109631315905967677)
        ·
          refine ⟨4208748791111743464737879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11223330109631315905967677 4208748791111743464737879)
          ·
            refine ⟨6313123186667615197106819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4208748791111743464737879 6313123186667615197106819)
            ·
              refine ⟨9469684780001422795660229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6313123186667615197106819 9469684780001422795660229)
              ·
                refine ⟨1775565896250266774186293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9469684780001422795660229 1775565896250266774186293)
                ·
                  refine ⟨166459302773462510079965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1775565896250266774186293 166459302773462510079965)
                  ·
                    rfl

theorem cell23_2917605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 5].length) (baseStart_2917605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917605 prefixEnd_2917605 := by exact prefixLift 2917605
  have htrace : WordTrace (prefixWord ++ tailWord_2917605) baseStart_2917605 baseEnd_2917605 := by
    simpa [prefixWord, tailWord_2917605, baseEnd_2917605] using wordTrace_append hprefix tailTrace_2917605
  have hstable : (prefixWord ++ tailWord_2917605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917605).length < 2 ^ (prefixWord ++ tailWord_2917605).sum := by decide
  have hdescent : baseEnd_2917605 < baseStart_2917605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917608 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 1, 7, 2]
def baseStart_2917608 : Nat := 118140960795 + 2917608 * 2 ^ 59
def prefixEnd_2917608 : Nat := 4983230072969 + 3 ^ 40 * 2917608 * 2
def baseEnd_2917608 : Nat := 1498135265403126078982171

theorem tailTrace_2917608 : CollatzResearch.WordTrace tailWord_2917608 prefixEnd_2917608 1498135265403126078982171 := by
  unfold tailWord_2917608
  simp only [CollatzResearch.WordTrace]
  refine ⟨53206953007005989310396739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70942604009341319080528985 53206953007005989310396739)
  ·
    refine ⟨79810429510508983965595109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53206953007005989310396739 79810429510508983965595109)
    ·
      refine ⟨14964455533220434493549083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79810429510508983965595109 14964455533220434493549083)
      ·
        refine ⟨22446683299830651740323625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14964455533220434493549083 22446683299830651740323625)
        ·
          refine ⟨16835012474872988805242719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22446683299830651740323625 16835012474872988805242719)
          ·
            refine ⟨25252518712309483207864079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16835012474872988805242719 25252518712309483207864079)
            ·
              refine ⟨37878778068464224811796119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25252518712309483207864079 37878778068464224811796119)
              ·
                refine ⟨56818167102696337217694179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37878778068464224811796119 56818167102696337217694179)
                ·
                  refine ⟨85227250654044505826541269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56818167102696337217694179 85227250654044505826541269)
                  ·
                    refine ⟨1997513687204168105309561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 85227250654044505826541269 1997513687204168105309561)
                    ·
                      refine ⟨1498135265403126078982171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1997513687204168105309561 1498135265403126078982171)
                      ·
                        rfl

theorem cell23_2917608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_2917608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917608 prefixEnd_2917608 := by exact prefixLift 2917608
  have htrace : WordTrace (prefixWord ++ tailWord_2917608) baseStart_2917608 baseEnd_2917608 := by
    simpa [prefixWord, tailWord_2917608, baseEnd_2917608] using wordTrace_append hprefix tailTrace_2917608
  have hstable : (prefixWord ++ tailWord_2917608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917608).length < 2 ^ (prefixWord ++ tailWord_2917608).sum := by decide
  have hdescent : baseEnd_2917608 < baseStart_2917608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917611 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 5]
def baseStart_2917611 : Nat := 118140960795 + 2917611 * 2 ^ 59
def prefixEnd_2917611 : Nat := 4983230072969 + 3 ^ 40 * 2917611 * 2
def baseEnd_2917611 : Nat := 1498136805845089567244657

theorem tailTrace_2917611 : CollatzResearch.WordTrace tailWord_2917611 prefixEnd_2917611 1498136805845089567244657 := by
  unfold tailWord_2917611
  simp only [CollatzResearch.WordTrace]
  refine ⟨106414015433001110133152687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70942676955334073422101791 106414015433001110133152687)
  ·
    refine ⟨159621023149501665199729031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106414015433001110133152687 159621023149501665199729031)
    ·
      refine ⟨239431534724252497799593547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159621023149501665199729031 239431534724252497799593547)
      ·
        refine ⟨359147302086378746699390321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239431534724252497799593547 359147302086378746699390321)
        ·
          refine ⟨269360476564784060024542741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359147302086378746699390321 269360476564784060024542741)
          ·
            refine ⟨12626272338974252813650441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 269360476564784060024542741 12626272338974252813650441)
            ·
              refine ⟨9469704254230689610237831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12626272338974252813650441 9469704254230689610237831)
              ·
                refine ⟨14204556381346034415356747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9469704254230689610237831 14204556381346034415356747)
                ·
                  refine ⟨21306834572019051623035121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14204556381346034415356747 21306834572019051623035121)
                  ·
                    refine ⟨15980125929014288717276341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21306834572019051623035121 15980125929014288717276341)
                    ·
                      refine ⟨1498136805845089567244657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15980125929014288717276341 1498136805845089567244657)
                      ·
                        rfl

theorem cell23_2917611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 5].length) (baseStart_2917611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917611 prefixEnd_2917611 := by exact prefixLift 2917611
  have htrace : WordTrace (prefixWord ++ tailWord_2917611) baseStart_2917611 baseEnd_2917611 := by
    simpa [prefixWord, tailWord_2917611, baseEnd_2917611] using wordTrace_append hprefix tailTrace_2917611
  have hstable : (prefixWord ++ tailWord_2917611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917611).length < 2 ^ (prefixWord ++ tailWord_2917611).sum := by decide
  have hdescent : baseEnd_2917611 < baseStart_2917611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917691 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 9, 5]
def baseStart_2917691 : Nat := 118140960795 + 2917691 * 2 ^ 59
def prefixEnd_2917691 : Nat := 4983230072969 + 3 ^ 40 * 2917691 * 2
def baseEnd_2917691 : Nat := 499392628099149751414763

theorem tailTrace_2917691 : CollatzResearch.WordTrace tailWord_2917691 prefixEnd_2917691 499392628099149751414763 := by
  unfold tailWord_2917691
  simp only [CollatzResearch.WordTrace]
  refine ⟨106416933272711283796064927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70944622181807522530709951 106416933272711283796064927)
  ·
    refine ⟨159625399909066925694097391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106416933272711283796064927 159625399909066925694097391)
    ·
      refine ⟨239438099863600388541146087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159625399909066925694097391 239438099863600388541146087)
      ·
        refine ⟨359157149795400582811719131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239438099863600388541146087 359157149795400582811719131)
        ·
          refine ⟨538735724693100874217578697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359157149795400582811719131 538735724693100874217578697)
          ·
            refine ⟨404051793519825655663184023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538735724693100874217578697 404051793519825655663184023)
            ·
              refine ⟨606077690279738483494776035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404051793519825655663184023 606077690279738483494776035)
              ·
                refine ⟨909116535419607725242164053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606077690279738483494776035 909116535419607725242164053)
                ·
                  refine ⟨5326854699724264015090805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 909116535419607725242164053 5326854699724264015090805)
                  ·
                    refine ⟨499392628099149751414763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5326854699724264015090805 499392628099149751414763)
                    ·
                      rfl

theorem cell23_2917691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 5].length) (baseStart_2917691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917691 prefixEnd_2917691 := by exact prefixLift 2917691
  have htrace : WordTrace (prefixWord ++ tailWord_2917691) baseStart_2917691 baseEnd_2917691 := by
    simpa [prefixWord, tailWord_2917691, baseEnd_2917691] using wordTrace_append hprefix tailTrace_2917691
  have hstable : (prefixWord ++ tailWord_2917691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917691).length < 2 ^ (prefixWord ++ tailWord_2917691).sum := by decide
  have hdescent : baseEnd_2917691 < baseStart_2917691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917709 : List Nat := [1, 6, 1, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_2917709 : Nat := 118140960795 + 2917709 * 2 ^ 59
def prefixEnd_2917709 : Nat := 4983230072969 + 3 ^ 40 * 2917709 * 2
def baseEnd_2917709 : Nat := 1498187126949230183819207

theorem tailTrace_2917709 : CollatzResearch.WordTrace tailWord_2917709 prefixEnd_2917709 1498187126949230183819207 := by
  unfold tailWord_2917709
  simp only [CollatzResearch.WordTrace]
  refine ⟨106417589786646072870220181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70945059857764048580146787 106417589786646072870220181)
  ·
    refine ⟨4988324521249034665791571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106417589786646072870220181 4988324521249034665791571)
    ·
      refine ⟨7482486781873551998687357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4988324521249034665791571 7482486781873551998687357)
      ·
        refine ⟨2805932543202581999507759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7482486781873551998687357 2805932543202581999507759)
        ·
          refine ⟨4208898814803872999261639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2805932543202581999507759 4208898814803872999261639)
          ·
            refine ⟨6313348222205809498892459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4208898814803872999261639 6313348222205809498892459)
            ·
              refine ⟨9470022333308714248338689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6313348222205809498892459 9470022333308714248338689)
              ·
                refine ⟨7102516749981535686254017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9470022333308714248338689 7102516749981535686254017)
                ·
                  refine ⟨5326887562486151764690513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7102516749981535686254017 5326887562486151764690513)
                  ·
                    refine ⟨3995165671864613823517885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5326887562486151764690513 3995165671864613823517885)
                    ·
                      refine ⟨1498187126949230183819207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3995165671864613823517885 1498187126949230183819207)
                      ·
                        rfl

theorem cell23_2917709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_2917709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917709 prefixEnd_2917709 := by exact prefixLift 2917709
  have htrace : WordTrace (prefixWord ++ tailWord_2917709) baseStart_2917709 baseEnd_2917709 := by
    simpa [prefixWord, tailWord_2917709, baseEnd_2917709] using wordTrace_append hprefix tailTrace_2917709
  have hstable : (prefixWord ++ tailWord_2917709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917709).length < 2 ^ (prefixWord ++ tailWord_2917709).sum := by decide
  have hdescent : baseEnd_2917709 < baseStart_2917709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917711 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 4]
def baseStart_2917711 : Nat := 118140960795 + 2917711 * 2 ^ 59
def prefixEnd_2917711 : Nat := 4983230072969 + 3 ^ 40 * 2917711 * 2
def baseEnd_2917711 : Nat := 1498188153910539175994197

theorem tailTrace_2917711 : CollatzResearch.WordTrace tailWord_2917711 prefixEnd_2917711 1498188153910539175994197 := by
  unfold tailWord_2917711
  simp only [CollatzResearch.WordTrace]
  refine ⟨106417662732638827211792987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70945108488425884807861991 106417662732638827211792987)
  ·
    refine ⟨159626494098958240817689481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106417662732638827211792987 159626494098958240817689481)
    ·
      refine ⟨119719870574218680613267111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159626494098958240817689481 119719870574218680613267111)
      ·
        refine ⟨179579805861328020919900667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119719870574218680613267111 179579805861328020919900667)
        ·
          refine ⟨269369708791992031379851001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179579805861328020919900667 269369708791992031379851001)
          ·
            refine ⟨202027281593994023534888251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269369708791992031379851001 202027281593994023534888251)
            ·
              refine ⟨303040922390991035302332377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202027281593994023534888251 303040922390991035302332377)
              ·
                refine ⟨227280691793243276476749283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303040922390991035302332377 227280691793243276476749283)
                ·
                  refine ⟨340921037689864914715123925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227280691793243276476749283 340921037689864914715123925)
                  ·
                    refine ⟨7990336820856208938635717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 340921037689864914715123925 7990336820856208938635717)
                    ·
                      refine ⟨1498188153910539175994197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7990336820856208938635717 1498188153910539175994197)
                      ·
                        rfl

theorem cell23_2917711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_2917711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917711 prefixEnd_2917711 := by exact prefixLift 2917711
  have htrace : WordTrace (prefixWord ++ tailWord_2917711) baseStart_2917711 baseEnd_2917711 := by
    simpa [prefixWord, tailWord_2917711, baseEnd_2917711] using wordTrace_append hprefix tailTrace_2917711
  have hstable : (prefixWord ++ tailWord_2917711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917711).length < 2 ^ (prefixWord ++ tailWord_2917711).sum := by decide
  have hdescent : baseEnd_2917711 < baseStart_2917711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917715 : List Nat := [1, 1, 1, 2, 1, 1, 7, 2, 2, 3, 2]
def baseStart_2917715 : Nat := 118140960795 + 2917715 * 2 ^ 59
def prefixEnd_2917715 : Nat := 4983230072969 + 3 ^ 40 * 2917715 * 2
def baseEnd_2917715 : Nat := 1498190207833157160344179

theorem tailTrace_2917715 : CollatzResearch.WordTrace tailWord_2917715 prefixEnd_2917715 1498190207833157160344179 := by
  unfold tailWord_2917715
  simp only [CollatzResearch.WordTrace]
  refine ⟨106417808624624335894938599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70945205749749557263292399 106417808624624335894938599)
  ·
    refine ⟨159626712936936503842407899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106417808624624335894938599 159626712936936503842407899)
    ·
      refine ⟨239440069405404755763611849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159626712936936503842407899 239440069405404755763611849)
      ·
        refine ⟨179580052054053566822708887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239440069405404755763611849 179580052054053566822708887)
        ·
          refine ⟨269370078081080350234063331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179580052054053566822708887 269370078081080350234063331)
          ·
            refine ⟨404055117121620525351094997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269370078081080350234063331 404055117121620525351094997)
            ·
              refine ⟨9470041807537981062916289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 404055117121620525351094997 9470041807537981062916289)
              ·
                refine ⟨7102531355653485797187217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9470041807537981062916289 7102531355653485797187217)
                ·
                  refine ⟨5326898516740114347890413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7102531355653485797187217 5326898516740114347890413)
                  ·
                    refine ⟨1997586943777542880458905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5326898516740114347890413 1997586943777542880458905)
                    ·
                      refine ⟨1498190207833157160344179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1997586943777542880458905 1498190207833157160344179)
                      ·
                        rfl

theorem cell23_2917715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 3, 2].length) (baseStart_2917715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917715 prefixEnd_2917715 := by exact prefixLift 2917715
  have htrace : WordTrace (prefixWord ++ tailWord_2917715) baseStart_2917715 baseEnd_2917715 := by
    simpa [prefixWord, tailWord_2917715, baseEnd_2917715] using wordTrace_append hprefix tailTrace_2917715
  have hstable : (prefixWord ++ tailWord_2917715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917715).length < 2 ^ (prefixWord ++ tailWord_2917715).sum := by decide
  have hdescent : baseEnd_2917715 < baseStart_2917715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917722 : List Nat := [3, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3]
def baseStart_2917722 : Nat := 118140960795 + 2917722 * 2 ^ 59
def prefixEnd_2917722 : Nat := 4983230072969 + 3 ^ 40 * 2917722 * 2
def baseEnd_2917722 : Nat := 1498193802197738632956647

theorem tailTrace_2917722 : CollatzResearch.WordTrace tailWord_2917722 prefixEnd_2917722 1498193802197738632956647 := by
  unfold tailWord_2917722
  simp only [CollatzResearch.WordTrace]
  refine ⟨26604515983899744022610855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70945375957065984060295613 26604515983899744022610855)
  ·
    refine ⟨39906773975849616033916283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26604515983899744022610855 39906773975849616033916283)
    ·
      refine ⟨59860160963774424050874425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39906773975849616033916283 59860160963774424050874425)
      ·
        refine ⟨44895120722830818038155819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59860160963774424050874425 44895120722830818038155819)
        ·
          refine ⟨67342681084246227057233729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44895120722830818038155819 67342681084246227057233729)
          ·
            refine ⟨50507010813184670292925297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67342681084246227057233729 50507010813184670292925297)
            ·
              refine ⟨37880258109888502719693973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50507010813184670292925297 37880258109888502719693973)
              ·
                refine ⟨1775637098901023564985655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37880258109888502719693973 1775637098901023564985655)
                ·
                  refine ⟨2663455648351535347478483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1775637098901023564985655 2663455648351535347478483)
                  ·
                    refine ⟨3995183472527303021217725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2663455648351535347478483 3995183472527303021217725)
                    ·
                      refine ⟨1498193802197738632956647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3995183472527303021217725 1498193802197738632956647)
                      ·
                        rfl

theorem cell23_2917722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_2917722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917722 prefixEnd_2917722 := by exact prefixLift 2917722
  have htrace : WordTrace (prefixWord ++ tailWord_2917722) baseStart_2917722 baseEnd_2917722 := by
    simpa [prefixWord, tailWord_2917722, baseEnd_2917722] using wordTrace_append hprefix tailTrace_2917722
  have hstable : (prefixWord ++ tailWord_2917722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917722).length < 2 ^ (prefixWord ++ tailWord_2917722).sum := by decide
  have hdescent : baseEnd_2917722 < baseStart_2917722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917742 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 3, 5]
def baseStart_2917742 : Nat := 118140960795 + 2917742 * 2 ^ 59
def prefixEnd_2917742 : Nat := 4983230072969 + 3 ^ 40 * 2917742 * 2
def baseEnd_2917742 : Nat := 499401357270276184902185

theorem tailTrace_2917742 : CollatzResearch.WordTrace tailWord_2917742 prefixEnd_2917742 499401357270276184902185 := by
  unfold tailWord_2917742
  simp only [CollatzResearch.WordTrace]
  refine ⟨13302349174440814938271435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70945862263684346337447653 13302349174440814938271435)
  ·
    refine ⟨19953523761661222407407153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13302349174440814938271435 19953523761661222407407153)
    ·
      refine ⟨14965142821245916805555365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19953523761661222407407153 14965142821245916805555365)
      ·
        refine ⟨2805964278983609401041631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14965142821245916805555365 2805964278983609401041631)
        ·
          refine ⟨4208946418475414101562447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2805964278983609401041631 4208946418475414101562447)
          ·
            refine ⟨6313419627713121152343671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4208946418475414101562447 6313419627713121152343671)
            ·
              refine ⟨9470129441569681728515507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6313419627713121152343671 9470129441569681728515507)
              ·
                refine ⟨14205194162354522592773261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9470129441569681728515507 14205194162354522592773261)
                ·
                  refine ⟨5326947810882945972289973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14205194162354522592773261 5326947810882945972289973)
                  ·
                    refine ⟨499401357270276184902185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5326947810882945972289973 499401357270276184902185)
                    ·
                      rfl

theorem cell23_2917742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_2917742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917742 prefixEnd_2917742 := by exact prefixLift 2917742
  have htrace : WordTrace (prefixWord ++ tailWord_2917742) baseStart_2917742 baseEnd_2917742 := by
    simpa [prefixWord, tailWord_2917742, baseEnd_2917742] using wordTrace_append hprefix tailTrace_2917742
  have hstable : (prefixWord ++ tailWord_2917742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917742).length < 2 ^ (prefixWord ++ tailWord_2917742).sum := by decide
  have hdescent : baseEnd_2917742 < baseStart_2917742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917745 : List Nat := [1, 2, 2, 2, 1, 2, 5, 2, 1, 1, 4]
def baseStart_2917745 : Nat := 118140960795 + 2917745 * 2 ^ 59
def prefixEnd_2917745 : Nat := 4983230072969 + 3 ^ 40 * 2917745 * 2
def baseEnd_2917745 : Nat := 1498205612252792042969041

theorem tailTrace_2917745 : CollatzResearch.WordTrace tailWord_2917745 prefixEnd_2917745 1498205612252792042969041 := by
  unfold tailWord_2917745
  simp only [CollatzResearch.WordTrace]
  refine ⟨106418902814515651018530689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70945935209677100679020459 106418902814515651018530689)
  ·
    refine ⟨79814177110886738263898017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106418902814515651018530689 79814177110886738263898017)
    ·
      refine ⟨59860632833165053697923513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79814177110886738263898017 59860632833165053697923513)
      ·
        refine ⟨44895474624873790273442635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59860632833165053697923513 44895474624873790273442635)
        ·
          refine ⟨67343211937310685410163953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44895474624873790273442635 67343211937310685410163953)
          ·
            refine ⟨50507408952983014057622965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67343211937310685410163953 50507408952983014057622965)
            ·
              refine ⟨4735069589342157567902153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50507408952983014057622965 4735069589342157567902153)
              ·
                refine ⟨3551302192006618175926615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4735069589342157567902153 3551302192006618175926615)
                ·
                  refine ⟨5326953288009927263889923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3551302192006618175926615 5326953288009927263889923)
                  ·
                    refine ⟨7990429932014890895834885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5326953288009927263889923 7990429932014890895834885)
                    ·
                      refine ⟨1498205612252792042969041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7990429932014890895834885 1498205612252792042969041)
                      ·
                        rfl

theorem cell23_2917745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_2917745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917745 prefixEnd_2917745 := by exact prefixLift 2917745
  have htrace : WordTrace (prefixWord ++ tailWord_2917745) baseStart_2917745 baseEnd_2917745 := by
    simpa [prefixWord, tailWord_2917745, baseEnd_2917745] using wordTrace_append hprefix tailTrace_2917745
  have hstable : (prefixWord ++ tailWord_2917745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917745).length < 2 ^ (prefixWord ++ tailWord_2917745).sum := by decide
  have hdescent : baseEnd_2917745 < baseStart_2917745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917749 : List Nat := [1, 3, 4, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_2917749 : Nat := 118140960795 + 2917749 * 2 ^ 59
def prefixEnd_2917749 : Nat := 4983230072969 + 3 ^ 40 * 2917749 * 2
def baseEnd_2917749 : Nat := 1498207666175410027319023

theorem tailTrace_2917749 : CollatzResearch.WordTrace tailWord_2917749 prefixEnd_2917749 1498207666175410027319023 := by
  unfold tailWord_2917749
  simp only [CollatzResearch.WordTrace]
  refine ⟨106419048706501159701676301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70946032471000773134450867 106419048706501159701676301)
  ·
    refine ⟨39907143264937934888128613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106419048706501159701676301 39907143264937934888128613)
    ·
      refine ⟨7482589362175862791524115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39907143264937934888128613 7482589362175862791524115)
      ·
        refine ⟨11223884043263794187286173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7482589362175862791524115 11223884043263794187286173)
        ·
          refine ⟨4208956516223922820232315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11223884043263794187286173 4208956516223922820232315)
          ·
            refine ⟨6313434774335884230348473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4208956516223922820232315 6313434774335884230348473)
            ·
              refine ⟨4735076080751913172761355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6313434774335884230348473 4735076080751913172761355)
              ·
                refine ⟨7102614121127869759142033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4735076080751913172761355 7102614121127869759142033)
                ·
                  refine ⟨5326960590845902319356525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7102614121127869759142033 5326960590845902319356525)
                  ·
                    refine ⟨1997610221567213369758697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5326960590845902319356525 1997610221567213369758697)
                    ·
                      refine ⟨1498207666175410027319023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1997610221567213369758697 1498207666175410027319023)
                      ·
                        rfl

theorem cell23_2917749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_2917749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917749 prefixEnd_2917749 := by exact prefixLift 2917749
  have htrace : WordTrace (prefixWord ++ tailWord_2917749) baseStart_2917749 baseEnd_2917749 := by
    simpa [prefixWord, tailWord_2917749, baseEnd_2917749] using wordTrace_append hprefix tailTrace_2917749
  have hstable : (prefixWord ++ tailWord_2917749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917749).length < 2 ^ (prefixWord ++ tailWord_2917749).sum := by decide
  have hdescent : baseEnd_2917749 < baseStart_2917749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917751 : List Nat := [1, 1, 3, 1, 1, 2, 3, 11]
def baseStart_2917751 : Nat := 118140960795 + 2917751 * 2 ^ 59
def prefixEnd_2917751 : Nat := 4983230072969 + 3 ^ 40 * 2917751 * 2
def baseEnd_2917751 : Nat := 55489210856915519240519

theorem tailTrace_2917751 : CollatzResearch.WordTrace tailWord_2917751 prefixEnd_2917751 55489210856915519240519 := by
  unfold tailWord_2917751
  simp only [CollatzResearch.WordTrace]
  refine ⟨106419121652493914043249107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70946081101662609362166071 106419121652493914043249107)
  ·
    refine ⟨159628682478740871064873661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106419121652493914043249107 159628682478740871064873661)
    ·
      refine ⟨59860755929527826649327623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159628682478740871064873661 59860755929527826649327623)
      ·
        refine ⟨89791133894291739973991435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59860755929527826649327623 89791133894291739973991435)
        ·
          refine ⟨134686700841437609960987153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89791133894291739973991435 134686700841437609960987153)
          ·
            refine ⟨101015025631078207470740365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134686700841437609960987153 101015025631078207470740365)
            ·
              refine ⟨37880634611654327801527637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101015025631078207470740365 37880634611654327801527637)
              ·
                refine ⟨55489210856915519240519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 37880634611654327801527637 55489210856915519240519)
                ·
                  rfl

theorem cell23_2917751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 11].length) (baseStart_2917751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917751 prefixEnd_2917751 := by exact prefixLift 2917751
  have htrace : WordTrace (prefixWord ++ tailWord_2917751) baseStart_2917751 baseEnd_2917751 := by
    simpa [prefixWord, tailWord_2917751, baseEnd_2917751] using wordTrace_append hprefix tailTrace_2917751
  have hstable : (prefixWord ++ tailWord_2917751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917751).length < 2 ^ (prefixWord ++ tailWord_2917751).sum := by decide
  have hdescent : baseEnd_2917751 < baseStart_2917751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917765 : List Nat := [1, 3, 1, 1, 3, 1, 2, 5, 1, 2, 3]
def baseStart_2917765 : Nat := 118140960795 + 2917765 * 2 ^ 59
def prefixEnd_2917765 : Nat := 4983230072969 + 3 ^ 40 * 2917765 * 2
def baseEnd_2917765 : Nat := 1498215881865881964718949

theorem tailTrace_2917765 : CollatzResearch.WordTrace tailWord_2917765 prefixEnd_2917765 1498215881865881964718949 := by
  unfold tailWord_2917765
  simp only [CollatzResearch.WordTrace]
  refine ⟨106419632274443194434258749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70946421516295462956172499 106419632274443194434258749)
  ·
    refine ⟨39907362102916197912847031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106419632274443194434258749 39907362102916197912847031)
    ·
      refine ⟨59861043154374296869270547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39907362102916197912847031 59861043154374296869270547)
      ·
        refine ⟨89791564731561445303905821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59861043154374296869270547 89791564731561445303905821)
        ·
          refine ⟨33671836774335541988964683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89791564731561445303905821 33671836774335541988964683)
          ·
            refine ⟨50507755161503312983447025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33671836774335541988964683 50507755161503312983447025)
            ·
              refine ⟨37880816371127484737585269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50507755161503312983447025 37880816371127484737585269)
              ·
                refine ⟨3551326534793201694148619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37880816371127484737585269 3551326534793201694148619)
                ·
                  refine ⟨5326989802189802541222929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3551326534793201694148619 5326989802189802541222929)
                  ·
                    refine ⟨3995242351642351905917197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5326989802189802541222929 3995242351642351905917197)
                    ·
                      refine ⟨1498215881865881964718949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3995242351642351905917197 1498215881865881964718949)
                      ·
                        rfl

theorem cell23_2917765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 2, 3].length) (baseStart_2917765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917765 prefixEnd_2917765 := by exact prefixLift 2917765
  have htrace : WordTrace (prefixWord ++ tailWord_2917765) baseStart_2917765 baseEnd_2917765 := by
    simpa [prefixWord, tailWord_2917765, baseEnd_2917765] using wordTrace_append hprefix tailTrace_2917765
  have hstable : (prefixWord ++ tailWord_2917765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917765).length < 2 ^ (prefixWord ++ tailWord_2917765).sum := by decide
  have hdescent : baseEnd_2917765 < baseStart_2917765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917795 : List Nat := [1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 3]
def baseStart_2917795 : Nat := 118140960795 + 2917795 * 2 ^ 59
def prefixEnd_2917795 : Nat := 4983230072969 + 3 ^ 40 * 2917795 * 2
def baseEnd_2917795 : Nat := 1498231286285516847343811

theorem tailTrace_2917795 : CollatzResearch.WordTrace tailWord_2917795 prefixEnd_2917795 1498231286285516847343811 := by
  unfold tailWord_2917795
  simp only [CollatzResearch.WordTrace]
  refine ⟨106420726464334509557850839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70947150976223006371900559 106420726464334509557850839)
  ·
    refine ⟨159631089696501764336776259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106420726464334509557850839 159631089696501764336776259)
    ·
      refine ⟨239446634544752646505164389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159631089696501764336776259 239446634544752646505164389)
      ·
        refine ⟨44896243977141121219718323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239446634544752646505164389 44896243977141121219718323)
        ·
          refine ⟨67344365965711681829577485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44896243977141121219718323 67344365965711681829577485)
          ·
            refine ⟨25254137237141880686091557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67344365965711681829577485 25254137237141880686091557)
            ·
              refine ⟨4735150731964102628642167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25254137237141880686091557 4735150731964102628642167)
              ·
                refine ⟨7102726097946153942963251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4735150731964102628642167 7102726097946153942963251)
                ·
                  refine ⟨10654089146919230914444877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7102726097946153942963251 10654089146919230914444877)
                  ·
                    refine ⟨3995283430094711592916829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10654089146919230914444877 3995283430094711592916829)
                    ·
                      refine ⟨1498231286285516847343811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3995283430094711592916829 1498231286285516847343811)
                      ·
                        rfl

theorem cell23_2917795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_2917795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917795 prefixEnd_2917795 := by exact prefixLift 2917795
  have htrace : WordTrace (prefixWord ++ tailWord_2917795) baseStart_2917795 baseEnd_2917795 := by
    simpa [prefixWord, tailWord_2917795, baseEnd_2917795] using wordTrace_append hprefix tailTrace_2917795
  have hstable : (prefixWord ++ tailWord_2917795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917795).length < 2 ^ (prefixWord ++ tailWord_2917795).sum := by decide
  have hdescent : baseEnd_2917795 < baseStart_2917795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917835 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 3, 4, 2]
def baseStart_2917835 : Nat := 118140960795 + 2917835 * 2 ^ 59
def prefixEnd_2917835 : Nat := 4983230072969 + 3 ^ 40 * 2917835 * 2
def baseEnd_2917835 : Nat := 1498251825511696690843627

theorem tailTrace_2917835 : CollatzResearch.WordTrace tailWord_2917835 prefixEnd_2917835 1498251825511696690843627 := by
  unfold tailWord_2917835
  simp only [CollatzResearch.WordTrace]
  refine ⟨106422185384189596389306959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70948123589459730926204639 106422185384189596389306959)
  ·
    refine ⟨159633278076284394583960439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106422185384189596389306959 159633278076284394583960439)
    ·
      refine ⟨239449917114426591875940659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159633278076284394583960439 239449917114426591875940659)
      ·
        refine ⟨359174875671639887813910989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239449917114426591875940659 359174875671639887813910989)
        ·
          refine ⟨134690578376864957930216621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359174875671639887813910989 134690578376864957930216621)
          ·
            refine ⟨50508966891324359223831233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134690578376864957930216621 50508966891324359223831233)
            ·
              refine ⟨37881725168493269417873425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50508966891324359223831233 37881725168493269417873425)
              ·
                refine ⟨28411293876369952063405069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37881725168493269417873425 28411293876369952063405069)
                ·
                  refine ⟨10654235203638732023776901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28411293876369952063405069 10654235203638732023776901)
                  ·
                    refine ⟨1997669100682262254458169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10654235203638732023776901 1997669100682262254458169)
                    ·
                      refine ⟨1498251825511696690843627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1997669100682262254458169 1498251825511696690843627)
                      ·
                        rfl

theorem cell23_2917835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 4, 2].length) (baseStart_2917835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917835 prefixEnd_2917835 := by exact prefixLift 2917835
  have htrace : WordTrace (prefixWord ++ tailWord_2917835) baseStart_2917835 baseEnd_2917835 := by
    simpa [prefixWord, tailWord_2917835, baseEnd_2917835] using wordTrace_append hprefix tailTrace_2917835
  have hstable : (prefixWord ++ tailWord_2917835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917835).length < 2 ^ (prefixWord ++ tailWord_2917835).sum := by decide
  have hdescent : baseEnd_2917835 < baseStart_2917835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917875 : List Nat := [1, 1, 1, 2, 2, 2, 2, 7, 5]
def baseStart_2917875 : Nat := 118140960795 + 2917875 * 2 ^ 59
def prefixEnd_2917875 : Nat := 4983230072969 + 3 ^ 40 * 2917875 * 2
def baseEnd_2917875 : Nat := 166474707193097392704827

theorem tailTrace_2917875 : CollatzResearch.WordTrace tailWord_2917875 prefixEnd_2917875 166474707193097392704827 := by
  unfold tailWord_2917875
  simp only [CollatzResearch.WordTrace]
  refine ⟨106423644304044683220763079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70949096202696455480508719 106423644304044683220763079)
  ·
    refine ⟨159635466456067024831144619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106423644304044683220763079 159635466456067024831144619)
    ·
      refine ⟨239453199684100537246716929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159635466456067024831144619 239453199684100537246716929)
      ·
        refine ⟨179589899763075402935037697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239453199684100537246716929 179589899763075402935037697)
        ·
          refine ⟨134692424822306552201278273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179589899763075402935037697 134692424822306552201278273)
          ·
            refine ⟨101019318616729914150958705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134692424822306552201278273 101019318616729914150958705)
            ·
              refine ⟨75764488962547435613219029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101019318616729914150958705 75764488962547435613219029)
              ·
                refine ⟨1775730210059705522184821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 75764488962547435613219029 1775730210059705522184821)
                ·
                  refine ⟨166474707193097392704827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1775730210059705522184821 166474707193097392704827)
                  ·
                    rfl

theorem cell23_2917875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 5].length) (baseStart_2917875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917875 prefixEnd_2917875 := by exact prefixLift 2917875
  have htrace : WordTrace (prefixWord ++ tailWord_2917875) baseStart_2917875 baseEnd_2917875 := by
    simpa [prefixWord, tailWord_2917875, baseEnd_2917875] using wordTrace_append hprefix tailTrace_2917875
  have hstable : (prefixWord ++ tailWord_2917875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917875).length < 2 ^ (prefixWord ++ tailWord_2917875).sum := by decide
  have hdescent : baseEnd_2917875 < baseStart_2917875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917959 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 2, 4, 2]
def baseStart_2917959 : Nat := 118140960795 + 2917959 * 2 ^ 59
def prefixEnd_2917959 : Nat := 4983230072969 + 3 ^ 40 * 2917959 * 2
def baseEnd_2917959 : Nat := 1498315497112854205693057

theorem tailTrace_2917959 : CollatzResearch.WordTrace tailWord_2917959 prefixEnd_2917959 1498315497112854205693057 := by
  unfold tailWord_2917959
  simp only [CollatzResearch.WordTrace]
  refine ⟨106426708035740365566820931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70951138690493577044547287 106426708035740365566820931)
  ·
    refine ⟨159640062053610548350231397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106426708035740365566820931 159640062053610548350231397)
    ·
      refine ⟨29932511635051977815668387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159640062053610548350231397 29932511635051977815668387)
      ·
        refine ⟨44898767452577966723502581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29932511635051977815668387 44898767452577966723502581)
        ·
          refine ⟨4209259448679184380328367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44898767452577966723502581 4209259448679184380328367)
          ·
            refine ⟨6313889173018776570492551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4209259448679184380328367 6313889173018776570492551)
            ·
              refine ⟨9470833759528164855738827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6313889173018776570492551 9470833759528164855738827)
              ·
                refine ⟨14206250639292247283608241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9470833759528164855738827 14206250639292247283608241)
                ·
                  refine ⟨10654687979469185462706181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14206250639292247283608241 10654687979469185462706181)
                  ·
                    refine ⟨1997753996150472274257409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10654687979469185462706181 1997753996150472274257409)
                    ·
                      refine ⟨1498315497112854205693057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1997753996150472274257409 1498315497112854205693057)
                      ·
                        rfl

theorem cell23_2917959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_2917959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2917959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2917959 prefixEnd_2917959 := by exact prefixLift 2917959
  have htrace : WordTrace (prefixWord ++ tailWord_2917959) baseStart_2917959 baseEnd_2917959 := by
    simpa [prefixWord, tailWord_2917959, baseEnd_2917959] using wordTrace_append hprefix tailTrace_2917959
  have hstable : (prefixWord ++ tailWord_2917959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917959).length < 2 ^ (prefixWord ++ tailWord_2917959).sum := by decide
  have hdescent : baseEnd_2917959 < baseStart_2917959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918009 : List Nat := [1, 2, 1, 3, 3, 1, 4, 1, 3, 1, 3]
def baseStart_2918009 : Nat := 118140960795 + 2918009 * 2 ^ 59
def prefixEnd_2918009 : Nat := 4983230072969 + 3 ^ 40 * 2918009 * 2
def baseEnd_2918009 : Nat := 1498341171145579010067827

theorem tailTrace_2918009 : CollatzResearch.WordTrace tailWord_2918009 prefixEnd_2918009 1498341171145579010067827 := by
  unfold tailWord_2918009
  simp only [CollatzResearch.WordTrace]
  refine ⟨106428531685559224106141081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70952354457039482737427387 106428531685559224106141081)
  ·
    refine ⟨79821398764169418079605811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106428531685559224106141081 79821398764169418079605811)
    ·
      refine ⟨119732098146254127119408717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79821398764169418079605811 119732098146254127119408717)
      ·
        refine ⟨44899536804845297669778269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119732098146254127119408717 44899536804845297669778269)
        ·
          refine ⟨16837326301816986626166851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44899536804845297669778269 16837326301816986626166851)
          ·
            refine ⟨25255989452725479939250277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16837326301816986626166851 25255989452725479939250277)
            ·
              refine ⟨4735498022386027488609427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25255989452725479939250277 4735498022386027488609427)
              ·
                refine ⟨7103247033579041232914141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4735498022386027488609427 7103247033579041232914141)
                ·
                  refine ⟨2663717637592140462342803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7103247033579041232914141 2663717637592140462342803)
                  ·
                    refine ⟨3995576456388210693514205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2663717637592140462342803 3995576456388210693514205)
                    ·
                      refine ⟨1498341171145579010067827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3995576456388210693514205 1498341171145579010067827)
                      ·
                        rfl

theorem cell23_2918009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_2918009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918009 prefixEnd_2918009 := by exact prefixLift 2918009
  have htrace : WordTrace (prefixWord ++ tailWord_2918009) baseStart_2918009 baseEnd_2918009 := by
    simpa [prefixWord, tailWord_2918009, baseEnd_2918009] using wordTrace_append hprefix tailTrace_2918009
  have hstable : (prefixWord ++ tailWord_2918009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918009).length < 2 ^ (prefixWord ++ tailWord_2918009).sum := by decide
  have hdescent : baseEnd_2918009 < baseStart_2918009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918049 : List Nat := [1, 2, 3, 3, 2, 1, 2, 3, 1, 1, 4]
def baseStart_2918049 : Nat := 118140960795 + 2918049 * 2 ^ 59
def prefixEnd_2918049 : Nat := 4983230072969 + 3 ^ 40 * 2918049 * 2
def baseEnd_2918049 : Nat := 1498361710371758853567643

theorem tailTrace_2918049 : CollatzResearch.WordTrace tailWord_2918049 prefixEnd_2918049 1498361710371758853567643 := by
  unfold tailWord_2918049
  simp only [CollatzResearch.WordTrace]
  refine ⟨106429990605414310937597201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70953327070276207291731467 106429990605414310937597201)
  ·
    refine ⟨79822492954060733203197901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106429990605414310937597201 79822492954060733203197901)
    ·
      refine ⟨29933434857772774951199213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79822492954060733203197901 29933434857772774951199213)
      ·
        refine ⟨11225038071664790606699705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29933434857772774951199213 11225038071664790606699705)
        ·
          refine ⟨8418778553748592955024779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11225038071664790606699705 8418778553748592955024779)
          ·
            refine ⟨12628167830622889432537169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8418778553748592955024779 12628167830622889432537169)
            ·
              refine ⟨9471125872967167074402877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12628167830622889432537169 9471125872967167074402877)
              ·
                refine ⟨3551672202362687652901079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9471125872967167074402877 3551672202362687652901079)
                ·
                  refine ⟨5327508303544031479351619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3551672202362687652901079 5327508303544031479351619)
                  ·
                    refine ⟨7991262455316047219027429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5327508303544031479351619 7991262455316047219027429)
                    ·
                      refine ⟨1498361710371758853567643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7991262455316047219027429 1498361710371758853567643)
                      ·
                        rfl

theorem cell23_2918049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_2918049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918049 prefixEnd_2918049 := by exact prefixLift 2918049
  have htrace : WordTrace (prefixWord ++ tailWord_2918049) baseStart_2918049 baseEnd_2918049 := by
    simpa [prefixWord, tailWord_2918049, baseEnd_2918049] using wordTrace_append hprefix tailTrace_2918049
  have hstable : (prefixWord ++ tailWord_2918049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918049).length < 2 ^ (prefixWord ++ tailWord_2918049).sum := by decide
  have hdescent : baseEnd_2918049 < baseStart_2918049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918052 : List Nat := [2, 3, 1, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_2918052 : Nat := 118140960795 + 2918052 * 2 ^ 59
def prefixEnd_2918052 : Nat := 4983230072969 + 3 ^ 40 * 2918052 * 2
def baseEnd_2918052 : Nat := 1498363250813722341830129

theorem tailTrace_2918052 : CollatzResearch.WordTrace tailWord_2918052 prefixEnd_2918052 1498363250813722341830129 := by
  unfold tailWord_2918052
  simp only [CollatzResearch.WordTrace]
  refine ⟨53215050012201721224978205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70953400016268961633304273 53215050012201721224978205)
  ·
    refine ⟨19955643754575645459366827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53215050012201721224978205 19955643754575645459366827)
    ·
      refine ⟨29933465631863468189050241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19955643754575645459366827 29933465631863468189050241)
      ·
        refine ⟨22450099223897601141787681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29933465631863468189050241 22450099223897601141787681)
        ·
          refine ⟨16837574417923200856340761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22450099223897601141787681 16837574417923200856340761)
          ·
            refine ⟨12628180813442400642255571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16837574417923200856340761 12628180813442400642255571)
            ·
              refine ⟨18942271220163600963383357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12628180813442400642255571 18942271220163600963383357)
              ·
                refine ⟨7103351707561350361268759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18942271220163600963383357 7103351707561350361268759)
                ·
                  refine ⟨10655027561342025541903139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7103351707561350361268759 10655027561342025541903139)
                  ·
                    refine ⟨15982541342013038312854709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10655027561342025541903139 15982541342013038312854709)
                    ·
                      refine ⟨1498363250813722341830129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15982541342013038312854709 1498363250813722341830129)
                      ·
                        rfl

theorem cell23_2918052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_2918052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918052 prefixEnd_2918052 := by exact prefixLift 2918052
  have htrace : WordTrace (prefixWord ++ tailWord_2918052) baseStart_2918052 baseEnd_2918052 := by
    simpa [prefixWord, tailWord_2918052, baseEnd_2918052] using wordTrace_append hprefix tailTrace_2918052
  have hstable : (prefixWord ++ tailWord_2918052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918052).length < 2 ^ (prefixWord ++ tailWord_2918052).sum := by decide
  have hdescent : baseEnd_2918052 < baseStart_2918052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918066 : List Nat := [3, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2]
def baseStart_2918066 : Nat := 118140960795 + 2918066 * 2 ^ 59
def prefixEnd_2918066 : Nat := 4983230072969 + 3 ^ 40 * 2918066 * 2
def baseEnd_2918066 : Nat := 1498370439542885287055065

theorem tailTrace_2918066 : CollatzResearch.WordTrace tailWord_2918066 prefixEnd_2918066 1498370439542885287055065 := by
  unfold tailWord_2918066
  simp only [CollatzResearch.WordTrace]
  refine ⟨26607652661588180710241513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70953740430901815227310701 26607652661588180710241513)
  ·
    refine ⟨19955739496191135532681135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26607652661588180710241513 19955739496191135532681135)
    ·
      refine ⟨29933609244286703299021703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19955739496191135532681135 29933609244286703299021703)
      ·
        refine ⟨44900413866430054948532555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29933609244286703299021703 44900413866430054948532555)
        ·
          refine ⟨67350620799645082422798833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44900413866430054948532555 67350620799645082422798833)
          ·
            refine ⟨50512965599733811817099125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67350620799645082422798833 50512965599733811817099125)
            ·
              refine ⟨4735590524975044857853043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50512965599733811817099125 4735590524975044857853043)
              ·
                refine ⟨7103385787462567286779565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4735590524975044857853043 7103385787462567286779565)
                ·
                  refine ⟨2663769670298462732542337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7103385787462567286779565 2663769670298462732542337)
                  ·
                    refine ⟨1997827252723847049406753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2663769670298462732542337 1997827252723847049406753)
                    ·
                      refine ⟨1498370439542885287055065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1997827252723847049406753 1498370439542885287055065)
                      ·
                        rfl

theorem cell23_2918066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_2918066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918066 prefixEnd_2918066 := by exact prefixLift 2918066
  have htrace : WordTrace (prefixWord ++ tailWord_2918066) baseStart_2918066 baseEnd_2918066 := by
    simpa [prefixWord, tailWord_2918066, baseEnd_2918066] using wordTrace_append hprefix tailTrace_2918066
  have hstable : (prefixWord ++ tailWord_2918066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918066).length < 2 ^ (prefixWord ++ tailWord_2918066).sum := by decide
  have hdescent : baseEnd_2918066 < baseStart_2918066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918076 : List Nat := [2, 2, 2, 3, 1, 2, 4, 1, 2, 4]
def baseStart_2918076 : Nat := 118140960795 + 2918076 * 2 ^ 59
def prefixEnd_2918076 : Nat := 4983230072969 + 3 ^ 40 * 2918076 * 2
def baseEnd_2918076 : Nat := 499458524783143415976673

theorem tailTrace_2918076 : CollatzResearch.WordTrace tailWord_2918076 prefixEnd_2918076 499458524783143415976673 := by
  unfold tailWord_2918076
  simp only [CollatzResearch.WordTrace]
  refine ⟨53215487688158247274415041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70953983584210996365886721 53215487688158247274415041)
  ·
    refine ⟨39911615766118685455811281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53215487688158247274415041 39911615766118685455811281)
    ·
      refine ⟨29933711824589014091858461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39911615766118685455811281 29933711824589014091858461)
      ·
        refine ⟨11225141934220880284446923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29933711824589014091858461 11225141934220880284446923)
        ·
          refine ⟨16837712901331320426670385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11225141934220880284446923 16837712901331320426670385)
          ·
            refine ⟨12628284675998490320002789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16837712901331320426670385 12628284675998490320002789)
            ·
              refine ⟨2367803376749716935000523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12628284675998490320002789 2367803376749716935000523)
              ·
                refine ⟨3551705065124575402500785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2367803376749716935000523 3551705065124575402500785)
                ·
                  refine ⟨2663778798843431551875589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3551705065124575402500785 2663778798843431551875589)
                  ·
                    refine ⟨499458524783143415976673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2663778798843431551875589 499458524783143415976673)
                    ·
                      rfl

theorem cell23_2918076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_2918076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918076 prefixEnd_2918076 := by exact prefixLift 2918076
  have htrace : WordTrace (prefixWord ++ tailWord_2918076) baseStart_2918076 baseEnd_2918076 := by
    simpa [prefixWord, tailWord_2918076, baseEnd_2918076] using wordTrace_append hprefix tailTrace_2918076
  have hstable : (prefixWord ++ tailWord_2918076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918076).length < 2 ^ (prefixWord ++ tailWord_2918076).sum := by decide
  have hdescent : baseEnd_2918076 < baseStart_2918076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918085 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 2, 7]
def baseStart_2918085 : Nat := 118140960795 + 2918085 * 2 ^ 59
def prefixEnd_2918085 : Nat := 4983230072969 + 3 ^ 40 * 2918085 * 2
def baseEnd_2918085 : Nat := 499460065225106904239159

theorem tailTrace_2918085 : CollatzResearch.WordTrace tailWord_2918085 prefixEnd_2918085 499460065225106904239159 := by
  unfold tailWord_2918085
  simp only [CollatzResearch.WordTrace]
  refine ⟨106431303633283889085907709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70954202422189259390605139 106431303633283889085907709)
  ·
    refine ⟨39911738862481458407215391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106431303633283889085907709 39911738862481458407215391)
    ·
      refine ⟨59867608293722187610823087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39911738862481458407215391 59867608293722187610823087)
      ·
        refine ⟨89801412440583281416234631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59867608293722187610823087 89801412440583281416234631)
        ·
          refine ⟨134702118660874922124351947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89801412440583281416234631 134702118660874922124351947)
          ·
            refine ⟨202053177991312383186527921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134702118660874922124351947 202053177991312383186527921)
            ·
              refine ⟨151539883493484287389895941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202053177991312383186527921 151539883493484287389895941)
              ·
                refine ⟨28413728155028303885605489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151539883493484287389895941 28413728155028303885605489)
                ·
                  refine ⟨21310296116271227914204117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28413728155028303885605489 21310296116271227914204117)
                  ·
                    refine ⟨499460065225106904239159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21310296116271227914204117 499460065225106904239159)
                    ·
                      rfl

theorem cell23_2918085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_2918085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918085 prefixEnd_2918085 := by exact prefixLift 2918085
  have htrace : WordTrace (prefixWord ++ tailWord_2918085) baseStart_2918085 baseEnd_2918085 := by
    simpa [prefixWord, tailWord_2918085, baseEnd_2918085] using wordTrace_append hprefix tailTrace_2918085
  have hstable : (prefixWord ++ tailWord_2918085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918085).length < 2 ^ (prefixWord ++ tailWord_2918085).sum := by decide
  have hdescent : baseEnd_2918085 < baseStart_2918085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918095 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 5]
def baseStart_2918095 : Nat := 118140960795 + 2918095 * 2 ^ 59
def prefixEnd_2918095 : Nat := 4983230072969 + 3 ^ 40 * 2918095 * 2
def baseEnd_2918095 : Nat := 1498385330481865673592431

theorem tailTrace_2918095 : CollatzResearch.WordTrace tailWord_2918095 prefixEnd_2918095 1498385330481865673592431 := by
  unfold tailWord_2918095
  simp only [CollatzResearch.WordTrace]
  refine ⟨106431668363247660793771739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70954445575498440529181159 106431668363247660793771739)
  ·
    refine ⟨159647502544871491190657609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106431668363247660793771739 159647502544871491190657609)
    ·
      refine ⟨119735626908653618392993207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159647502544871491190657609 119735626908653618392993207)
      ·
        refine ⟨179603440362980427589489811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119735626908653618392993207 179603440362980427589489811)
        ·
          refine ⟨269405160544470641384234717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179603440362980427589489811 269405160544470641384234717)
          ·
            refine ⟨101026935204176490519088019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269405160544470641384234717 101026935204176490519088019)
            ·
              refine ⟨151540402806264735778632029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101026935204176490519088019 151540402806264735778632029)
              ·
                refine ⟨56827651052349275916987011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151540402806264735778632029 56827651052349275916987011)
                ·
                  refine ⟨85241476578523913875480517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56827651052349275916987011 85241476578523913875480517)
                  ·
                    refine ⟨15982776858473233851652597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85241476578523913875480517 15982776858473233851652597)
                    ·
                      refine ⟨1498385330481865673592431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15982776858473233851652597 1498385330481865673592431)
                      ·
                        rfl

theorem cell23_2918095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_2918095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918095 prefixEnd_2918095 := by exact prefixLift 2918095
  have htrace : WordTrace (prefixWord ++ tailWord_2918095) baseStart_2918095 baseEnd_2918095 := by
    simpa [prefixWord, tailWord_2918095, baseEnd_2918095] using wordTrace_append hprefix tailTrace_2918095
  have hstable : (prefixWord ++ tailWord_2918095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918095).length < 2 ^ (prefixWord ++ tailWord_2918095).sum := by decide
  have hdescent : baseEnd_2918095 < baseStart_2918095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918116 : List Nat := [2, 3, 1, 1, 1, 3, 4, 2, 2, 1, 3]
def baseStart_2918116 : Nat := 118140960795 + 2918116 * 2 ^ 59
def prefixEnd_2918116 : Nat := 4983230072969 + 3 ^ 40 * 2918116 * 2
def baseEnd_2918116 : Nat := 1498396113575610091429835

theorem tailTrace_2918116 : CollatzResearch.WordTrace tailWord_2918116 prefixEnd_2918116 1498396113575610091429835 := by
  unfold tailWord_2918116
  simp only [CollatzResearch.WordTrace]
  refine ⟨53216217148085790690143101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70954956197447720920190801 53216217148085790690143101)
  ·
    refine ⟨19956081430532171508803663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53216217148085790690143101 19956081430532171508803663)
    ·
      refine ⟨29934122145798257263205495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19956081430532171508803663 29934122145798257263205495)
      ·
        refine ⟨44901183218697385894808243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29934122145798257263205495 44901183218697385894808243)
        ·
          refine ⟨67351774828046078842212365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44901183218697385894808243 67351774828046078842212365)
          ·
            refine ⟨25256915560517279565829637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67351774828046078842212365 25256915560517279565829637)
            ·
              refine ⟨4735671667596989918593057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25256915560517279565829637 4735671667596989918593057)
              ·
                refine ⟨3551753750697742438944793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4735671667596989918593057 3551753750697742438944793)
                ·
                  refine ⟨2663815313023306829208595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3551753750697742438944793 2663815313023306829208595)
                  ·
                    refine ⟨3995722969534960243812893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2663815313023306829208595 3995722969534960243812893)
                    ·
                      refine ⟨1498396113575610091429835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3995722969534960243812893 1498396113575610091429835)
                      ·
                        rfl

theorem cell23_2918116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_2918116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918116 prefixEnd_2918116 := by exact prefixLift 2918116
  have htrace : WordTrace (prefixWord ++ tailWord_2918116) baseStart_2918116 baseEnd_2918116 := by
    simpa [prefixWord, tailWord_2918116, baseEnd_2918116] using wordTrace_append hprefix tailTrace_2918116
  have hstable : (prefixWord ++ tailWord_2918116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918116).length < 2 ^ (prefixWord ++ tailWord_2918116).sum := by decide
  have hdescent : baseEnd_2918116 < baseStart_2918116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918122 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_2918122 : Nat := 118140960795 + 2918122 * 2 ^ 59
def prefixEnd_2918122 : Nat := 4983230072969 + 3 ^ 40 * 2918122 * 2
def baseEnd_2918122 : Nat := 1498399194459537067954807

theorem tailTrace_2918122 : CollatzResearch.WordTrace tailWord_2918122 prefixEnd_2918122 1498399194459537067954807 := by
  unfold tailWord_2918122
  simp only [CollatzResearch.WordTrace]
  refine ⟨26608163283537461101251155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70955102089433229603336413 26608163283537461101251155)
  ·
    refine ⟨39912244925306191651876733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26608163283537461101251155 39912244925306191651876733)
    ·
      refine ⟨14967091846989821869453775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39912244925306191651876733 14967091846989821869453775)
      ·
        refine ⟨22450637770484732804180663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14967091846989821869453775 22450637770484732804180663)
        ·
          refine ⟨33675956655727099206270995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22450637770484732804180663 33675956655727099206270995)
          ·
            refine ⟨50513934983590648809406493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33675956655727099206270995 50513934983590648809406493)
            ·
              refine ⟨18942725618846493303527435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50513934983590648809406493 18942725618846493303527435)
              ·
                refine ⟨28414088428269739955291153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18942725618846493303527435 28414088428269739955291153)
                ·
                  refine ⟨21310566321202304966468365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28414088428269739955291153 21310566321202304966468365)
                  ·
                    refine ⟨7991462370450864362425637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21310566321202304966468365 7991462370450864362425637)
                    ·
                      refine ⟨1498399194459537067954807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7991462370450864362425637 1498399194459537067954807)
                      ·
                        rfl

theorem cell23_2918122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_2918122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918122 prefixEnd_2918122 := by exact prefixLift 2918122
  have htrace : WordTrace (prefixWord ++ tailWord_2918122) baseStart_2918122 baseEnd_2918122 := by
    simpa [prefixWord, tailWord_2918122, baseEnd_2918122] using wordTrace_append hprefix tailTrace_2918122
  have hstable : (prefixWord ++ tailWord_2918122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918122).length < 2 ^ (prefixWord ++ tailWord_2918122).sum := by decide
  have hdescent : baseEnd_2918122 < baseStart_2918122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918152 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_2918152 : Nat := 118140960795 + 2918152 * 2 ^ 59
def prefixEnd_2918152 : Nat := 4983230072969 + 3 ^ 40 * 2918152 * 2
def baseEnd_2918152 : Nat := 1498414598879171950579669

theorem tailTrace_2918152 : CollatzResearch.WordTrace tailWord_2918152 prefixEnd_2918152 1498414598879171950579669 := by
  unfold tailWord_2918152
  simp only [CollatzResearch.WordTrace]
  refine ⟨53216873662020579764298355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70955831549360773019064473 53216873662020579764298355)
  ·
    refine ⟨79825310493030869646447533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53216873662020579764298355 79825310493030869646447533)
    ·
      refine ⟨29934491434886576117417825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79825310493030869646447533 29934491434886576117417825)
      ·
        refine ⟨22450868576164932088063369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29934491434886576117417825 22450868576164932088063369)
        ·
          refine ⟨16838151432123699066047527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22450868576164932088063369 16838151432123699066047527)
          ·
            refine ⟨25257227148185548599071291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16838151432123699066047527 25257227148185548599071291)
            ·
              refine ⟨37885840722278322898606937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25257227148185548599071291 37885840722278322898606937)
              ·
                refine ⟨28414380541708742173955203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37885840722278322898606937 28414380541708742173955203)
                ·
                  refine ⟨42621570812563113260932805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28414380541708742173955203 42621570812563113260932805)
                  ·
                    refine ⟨7991544527355583736424901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42621570812563113260932805 7991544527355583736424901)
                    ·
                      refine ⟨1498414598879171950579669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7991544527355583736424901 1498414598879171950579669)
                      ·
                        rfl

theorem cell23_2918152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_2918152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918152 prefixEnd_2918152 := by exact prefixLift 2918152
  have htrace : WordTrace (prefixWord ++ tailWord_2918152) baseStart_2918152 baseEnd_2918152 := by
    simpa [prefixWord, tailWord_2918152, baseEnd_2918152] using wordTrace_append hprefix tailTrace_2918152
  have hstable : (prefixWord ++ tailWord_2918152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918152).length < 2 ^ (prefixWord ++ tailWord_2918152).sum := by decide
  have hdescent : baseEnd_2918152 < baseStart_2918152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918179 : List Nat := [1, 1, 1, 4, 2, 1, 4, 4, 5]
def baseStart_2918179 : Nat := 118140960795 + 2918179 * 2 ^ 59
def prefixEnd_2918179 : Nat := 4983230072969 + 3 ^ 40 * 2918179 * 2
def baseEnd_2918179 : Nat := 166492051428538149438005

theorem tailTrace_2918179 : CollatzResearch.WordTrace tailWord_2918179 prefixEnd_2918179 166492051428538149438005 := by
  unfold tailWord_2918179
  simp only [CollatzResearch.WordTrace]
  refine ⟨106434732094943343139829591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70956488063295562093219727 106434732094943343139829591)
  ·
    refine ⟨159652098142415014709744387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106434732094943343139829591 159652098142415014709744387)
    ·
      refine ⟨239478147213622522064616581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159652098142415014709744387 239478147213622522064616581)
      ·
        refine ⟨44902152602554222887115609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239478147213622522064616581 44902152602554222887115609)
        ·
          refine ⟨33676614451915667165336707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44902152602554222887115609 33676614451915667165336707)
          ·
            refine ⟨50514921677873500748005061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33676614451915667165336707 50514921677873500748005061)
            ·
              refine ⟨9471547814601281390250949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50514921677873500748005061 9471547814601281390250949)
              ·
                refine ⟨1775915215237740260672053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9471547814601281390250949 1775915215237740260672053)
                ·
                  refine ⟨166492051428538149438005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1775915215237740260672053 166492051428538149438005)
                  ·
                    rfl

theorem cell23_2918179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 5].length) (baseStart_2918179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918179 prefixEnd_2918179 := by exact prefixLift 2918179
  have htrace : WordTrace (prefixWord ++ tailWord_2918179) baseStart_2918179 baseEnd_2918179 := by
    simpa [prefixWord, tailWord_2918179, baseEnd_2918179] using wordTrace_append hprefix tailTrace_2918179
  have hstable : (prefixWord ++ tailWord_2918179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918179).length < 2 ^ (prefixWord ++ tailWord_2918179).sum := by decide
  have hdescent : baseEnd_2918179 < baseStart_2918179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918190 : List Nat := [4, 1, 3, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_2918190 : Nat := 118140960795 + 2918190 * 2 ^ 59
def prefixEnd_2918190 : Nat := 4983230072969 + 3 ^ 40 * 2918190 * 2
def baseEnd_2918190 : Nat := 1498434111144042801904495

theorem tailTrace_2918190 : CollatzResearch.WordTrace tailWord_2918190 prefixEnd_2918190 1498434111144042801904495 := by
  unfold tailWord_2918190
  simp only [CollatzResearch.WordTrace]
  refine ⟨13304391662237936502310003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70956755531935661345653349 13304391662237936502310003)
  ·
    refine ⟨19956587493356904753465005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13304391662237936502310003 19956587493356904753465005)
    ·
      refine ⟨7483720310008839282549377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19956587493356904753465005 7483720310008839282549377)
      ·
        refine ⟨5612790232506629461912033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7483720310008839282549377 5612790232506629461912033)
        ·
          refine ⟨4209592674379972096434025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5612790232506629461912033 4209592674379972096434025)
          ·
            refine ⟨3157194505784979072325519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4209592674379972096434025 3157194505784979072325519)
            ·
              refine ⟨4735791758677468608488279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3157194505784979072325519 4735791758677468608488279)
              ·
                refine ⟨7103687638016202912732419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4735791758677468608488279 7103687638016202912732419)
                ·
                  refine ⟨10655531457024304369098629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7103687638016202912732419 10655531457024304369098629)
                  ·
                    refine ⟨1997912148192057069205993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10655531457024304369098629 1997912148192057069205993)
                    ·
                      refine ⟨1498434111144042801904495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1997912148192057069205993 1498434111144042801904495)
                      ·
                        rfl

theorem cell23_2918190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_2918190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918190 prefixEnd_2918190 := by exact prefixLift 2918190
  have htrace : WordTrace (prefixWord ++ tailWord_2918190) baseStart_2918190 baseEnd_2918190 := by
    simpa [prefixWord, tailWord_2918190, baseEnd_2918190] using wordTrace_append hprefix tailTrace_2918190
  have hstable : (prefixWord ++ tailWord_2918190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918190).length < 2 ^ (prefixWord ++ tailWord_2918190).sum := by decide
  have hdescent : baseEnd_2918190 < baseStart_2918190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918229 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_2918229 : Nat := 118140960795 + 2918229 * 2 ^ 59
def prefixEnd_2918229 : Nat := 4983230072969 + 3 ^ 40 * 2918229 * 2
def baseEnd_2918229 : Nat := 1498454136889568149316815

theorem tailTrace_2918229 : CollatzResearch.WordTrace tailWord_2918229 prefixEnd_2918229 1498454136889568149316815 := by
  unfold tailWord_2918229
  simp only [CollatzResearch.WordTrace]
  refine ⟨106436555744762201679149741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70957703829841467786099827 106436555744762201679149741)
  ·
    refine ⟨39913708404285825629681153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106436555744762201679149741 39913708404285825629681153)
    ·
      refine ⟨29935281303214369222260865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39913708404285825629681153 29935281303214369222260865)
      ·
        refine ⟨22451460977410776916695649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29935281303214369222260865 22451460977410776916695649)
        ·
          refine ⟨16838595733058082687521737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22451460977410776916695649 16838595733058082687521737)
          ·
            refine ⟨12628946799793562015641303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16838595733058082687521737 12628946799793562015641303)
            ·
              refine ⟨18943420199690343023461955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12628946799793562015641303 18943420199690343023461955)
              ·
                refine ⟨28415130299535514535192933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18943420199690343023461955 28415130299535514535192933)
                ·
                  refine ⟨5327836931162908975348675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28415130299535514535192933 5327836931162908975348675)
                  ·
                    refine ⟨7991755396744363463023013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5327836931162908975348675 7991755396744363463023013)
                    ·
                      refine ⟨1498454136889568149316815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7991755396744363463023013 1498454136889568149316815)
                      ·
                        rfl

theorem cell23_2918229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_2918229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918229 prefixEnd_2918229 := by exact prefixLift 2918229
  have htrace : WordTrace (prefixWord ++ tailWord_2918229) baseStart_2918229 baseEnd_2918229 := by
    simpa [prefixWord, tailWord_2918229, baseEnd_2918229] using wordTrace_append hprefix tailTrace_2918229
  have hstable : (prefixWord ++ tailWord_2918229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918229).length < 2 ^ (prefixWord ++ tailWord_2918229).sum := by decide
  have hdescent : baseEnd_2918229 < baseStart_2918229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918236 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_2918236 : Nat := 118140960795 + 2918236 * 2 ^ 59
def prefixEnd_2918236 : Nat := 4983230072969 + 3 ^ 40 * 2918236 * 2
def baseEnd_2918236 : Nat := 1498457731254149621929283

theorem tailTrace_2918236 : CollatzResearch.WordTrace tailWord_2918236 prefixEnd_2918236 1498457731254149621929283 := by
  unfold tailWord_2918236
  simp only [CollatzResearch.WordTrace]
  refine ⟨53218405527868420937327281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70957874037157894583103041 53218405527868420937327281)
  ·
    refine ⟨39913804145901315702995461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53218405527868420937327281 39913804145901315702995461)
    ·
      refine ⟨7483838277356496694311649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39913804145901315702995461 7483838277356496694311649)
      ·
        refine ⟨5612878708017372520733737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7483838277356496694311649 5612878708017372520733737)
        ·
          refine ⟨4209659031013029390550303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5612878708017372520733737 4209659031013029390550303)
          ·
            refine ⟨6314488546519544085825455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4209659031013029390550303 6314488546519544085825455)
            ·
              refine ⟨9471732819779316128738183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6314488546519544085825455 9471732819779316128738183)
              ·
                refine ⟨14207599229668974193107275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9471732819779316128738183 14207599229668974193107275)
                ·
                  refine ⟨21311398844503461289660913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14207599229668974193107275 21311398844503461289660913)
                  ·
                    refine ⟨15983549133377595967245685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21311398844503461289660913 15983549133377595967245685)
                    ·
                      refine ⟨1498457731254149621929283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15983549133377595967245685 1498457731254149621929283)
                      ·
                        rfl

theorem cell23_2918236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_2918236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918236 prefixEnd_2918236 := by exact prefixLift 2918236
  have htrace : WordTrace (prefixWord ++ tailWord_2918236) baseStart_2918236 baseEnd_2918236 := by
    simpa [prefixWord, tailWord_2918236, baseEnd_2918236] using wordTrace_append hprefix tailTrace_2918236
  have hstable : (prefixWord ++ tailWord_2918236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918236).length < 2 ^ (prefixWord ++ tailWord_2918236).sum := by decide
  have hdescent : baseEnd_2918236 < baseStart_2918236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918290 : List Nat := [3, 2, 3, 2, 1, 2, 1, 4, 1, 4]
def baseStart_2918290 : Nat := 118140960795 + 2918290 * 2 ^ 59
def prefixEnd_2918290 : Nat := 4983230072969 + 3 ^ 40 * 2918290 * 2
def baseEnd_2918290 : Nat := 499495153069830803551345

theorem tailTrace_2918290 : CollatzResearch.WordTrace tailWord_2918290 prefixEnd_2918290 499495153069830803551345 := by
  unfold tailWord_2918290
  simp only [CollatzResearch.WordTrace]
  refine ⟨26609695149385302274280081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70959187065027472731413549 26609695149385302274280081)
  ·
    refine ⟨19957271362038976705710061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26609695149385302274280081 19957271362038976705710061)
    ·
      refine ⟨7483976760764616264641273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19957271362038976705710061 7483976760764616264641273)
      ·
        refine ⟨5612982570573462198480955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7483976760764616264641273 5612982570573462198480955)
        ·
          refine ⟨8419473855860193297721433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5612982570573462198480955 8419473855860193297721433)
          ·
            refine ⟨6314605391895144973291075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8419473855860193297721433 6314605391895144973291075)
            ·
              refine ⟨9471908087842717459936613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6314605391895144973291075 9471908087842717459936613)
              ·
                refine ⟨1775982766470509523738115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9471908087842717459936613 1775982766470509523738115)
                ·
                  refine ⟨2663974149705764285607173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1775982766470509523738115 2663974149705764285607173)
                  ·
                    refine ⟨499495153069830803551345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2663974149705764285607173 499495153069830803551345)
                    ·
                      rfl

theorem cell23_2918290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_2918290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918290 prefixEnd_2918290 := by exact prefixLift 2918290
  have htrace : WordTrace (prefixWord ++ tailWord_2918290) baseStart_2918290 baseEnd_2918290 := by
    simpa [prefixWord, tailWord_2918290, baseEnd_2918290] using wordTrace_append hprefix tailTrace_2918290
  have hstable : (prefixWord ++ tailWord_2918290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918290).length < 2 ^ (prefixWord ++ tailWord_2918290).sum := by decide
  have hdescent : baseEnd_2918290 < baseStart_2918290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918319 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 4]
def baseStart_2918319 : Nat := 118140960795 + 2918319 * 2 ^ 59
def prefixEnd_2918319 : Nat := 4983230072969 + 3 ^ 40 * 2918319 * 2
def baseEnd_2918319 : Nat := 1498500350148472797191401

theorem tailTrace_2918319 : CollatzResearch.WordTrace tailWord_2918319 prefixEnd_2918319 1498500350148472797191401 := by
  unfold tailWord_2918319
  simp only [CollatzResearch.WordTrace]
  refine ⟨106439838314436147049926011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70959892209624098033284007 106439838314436147049926011)
  ·
    refine ⟨159659757471654220574889017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106439838314436147049926011 159659757471654220574889017)
    ·
      refine ⟨119744818103740665431166763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159659757471654220574889017 119744818103740665431166763)
      ·
        refine ⟨179617227155610998146750145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119744818103740665431166763 179617227155610998146750145)
        ·
          refine ⟨134712920366708248610062609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179617227155610998146750145 134712920366708248610062609)
          ·
            refine ⟨101034690275031186457546957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134712920366708248610062609 101034690275031186457546957)
            ·
              refine ⟨37888008853136694921580109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101034690275031186457546957 37888008853136694921580109)
              ·
                refine ⟨14208003319926260595592541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37888008853136694921580109 14208003319926260595592541)
                ·
                  refine ⟨5328001244972347723347203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14208003319926260595592541 5328001244972347723347203)
                  ·
                    refine ⟨7992001867458521585020805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5328001244972347723347203 7992001867458521585020805)
                    ·
                      refine ⟨1498500350148472797191401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7992001867458521585020805 1498500350148472797191401)
                      ·
                        rfl

theorem cell23_2918319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 4].length) (baseStart_2918319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918319 prefixEnd_2918319 := by exact prefixLift 2918319
  have htrace : WordTrace (prefixWord ++ tailWord_2918319) baseStart_2918319 baseEnd_2918319 := by
    simpa [prefixWord, tailWord_2918319, baseEnd_2918319] using wordTrace_append hprefix tailTrace_2918319
  have hstable : (prefixWord ++ tailWord_2918319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918319).length < 2 ^ (prefixWord ++ tailWord_2918319).sum := by decide
  have hdescent : baseEnd_2918319 < baseStart_2918319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918329 : List Nat := [1, 2, 1, 4, 2, 1, 1, 4, 1, 6]
def baseStart_2918329 : Nat := 118140960795 + 2918329 * 2 ^ 59
def prefixEnd_2918329 : Nat := 4983230072969 + 3 ^ 40 * 2918329 * 2
def baseEnd_2918329 : Nat := 499501828318339252688785

theorem tailTrace_2918329 : CollatzResearch.WordTrace tailWord_2918329 prefixEnd_2918329 499501828318339252688785 := by
  unfold tailWord_2918329
  simp only [CollatzResearch.WordTrace]
  refine ⟨106440203044399918757790041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70960135362933279171860027 106440203044399918757790041)
  ·
    refine ⟨79830152283299939068342531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106440203044399918757790041 79830152283299939068342531)
    ·
      refine ⟨119745228424949908602513797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79830152283299939068342531 119745228424949908602513797)
      ·
        refine ⟨22452230329678107862971337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119745228424949908602513797 22452230329678107862971337)
        ·
          refine ⟨16839172747258580897228503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22452230329678107862971337 16839172747258580897228503)
          ·
            refine ⟨25258759120887871345842755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16839172747258580897228503 25258759120887871345842755)
            ·
              refine ⟨37888138681331807018764133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25258759120887871345842755 37888138681331807018764133)
              ·
                refine ⟨7104026002749713816018275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37888138681331807018764133 7104026002749713816018275)
                ·
                  refine ⟨10656039004124570724027413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7104026002749713816018275 10656039004124570724027413)
                  ·
                    refine ⟨499501828318339252688785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10656039004124570724027413 499501828318339252688785)
                    ·
                      rfl

theorem cell23_2918329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 6].length) (baseStart_2918329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918329 prefixEnd_2918329 := by exact prefixLift 2918329
  have htrace : WordTrace (prefixWord ++ tailWord_2918329) baseStart_2918329 baseEnd_2918329 := by
    simpa [prefixWord, tailWord_2918329, baseEnd_2918329] using wordTrace_append hprefix tailTrace_2918329
  have hstable : (prefixWord ++ tailWord_2918329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918329).length < 2 ^ (prefixWord ++ tailWord_2918329).sum := by decide
  have hdescent : baseEnd_2918329 < baseStart_2918329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918333 : List Nat := [1, 4, 1, 2, 3, 1, 4, 1, 1, 5]
def baseStart_2918333 : Nat := 118140960795 + 2918333 * 2 ^ 59
def prefixEnd_2918333 : Nat := 4983230072969 + 3 ^ 40 * 2918333 * 2
def baseEnd_2918333 : Nat := 499502512959211914138779

theorem tailTrace_2918333 : CollatzResearch.WordTrace tailWord_2918333 prefixEnd_2918333 499502512959211914138779 := by
  unfold tailWord_2918333
  simp only [CollatzResearch.WordTrace]
  refine ⟨106440348936385427440935653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70960232624256951627290435 106440348936385427440935653)
  ·
    refine ⟨19957565425572267645175435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106440348936385427440935653 19957565425572267645175435)
    ·
      refine ⟨29936348138358401467763153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19957565425572267645175435 29936348138358401467763153)
      ·
        refine ⟨22452261103768801100822365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29936348138358401467763153 22452261103768801100822365)
        ·
          refine ⟨8419597913913300412808387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22452261103768801100822365 8419597913913300412808387)
          ·
            refine ⟨12629396870869950619212581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8419597913913300412808387 12629396870869950619212581)
            ·
              refine ⟨2368011913288115741102359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12629396870869950619212581 2368011913288115741102359)
              ·
                refine ⟨3552017869932173611653539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2368011913288115741102359 3552017869932173611653539)
                ·
                  refine ⟨5328026804898260417480309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3552017869932173611653539 5328026804898260417480309)
                  ·
                    refine ⟨499502512959211914138779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5328026804898260417480309 499502512959211914138779)
                    ·
                      rfl

theorem cell23_2918333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_2918333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918333 prefixEnd_2918333 := by exact prefixLift 2918333
  have htrace : WordTrace (prefixWord ++ tailWord_2918333) baseStart_2918333 baseEnd_2918333 := by
    simpa [prefixWord, tailWord_2918333, baseEnd_2918333] using wordTrace_append hprefix tailTrace_2918333
  have hstable : (prefixWord ++ tailWord_2918333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918333).length < 2 ^ (prefixWord ++ tailWord_2918333).sum := by decide
  have hdescent : baseEnd_2918333 < baseStart_2918333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918336 : List Nat := [2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 4]
def baseStart_2918336 : Nat := 118140960795 + 2918336 * 2 ^ 59
def prefixEnd_2918336 : Nat := 4983230072969 + 3 ^ 40 * 2918336 * 2
def baseEnd_2918336 : Nat := 1498509079319599230678823

theorem tailTrace_2918336 : CollatzResearch.WordTrace tailWord_2918336 prefixEnd_2918336 1498509079319599230678823 := by
  unfold tailWord_2918336
  simp only [CollatzResearch.WordTrace]
  refine ⟨53220229177687279476647431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70960305570249705968863241 53220229177687279476647431)
  ·
    refine ⟨79830343766530919214971147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53220229177687279476647431 79830343766530919214971147)
    ·
      refine ⟨119745515649796378822456721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79830343766530919214971147 119745515649796378822456721)
      ·
        refine ⟨89809136737347284116842541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119745515649796378822456721 89809136737347284116842541)
        ·
          refine ⟨33678426276505231543815953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89809136737347284116842541 33678426276505231543815953)
          ·
            refine ⟨25258819707378923657861965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33678426276505231543815953 25258819707378923657861965)
            ·
              refine ⟨9472057390267096371698237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25258819707378923657861965 9472057390267096371698237)
              ·
                refine ⟨3552021521350161139386839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9472057390267096371698237 3552021521350161139386839)
                ·
                  refine ⟨5328032282025241709080259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3552021521350161139386839 5328032282025241709080259)
                  ·
                    refine ⟨7992048423037862563620389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5328032282025241709080259 7992048423037862563620389)
                    ·
                      refine ⟨1498509079319599230678823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7992048423037862563620389 1498509079319599230678823)
                      ·
                        rfl

theorem cell23_2918336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 4].length) (baseStart_2918336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918336 prefixEnd_2918336 := by exact prefixLift 2918336
  have htrace : WordTrace (prefixWord ++ tailWord_2918336) baseStart_2918336 baseEnd_2918336 := by
    simpa [prefixWord, tailWord_2918336, baseEnd_2918336] using wordTrace_append hprefix tailTrace_2918336
  have hstable : (prefixWord ++ tailWord_2918336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918336).length < 2 ^ (prefixWord ++ tailWord_2918336).sum := by decide
  have hdescent : baseEnd_2918336 < baseStart_2918336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918356 : List Nat := [2, 4, 1, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_2918356 : Nat := 118140960795 + 2918356 * 2 ^ 59
def prefixEnd_2918356 : Nat := 4983230072969 + 3 ^ 40 * 2918356 * 2
def baseEnd_2918356 : Nat := 1498519348932689152428731

theorem tailTrace_2918356 : CollatzResearch.WordTrace tailWord_2918356 prefixEnd_2918356 1498519348932689152428731 := by
  unfold tailWord_2918356
  simp only [CollatzResearch.WordTrace]
  refine ⟨53220593907651051184511461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70960791876868068246015281 53220593907651051184511461)
  ·
    refine ⟨9978861357684572097095899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53220593907651051184511461 9978861357684572097095899)
    ·
      refine ⟨14968292036526858145643849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9978861357684572097095899 14968292036526858145643849)
      ·
        refine ⟨11226219027395143609232887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14968292036526858145643849 11226219027395143609232887)
        ·
          refine ⟨16839328541092715413849331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11226219027395143609232887 16839328541092715413849331)
          ·
            refine ⟨25258992811639073120773997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16839328541092715413849331 25258992811639073120773997)
            ·
              refine ⟨9472122304364652420290249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25258992811639073120773997 9472122304364652420290249)
              ·
                refine ⟨7104091728273489315217687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9472122304364652420290249 7104091728273489315217687)
                ·
                  refine ⟨10656137592410233972826531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7104091728273489315217687 10656137592410233972826531)
                  ·
                    refine ⟨15984206388615350959239797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10656137592410233972826531 15984206388615350959239797)
                    ·
                      refine ⟨1498519348932689152428731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15984206388615350959239797 1498519348932689152428731)
                      ·
                        rfl

theorem cell23_2918356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_2918356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918356 prefixEnd_2918356 := by exact prefixLift 2918356
  have htrace : WordTrace (prefixWord ++ tailWord_2918356) baseStart_2918356 baseEnd_2918356 := by
    simpa [prefixWord, tailWord_2918356, baseEnd_2918356] using wordTrace_append hprefix tailTrace_2918356
  have hstable : (prefixWord ++ tailWord_2918356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918356).length < 2 ^ (prefixWord ++ tailWord_2918356).sum := by decide
  have hdescent : baseEnd_2918356 < baseStart_2918356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918381 : List Nat := [1, 5, 1, 4, 2, 1, 1, 3, 1, 1, 3]
def baseStart_2918381 : Nat := 118140960795 + 2918381 * 2 ^ 59
def prefixEnd_2918381 : Nat := 4983230072969 + 3 ^ 40 * 2918381 * 2
def baseEnd_2918381 : Nat := 1498532185949051554616117

theorem tailTrace_2918381 : CollatzResearch.WordTrace tailWord_2918381 prefixEnd_2918381 1498532185949051554616117 := by
  unfold tailWord_2918381
  simp only [CollatzResearch.WordTrace]
  refine ⟨106442099640211531638682997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70961399760141021092455331 106442099640211531638682997)
  ·
    refine ⟨9978946841269831091126531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106442099640211531638682997 9978946841269831091126531)
    ·
      refine ⟨14968420261904746636689797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9978946841269831091126531 14968420261904746636689797)
      ·
        refine ⟨2806578799107139994379337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14968420261904746636689797 2806578799107139994379337)
        ·
          refine ⟨2104934099330354995784503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2806578799107139994379337 2104934099330354995784503)
          ·
            refine ⟨3157401148995532493676755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2104934099330354995784503 3157401148995532493676755)
            ·
              refine ⟨4736101723493298740515133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3157401148995532493676755 4736101723493298740515133)
              ·
                refine ⟨1776038146309987027693175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4736101723493298740515133 1776038146309987027693175)
                ·
                  refine ⟨2664057219464980541539763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776038146309987027693175 2664057219464980541539763)
                  ·
                    refine ⟨3996085829197470812309645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2664057219464980541539763 3996085829197470812309645)
                    ·
                      refine ⟨1498532185949051554616117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3996085829197470812309645 1498532185949051554616117)
                      ·
                        rfl

theorem cell23_2918381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_2918381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918381 prefixEnd_2918381 := by exact prefixLift 2918381
  have htrace : WordTrace (prefixWord ++ tailWord_2918381) baseStart_2918381 baseEnd_2918381 := by
    simpa [prefixWord, tailWord_2918381, baseEnd_2918381] using wordTrace_append hprefix tailTrace_2918381
  have hstable : (prefixWord ++ tailWord_2918381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918381).length < 2 ^ (prefixWord ++ tailWord_2918381).sum := by decide
  have hdescent : baseEnd_2918381 < baseStart_2918381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918404 : List Nat := [2, 3, 2, 4, 1, 2, 1, 1, 3, 2, 2]
def baseStart_2918404 : Nat := 118140960795 + 2918404 * 2 ^ 59
def prefixEnd_2918404 : Nat := 4983230072969 + 3 ^ 40 * 2918404 * 2
def baseEnd_2918404 : Nat := 1498543996004104964628511

theorem tailTrace_2918404 : CollatzResearch.WordTrace tailWord_2918404 prefixEnd_2918404 1498543996004104964628511 := by
  unfold tailWord_2918404
  simp only [CollatzResearch.WordTrace]
  refine ⟨53221469259564103283385133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70961959012752137711180177 53221469259564103283385133)
  ·
    refine ⟨19958050972336538731269425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53221469259564103283385133 19958050972336538731269425)
    ·
      refine ⟨14968538229252404048452069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19958050972336538731269425 14968538229252404048452069)
      ·
        refine ⟨2806600917984825759084763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14968538229252404048452069 2806600917984825759084763)
        ·
          refine ⟨4209901376977238638627145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2806600917984825759084763 4209901376977238638627145)
          ·
            refine ⟨3157426032732928978970359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4209901376977238638627145 3157426032732928978970359)
            ·
              refine ⟨4736139049099393468455539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3157426032732928978970359 4736139049099393468455539)
              ·
                refine ⟨7104208573649090202683309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4736139049099393468455539 7104208573649090202683309)
                ·
                  refine ⟨2664078215118408826006241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7104208573649090202683309 2664078215118408826006241)
                  ·
                    refine ⟨1998058661338806619504681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2664078215118408826006241 1998058661338806619504681)
                    ·
                      refine ⟨1498543996004104964628511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1998058661338806619504681 1498543996004104964628511)
                      ·
                        rfl

theorem cell23_2918404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_2918404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918404 prefixEnd_2918404 := by exact prefixLift 2918404
  have htrace : WordTrace (prefixWord ++ tailWord_2918404) baseStart_2918404 baseEnd_2918404 := by
    simpa [prefixWord, tailWord_2918404, baseEnd_2918404] using wordTrace_append hprefix tailTrace_2918404
  have hstable : (prefixWord ++ tailWord_2918404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918404).length < 2 ^ (prefixWord ++ tailWord_2918404).sum := by decide
  have hdescent : baseEnd_2918404 < baseStart_2918404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918419 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 2, 6]
def baseStart_2918419 : Nat := 118140960795 + 2918419 * 2 ^ 59
def prefixEnd_2918419 : Nat := 4983230072969 + 3 ^ 40 * 2918419 * 2
def baseEnd_2918419 : Nat := 499517232737974135313647

theorem tailTrace_2918419 : CollatzResearch.WordTrace tailWord_2918419 prefixEnd_2918419 499517232737974135313647 := by
  unfold tailWord_2918419
  simp only [CollatzResearch.WordTrace]
  refine ⟨106443485614073864128566311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70962323742715909419044207 106443485614073864128566311)
  ·
    refine ⟨159665228421110796192849467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106443485614073864128566311 159665228421110796192849467)
    ·
      refine ⟨239497842631666194289274201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159665228421110796192849467 239497842631666194289274201)
      ·
        refine ⟨179623381973749645716955651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239497842631666194289274201 179623381973749645716955651)
        ·
          refine ⟨269435072960624468575433477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179623381973749645716955651 269435072960624468575433477)
          ·
            refine ⟨50519076180117087857893777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 269435072960624468575433477 50519076180117087857893777)
            ·
              refine ⟨37889307135087815893420333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50519076180117087857893777 37889307135087815893420333)
              ·
                refine ⟨14208490175657930960032625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37889307135087815893420333 14208490175657930960032625)
                ·
                  refine ⟨10656367631743448220024469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14208490175657930960032625 10656367631743448220024469)
                  ·
                    refine ⟨499517232737974135313647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10656367631743448220024469 499517232737974135313647)
                    ·
                      rfl

theorem cell23_2918419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 6].length) (baseStart_2918419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918419 prefixEnd_2918419 := by exact prefixLift 2918419
  have htrace : WordTrace (prefixWord ++ tailWord_2918419) baseStart_2918419 baseEnd_2918419 := by
    simpa [prefixWord, tailWord_2918419, baseEnd_2918419] using wordTrace_append hprefix tailTrace_2918419
  have hstable : (prefixWord ++ tailWord_2918419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918419).length < 2 ^ (prefixWord ++ tailWord_2918419).sum := by decide
  have hdescent : baseEnd_2918419 < baseStart_2918419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918443 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 4, 2, 2]
def baseStart_2918443 : Nat := 118140960795 + 2918443 * 2 ^ 59
def prefixEnd_2918443 : Nat := 4983230072969 + 3 ^ 40 * 2918443 * 2
def baseEnd_2918443 : Nat := 1498564021749630312040831

theorem tailTrace_2918443 : CollatzResearch.WordTrace tailWord_2918443 prefixEnd_2918443 1498564021749630312040831 := by
  unfold tailWord_2918443
  simp only [CollatzResearch.WordTrace]
  refine ⟨106444360965986916227439983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70962907310657944151626655 106444360965986916227439983)
  ·
    refine ⟨159666541448980374341159975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106444360965986916227439983 159666541448980374341159975)
    ·
      refine ⟨239499812173470561511739963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159666541448980374341159975 239499812173470561511739963)
      ·
        refine ⟨359249718260205842267609945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239499812173470561511739963 359249718260205842267609945)
        ·
          refine ⟨269437288695154381700707459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359249718260205842267609945 269437288695154381700707459)
          ·
            refine ⟨404155933042731572551061189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269437288695154381700707459 404155933042731572551061189)
            ·
              refine ⟨75779237445512169853323973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 404155933042731572551061189 75779237445512169853323973)
              ·
                refine ⟨14208607021033531847498245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75779237445512169853323973 14208607021033531847498245)
                ·
                  refine ⟨2664113816443787221405921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14208607021033531847498245 2664113816443787221405921)
                  ·
                    refine ⟨1998085362332840416054441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2664113816443787221405921 1998085362332840416054441)
                    ·
                      refine ⟨1498564021749630312040831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1998085362332840416054441 1498564021749630312040831)
                      ·
                        rfl

theorem cell23_2918443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 2, 2].length) (baseStart_2918443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918443 prefixEnd_2918443 := by exact prefixLift 2918443
  have htrace : WordTrace (prefixWord ++ tailWord_2918443) baseStart_2918443 baseEnd_2918443 := by
    simpa [prefixWord, tailWord_2918443, baseEnd_2918443] using wordTrace_append hprefix tailTrace_2918443
  have hstable : (prefixWord ++ tailWord_2918443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918443).length < 2 ^ (prefixWord ++ tailWord_2918443).sum := by decide
  have hdescent : baseEnd_2918443 < baseStart_2918443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918469 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 8]
def baseStart_2918469 : Nat := 118140960795 + 2918469 * 2 ^ 59
def prefixEnd_2918469 : Nat := 4983230072969 + 3 ^ 40 * 2918469 * 2
def baseEnd_2918469 : Nat := 1498577372246647210315711

theorem tailTrace_2918469 : CollatzResearch.WordTrace tailWord_2918469 prefixEnd_2918469 1498577372246647210315711 := by
  unfold tailWord_2918469
  simp only [CollatzResearch.WordTrace]
  refine ⟨106445309263892722667886461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70963539509261815111924307 106445309263892722667886461)
  ·
    refine ⟨39916990973959771000457423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106445309263892722667886461 39916990973959771000457423)
    ·
      refine ⟨59875486460939656500686135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39916990973959771000457423 59875486460939656500686135)
      ·
        refine ⟨89813229691409484751029203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59875486460939656500686135 89813229691409484751029203)
        ·
          refine ⟨134719844537114227126543805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89813229691409484751029203 134719844537114227126543805)
          ·
            refine ⟨50519941701417835172453927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134719844537114227126543805 50519941701417835172453927)
            ·
              refine ⟨75779912552126752758680891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50519941701417835172453927 75779912552126752758680891)
              ·
                refine ⟨113669868828190129138021337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75779912552126752758680891 113669868828190129138021337)
                ·
                  refine ⟨85252401621142596853516003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113669868828190129138021337 85252401621142596853516003)
                  ·
                    refine ⟨127878602431713895280274005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85252401621142596853516003 127878602431713895280274005)
                    ·
                      refine ⟨1498577372246647210315711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 127878602431713895280274005 1498577372246647210315711)
                      ·
                        rfl

theorem cell23_2918469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_2918469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918469 prefixEnd_2918469 := by exact prefixLift 2918469
  have htrace : WordTrace (prefixWord ++ tailWord_2918469) baseStart_2918469 baseEnd_2918469 := by
    simpa [prefixWord, tailWord_2918469, baseEnd_2918469] using wordTrace_append hprefix tailTrace_2918469
  have hstable : (prefixWord ++ tailWord_2918469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918469).length < 2 ^ (prefixWord ++ tailWord_2918469).sum := by decide
  have hdescent : baseEnd_2918469 < baseStart_2918469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918476 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 1, 5, 3]
def baseStart_2918476 : Nat := 118140960795 + 2918476 * 2 ^ 59
def prefixEnd_2918476 : Nat := 4983230072969 + 3 ^ 40 * 2918476 * 2
def baseEnd_2918476 : Nat := 1498580966611228682928179

theorem tailTrace_2918476 : CollatzResearch.WordTrace tailWord_2918476 prefixEnd_2918476 1498580966611228682928179 := by
  unfold tailWord_2918476
  simp only [CollatzResearch.WordTrace]
  refine ⟨53222782287433681431695641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70963709716578241908927521 53222782287433681431695641)
  ·
    refine ⟨39917086715575261073771731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53222782287433681431695641 39917086715575261073771731)
    ·
      refine ⟨59875630073362891610657597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39917086715575261073771731 59875630073362891610657597)
      ·
        refine ⟨22453361277511084353996599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59875630073362891610657597 22453361277511084353996599)
        ·
          refine ⟨33680041916266626530994899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22453361277511084353996599 33680041916266626530994899)
          ·
            refine ⟨50520062874399939796492349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33680041916266626530994899 50520062874399939796492349)
            ·
              refine ⟨18945023577899977423684631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50520062874399939796492349 18945023577899977423684631)
              ·
                refine ⟨28417535366849966135526947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18945023577899977423684631 28417535366849966135526947)
                ·
                  refine ⟨42626303050274949203290421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28417535366849966135526947 42626303050274949203290421)
                  ·
                    refine ⟨3996215910963276487808477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42626303050274949203290421 3996215910963276487808477)
                    ·
                      refine ⟨1498580966611228682928179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3996215910963276487808477 1498580966611228682928179)
                      ·
                        rfl

theorem cell23_2918476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_2918476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918476 prefixEnd_2918476 := by exact prefixLift 2918476
  have htrace : WordTrace (prefixWord ++ tailWord_2918476) baseStart_2918476 baseEnd_2918476 := by
    simpa [prefixWord, tailWord_2918476, baseEnd_2918476] using wordTrace_append hprefix tailTrace_2918476
  have hstable : (prefixWord ++ tailWord_2918476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918476).length < 2 ^ (prefixWord ++ tailWord_2918476).sum := by decide
  have hdescent : baseEnd_2918476 < baseStart_2918476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918477 : List Nat := [1, 6, 1, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_2918477 : Nat := 118140960795 + 2918477 * 2 ^ 59
def prefixEnd_2918477 : Nat := 4983230072969 + 3 ^ 40 * 2918477 * 2
def baseEnd_2918477 : Nat := 1498581480091883179015675

theorem tailTrace_2918477 : CollatzResearch.WordTrace tailWord_2918477 prefixEnd_2918477 1498581480091883179015675 := by
  unfold tailWord_2918477
  simp only [CollatzResearch.WordTrace]
  refine ⟨106445601047863740034177685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70963734031909160022785123 106445601047863740034177685)
  ·
    refine ⟨4989637549118612814102079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106445601047863740034177685 4989637549118612814102079)
    ·
      refine ⟨7484456323677919221153119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4989637549118612814102079 7484456323677919221153119)
      ·
        refine ⟨11226684485516878831729679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7484456323677919221153119 11226684485516878831729679)
        ·
          refine ⟨16840026728275318247594519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11226684485516878831729679 16840026728275318247594519)
          ·
            refine ⟨25260040092412977371391779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16840026728275318247594519 25260040092412977371391779)
            ·
              refine ⟨37890060138619466057087669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25260040092412977371391779 37890060138619466057087669)
              ·
                refine ⟨3552193137995574942851969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37890060138619466057087669 3552193137995574942851969)
                ·
                  refine ⟨2664144853496681207138977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3552193137995574942851969 2664144853496681207138977)
                  ·
                    refine ⟨1998108640122510905354233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2664144853496681207138977 1998108640122510905354233)
                    ·
                      refine ⟨1498581480091883179015675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1998108640122510905354233 1498581480091883179015675)
                      ·
                        rfl

theorem cell23_2918477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_2918477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918477 prefixEnd_2918477 := by exact prefixLift 2918477
  have htrace : WordTrace (prefixWord ++ tailWord_2918477) baseStart_2918477 baseEnd_2918477 := by
    simpa [prefixWord, tailWord_2918477, baseEnd_2918477] using wordTrace_append hprefix tailTrace_2918477
  have hstable : (prefixWord ++ tailWord_2918477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918477).length < 2 ^ (prefixWord ++ tailWord_2918477).sum := by decide
  have hdescent : baseEnd_2918477 < baseStart_2918477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918479 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 3, 7]
def baseStart_2918479 : Nat := 118140960795 + 2918479 * 2 ^ 59
def prefixEnd_2918479 : Nat := 4983230072969 + 3 ^ 40 * 2918479 * 2
def baseEnd_2918479 : Nat := 499527502351064057063555

theorem tailTrace_2918479 : CollatzResearch.WordTrace tailWord_2918479 prefixEnd_2918479 499527502351064057063555 := by
  unfold tailWord_2918479
  simp only [CollatzResearch.WordTrace]
  refine ⟨106445673993856494375750491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70963782662570996250500327 106445673993856494375750491)
  ·
    refine ⟨159668510990784741563625737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106445673993856494375750491 159668510990784741563625737)
    ·
      refine ⟨119751383243088556172719303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159668510990784741563625737 119751383243088556172719303)
      ·
        refine ⟨179627074864632834259078955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119751383243088556172719303 179627074864632834259078955)
        ·
          refine ⟨269440612296949251388618433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179627074864632834259078955 269440612296949251388618433)
          ·
            refine ⟨202080459222711938541463825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269440612296949251388618433 202080459222711938541463825)
            ·
              refine ⟨151560344417033953906097869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202080459222711938541463825 151560344417033953906097869)
              ·
                refine ⟨56835129156387732714786701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151560344417033953906097869 56835129156387732714786701)
                ·
                  refine ⟨21313173433645399768045013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56835129156387732714786701 21313173433645399768045013)
                  ·
                    refine ⟨499527502351064057063555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21313173433645399768045013 499527502351064057063555)
                    ·
                      rfl

theorem cell23_2918479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 7].length) (baseStart_2918479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918479 prefixEnd_2918479 := by exact prefixLift 2918479
  have htrace : WordTrace (prefixWord ++ tailWord_2918479) baseStart_2918479 baseEnd_2918479 := by
    simpa [prefixWord, tailWord_2918479, baseEnd_2918479] using wordTrace_append hprefix tailTrace_2918479
  have hstable : (prefixWord ++ tailWord_2918479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918479).length < 2 ^ (prefixWord ++ tailWord_2918479).sum := by decide
  have hdescent : baseEnd_2918479 < baseStart_2918479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918496 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 1, 7]
def baseStart_2918496 : Nat := 118140960795 + 2918496 * 2 ^ 59
def prefixEnd_2918496 : Nat := 4983230072969 + 3 ^ 40 * 2918496 * 2
def baseEnd_2918496 : Nat := 499530412074772868226029

theorem tailTrace_2918496 : CollatzResearch.WordTrace tailWord_2918496 prefixEnd_2918496 499530412074772868226029 := by
  unfold tailWord_2918496
  simp only [CollatzResearch.WordTrace]
  refine ⟨53223147017397453139559671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70964196023196604186079561 53223147017397453139559671)
  ·
    refine ⟨79834720526096179709339507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53223147017397453139559671 79834720526096179709339507)
    ·
      refine ⟨119752080789144269564009261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79834720526096179709339507 119752080789144269564009261)
      ·
        refine ⟨44907030295929101086503473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119752080789144269564009261 44907030295929101086503473)
        ·
          refine ⟨33680272721946825814877605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44907030295929101086503473 33680272721946825814877605)
          ·
            refine ⟨6315051135365029840289551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33680272721946825814877605 6315051135365029840289551)
            ·
              refine ⟨9472576703047544760434327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6315051135365029840289551 9472576703047544760434327)
              ·
                refine ⟨14208865054571317140651491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9472576703047544760434327 14208865054571317140651491)
                ·
                  refine ⟨21313297581856975710977237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14208865054571317140651491 21313297581856975710977237)
                  ·
                    refine ⟨499530412074772868226029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21313297581856975710977237 499530412074772868226029)
                    ·
                      rfl

theorem cell23_2918496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 1, 7].length) (baseStart_2918496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918496 prefixEnd_2918496 := by exact prefixLift 2918496
  have htrace : WordTrace (prefixWord ++ tailWord_2918496) baseStart_2918496 baseEnd_2918496 := by
    simpa [prefixWord, tailWord_2918496, baseEnd_2918496] using wordTrace_append hprefix tailTrace_2918496
  have hstable : (prefixWord ++ tailWord_2918496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918496).length < 2 ^ (prefixWord ++ tailWord_2918496).sum := by decide
  have hdescent : baseEnd_2918496 < baseStart_2918496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918556 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 10]
def baseStart_2918556 : Nat := 118140960795 + 2918556 * 2 ^ 59
def prefixEnd_2918556 : Nat := 4983230072969 + 3 ^ 40 * 2918556 * 2
def baseEnd_2918556 : Nat := 166513560562620929991979

theorem tailTrace_2918556 : CollatzResearch.WordTrace tailWord_2918556 prefixEnd_2918556 166513560562620929991979 := by
  unfold tailWord_2918556
  simp only [CollatzResearch.WordTrace]
  refine ⟨53224241207288768263151761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70965654943051691017535681 53224241207288768263151761)
  ·
    refine ⟨39918180905466576197363821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53224241207288768263151761 39918180905466576197363821)
    ·
      refine ⟨14969317839549966074011433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39918180905466576197363821 14969317839549966074011433)
      ·
        refine ⟨11226988379662474555508575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14969317839549966074011433 11226988379662474555508575)
        ·
          refine ⟨16840482569493711833262863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11226988379662474555508575 16840482569493711833262863)
          ·
            refine ⟨25260723854240567749894295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16840482569493711833262863 25260723854240567749894295)
            ·
              refine ⟨37891085781360851624841443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25260723854240567749894295 37891085781360851624841443)
              ·
                refine ⟨56836628672041277437262165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37891085781360851624841443 56836628672041277437262165)
                ·
                  refine ⟨166513560562620929991979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 56836628672041277437262165 166513560562620929991979)
                  ·
                    rfl

theorem cell23_2918556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 10].length) (baseStart_2918556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918556 prefixEnd_2918556 := by exact prefixLift 2918556
  have htrace : WordTrace (prefixWord ++ tailWord_2918556) baseStart_2918556 baseEnd_2918556 := by
    simpa [prefixWord, tailWord_2918556, baseEnd_2918556] using wordTrace_append hprefix tailTrace_2918556
  have hstable : (prefixWord ++ tailWord_2918556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918556).length < 2 ^ (prefixWord ++ tailWord_2918556).sum := by decide
  have hdescent : baseEnd_2918556 < baseStart_2918556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918573 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 8]
def baseStart_2918573 : Nat := 118140960795 + 2918573 * 2 ^ 59
def prefixEnd_2918573 : Nat := 4983230072969 + 3 ^ 40 * 2918573 * 2
def baseEnd_2918573 : Nat := 166514530470523867046137

theorem tailTrace_2918573 : CollatzResearch.WordTrace tailWord_2918573 prefixEnd_2918573 166514530470523867046137 := by
  unfold tailWord_2918573
  simp only [CollatzResearch.WordTrace]
  refine ⟨106449102455515948429672373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70966068303677298953114915 106449102455515948429672373)
  ·
    refine ⟨9979603355204620165281785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106449102455515948429672373 9979603355204620165281785)
    ·
      refine ⟨7484702516403465123961339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9979603355204620165281785 7484702516403465123961339)
      ·
        refine ⟨11227053774605197685942009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7484702516403465123961339 11227053774605197685942009)
        ·
          refine ⟨8420290330953898264456507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11227053774605197685942009 8420290330953898264456507)
          ·
            refine ⟨12630435496430847396684761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8420290330953898264456507 12630435496430847396684761)
            ·
              refine ⟨9472826622323135547513571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12630435496430847396684761 9472826622323135547513571)
              ·
                refine ⟨14209239933484703321270357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9472826622323135547513571 14209239933484703321270357)
                ·
                  refine ⟨166514530470523867046137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14209239933484703321270357 166514530470523867046137)
                  ·
                    rfl

theorem cell23_2918573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_2918573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918573 prefixEnd_2918573 := by exact prefixLift 2918573
  have htrace : WordTrace (prefixWord ++ tailWord_2918573) baseStart_2918573 baseEnd_2918573 := by
    simpa [prefixWord, tailWord_2918573, baseEnd_2918573] using wordTrace_append hprefix tailTrace_2918573
  have hstable : (prefixWord ++ tailWord_2918573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918573).length < 2 ^ (prefixWord ++ tailWord_2918573).sum := by decide
  have hdescent : baseEnd_2918573 < baseStart_2918573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918577 : List Nat := [1, 2, 2, 5, 2, 2, 1, 1, 3, 4]
def baseStart_2918577 : Nat := 118140960795 + 2918577 * 2 ^ 59
def prefixEnd_2918577 : Nat := 4983230072969 + 3 ^ 40 * 2918577 * 2
def baseEnd_2918577 : Nat := 499544276052444262588405

theorem tailTrace_2918577 : CollatzResearch.WordTrace tailWord_2918577 prefixEnd_2918577 499544276052444262588405 := by
  unfold tailWord_2918577
  simp only [CollatzResearch.WordTrace]
  refine ⟨106449248347501457112817985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70966165565000971408545323 106449248347501457112817985)
  ·
    refine ⟨79836936260626092834613489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106449248347501457112817985 79836936260626092834613489)
    ·
      refine ⟨59877702195469569625960117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79836936260626092834613489 59877702195469569625960117)
      ·
        refine ⟨5613534580825272152433761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59877702195469569625960117 5613534580825272152433761)
        ·
          refine ⟨4210150935618954114325321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5613534580825272152433761 4210150935618954114325321)
          ·
            refine ⟨3157613201714215585743991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4210150935618954114325321 3157613201714215585743991)
            ·
              refine ⟨4736419802571323378615987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3157613201714215585743991 4736419802571323378615987)
              ·
                refine ⟨7104629703856985067923981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4736419802571323378615987 7104629703856985067923981)
                ·
                  refine ⟨2664236138946369400471493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7104629703856985067923981 2664236138946369400471493)
                  ·
                    refine ⟨499544276052444262588405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2664236138946369400471493 499544276052444262588405)
                    ·
                      rfl

theorem cell23_2918577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_2918577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918577 prefixEnd_2918577 := by exact prefixLift 2918577
  have htrace : WordTrace (prefixWord ++ tailWord_2918577) baseStart_2918577 baseEnd_2918577 := by
    simpa [prefixWord, tailWord_2918577, baseEnd_2918577] using wordTrace_append hprefix tailTrace_2918577
  have hstable : (prefixWord ++ tailWord_2918577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918577).length < 2 ^ (prefixWord ++ tailWord_2918577).sum := by decide
  have hdescent : baseEnd_2918577 < baseStart_2918577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918590 : List Nat := [4, 2, 1, 1, 4, 1, 1, 3, 6]
def baseStart_2918590 : Nat := 118140960795 + 2918590 * 2 ^ 59
def prefixEnd_2918590 : Nat := 4983230072969 + 3 ^ 40 * 2918590 * 2
def baseEnd_2918590 : Nat := 166515500378426804100295

theorem tailTrace_2918590 : CollatzResearch.WordTrace tailWord_2918590 prefixEnd_2918590 166515500378426804100295 := by
  unfold tailWord_2918590
  simp only [CollatzResearch.WordTrace]
  refine ⟨13306215312056795041630153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70966481664302906888694149 13306215312056795041630153)
  ·
    refine ⟨9979661484042596281222615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13306215312056795041630153 9979661484042596281222615)
    ·
      refine ⟨14969492226063894421833923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9979661484042596281222615 14969492226063894421833923)
      ·
        refine ⟨22454238339095841632750885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14969492226063894421833923 22454238339095841632750885)
        ·
          refine ⟨4210169688580470306140791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22454238339095841632750885 4210169688580470306140791)
          ·
            refine ⟨6315254532870705459211187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210169688580470306140791 6315254532870705459211187)
            ·
              refine ⟨9472881799306058188816781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6315254532870705459211187 9472881799306058188816781)
              ·
                refine ⟨3552330674739771820806293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9472881799306058188816781 3552330674739771820806293)
                ·
                  refine ⟨166515500378426804100295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3552330674739771820806293 166515500378426804100295)
                  ·
                    rfl

theorem cell23_2918590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_2918590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918590 prefixEnd_2918590 := by exact prefixLift 2918590
  have htrace : WordTrace (prefixWord ++ tailWord_2918590) baseStart_2918590 baseEnd_2918590 := by
    simpa [prefixWord, tailWord_2918590, baseEnd_2918590] using wordTrace_append hprefix tailTrace_2918590
  have hstable : (prefixWord ++ tailWord_2918590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918590).length < 2 ^ (prefixWord ++ tailWord_2918590).sum := by decide
  have hdescent : baseEnd_2918590 < baseStart_2918590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918640 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 7, 2, 2]
def baseStart_2918640 : Nat := 118140960795 + 2918640 * 2 ^ 59
def prefixEnd_2918640 : Nat := 4983230072969 + 3 ^ 40 * 2918640 * 2
def baseEnd_2918640 : Nat := 1498665177438566041277425

theorem tailTrace_2918640 : CollatzResearch.WordTrace tailWord_2918640 prefixEnd_2918640 1498665177438566041277425 := by
  unfold tailWord_2918640
  simp only [CollatzResearch.WordTrace]
  refine ⟨53225773073136609436180687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70967697430848812581574249 53225773073136609436180687)
  ·
    refine ⟨79838659609704914154271031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53225773073136609436180687 79838659609704914154271031)
    ·
      refine ⟨119757989414557371231406547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79838659609704914154271031 119757989414557371231406547)
      ·
        refine ⟨179636984121836056847109821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119757989414557371231406547 179636984121836056847109821)
        ·
          refine ⟨67363869045688521317666183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179636984121836056847109821 67363869045688521317666183)
          ·
            refine ⟨101045803568532781976499275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67363869045688521317666183 101045803568532781976499275)
            ·
              refine ⟨151568705352799172964748913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101045803568532781976499275 151568705352799172964748913)
              ·
                refine ⟨113676529014599379723561685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151568705352799172964748913 113676529014599379723561685)
                ·
                  refine ⟨2664293648779672962270977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 113676529014599379723561685 2664293648779672962270977)
                  ·
                    refine ⟨1998220236584754721703233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2664293648779672962270977 1998220236584754721703233)
                    ·
                      refine ⟨1498665177438566041277425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1998220236584754721703233 1498665177438566041277425)
                      ·
                        rfl

theorem cell23_2918640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 7, 2, 2].length) (baseStart_2918640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918640 prefixEnd_2918640 := by exact prefixLift 2918640
  have htrace : WordTrace (prefixWord ++ tailWord_2918640) baseStart_2918640 baseEnd_2918640 := by
    simpa [prefixWord, tailWord_2918640, baseEnd_2918640] using wordTrace_append hprefix tailTrace_2918640
  have hstable : (prefixWord ++ tailWord_2918640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918640).length < 2 ^ (prefixWord ++ tailWord_2918640).sum := by decide
  have hdescent : baseEnd_2918640 < baseStart_2918640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918643 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 3]
def baseStart_2918643 : Nat := 118140960795 + 2918643 * 2 ^ 59
def prefixEnd_2918643 : Nat := 4983230072969 + 3 ^ 40 * 2918643 * 2
def baseEnd_2918643 : Nat := 1498666717880529529539911

theorem tailTrace_2918643 : CollatzResearch.WordTrace tailWord_2918643 prefixEnd_2918643 1498666717880529529539911 := by
  unfold tailWord_2918643
  simp only [CollatzResearch.WordTrace]
  refine ⟨106451655565262350384720583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70967770376841566923147055 106451655565262350384720583)
  ·
    refine ⟨159677483347893525577080875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106451655565262350384720583 159677483347893525577080875)
    ·
      refine ⟨239516225021840288365621313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159677483347893525577080875 239516225021840288365621313)
      ·
        refine ⟨179637168766380216274215985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239516225021840288365621313 179637168766380216274215985)
        ·
          refine ⟨134727876574785162205661989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179637168766380216274215985 134727876574785162205661989)
          ·
            refine ⟨25261476857772217913561623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134727876574785162205661989 25261476857772217913561623)
            ·
              refine ⟨37892215286658326870342435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25261476857772217913561623 37892215286658326870342435)
              ·
                refine ⟨56838322929987490305513653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37892215286658326870342435 56838322929987490305513653)
                ·
                  refine ⟨5328592774686327216141905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56838322929987490305513653 5328592774686327216141905)
                  ·
                    refine ⟨3996444581014745412106429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5328592774686327216141905 3996444581014745412106429)
                    ·
                      refine ⟨1498666717880529529539911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3996444581014745412106429 1498666717880529529539911)
                      ·
                        rfl

theorem cell23_2918643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 3].length) (baseStart_2918643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918643 prefixEnd_2918643 := by exact prefixLift 2918643
  have htrace : WordTrace (prefixWord ++ tailWord_2918643) baseStart_2918643 baseEnd_2918643 := by
    simpa [prefixWord, tailWord_2918643, baseEnd_2918643] using wordTrace_append hprefix tailTrace_2918643
  have hstable : (prefixWord ++ tailWord_2918643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918643).length < 2 ^ (prefixWord ++ tailWord_2918643).sum := by decide
  have hdescent : baseEnd_2918643 < baseStart_2918643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918650 : List Nat := [3, 1, 1, 1, 1, 5, 2, 3, 2, 4]
def baseStart_2918650 : Nat := 118140960795 + 2918650 * 2 ^ 59
def prefixEnd_2918650 : Nat := 4983230072969 + 3 ^ 40 * 2918650 * 2
def baseEnd_2918650 : Nat := 499556770748370334050793

theorem tailTrace_2918650 : CollatzResearch.WordTrace tailWord_2918650 prefixEnd_2918650 499556770748370334050793 := by
  unfold tailWord_2918650
  simp only [CollatzResearch.WordTrace]
  refine ⟨26612977719059247645056351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70967940584157993720150269 26612977719059247645056351)
  ·
    refine ⟨39919466578588871467584527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26612977719059247645056351 39919466578588871467584527)
    ·
      refine ⟨59879199867883307201376791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39919466578588871467584527 59879199867883307201376791)
      ·
        refine ⟨89818799801824960802065187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59879199867883307201376791 89818799801824960802065187)
        ·
          refine ⟨134728199702737441203097781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89818799801824960802065187 134728199702737441203097781)
          ·
            refine ⟨12630768722131635112790417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134728199702737441203097781 12630768722131635112790417)
            ·
              refine ⟨9473076541598726334592813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12630768722131635112790417 9473076541598726334592813)
              ·
                refine ⟨3552403703099522375472305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9473076541598726334592813 3552403703099522375472305)
                ·
                  refine ⟨2664302777324641781604229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3552403703099522375472305 2664302777324641781604229)
                  ·
                    refine ⟨499556770748370334050793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2664302777324641781604229 499556770748370334050793)
                    ·
                      rfl

theorem cell23_2918650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_2918650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918650 prefixEnd_2918650 := by exact prefixLift 2918650
  have htrace : WordTrace (prefixWord ++ tailWord_2918650) baseStart_2918650 baseEnd_2918650 := by
    simpa [prefixWord, tailWord_2918650, baseEnd_2918650] using wordTrace_append hprefix tailTrace_2918650
  have hstable : (prefixWord ++ tailWord_2918650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918650).length < 2 ^ (prefixWord ++ tailWord_2918650).sum := by decide
  have hdescent : baseEnd_2918650 < baseStart_2918650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918657 : List Nat := [1, 2, 4, 1, 1, 2, 3, 2, 3, 2, 2]
def baseStart_2918657 : Nat := 118140960795 + 2918657 * 2 ^ 59
def prefixEnd_2918657 : Nat := 4983230072969 + 3 ^ 40 * 2918657 * 2
def baseEnd_2918657 : Nat := 1498673906609692474764847

theorem tailTrace_2918657 : CollatzResearch.WordTrace tailWord_2918657 prefixEnd_2918657 1498673906609692474764847 := by
  unfold tailWord_2918657
  simp only [CollatzResearch.WordTrace]
  refine ⟨106452166187211630775730225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70968110791474420517153483 106452166187211630775730225)
  ·
    refine ⟨79839124640408723081797669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106452166187211630775730225 79839124640408723081797669)
    ·
      refine ⟨14969835870076635577837063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79839124640408723081797669 14969835870076635577837063)
      ·
        refine ⟨22454753805114953366755595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14969835870076635577837063 22454753805114953366755595)
        ·
          refine ⟨33682130707672430050133393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22454753805114953366755595 33682130707672430050133393)
          ·
            refine ⟨25261598030754322537600045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33682130707672430050133393 25261598030754322537600045)
            ·
              refine ⟨9473099261532870951600017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25261598030754322537600045 9473099261532870951600017)
              ·
                refine ⟨7104824446149653213700013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9473099261532870951600017 7104824446149653213700013)
                ·
                  refine ⟨2664309167306119955137505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7104824446149653213700013 2664309167306119955137505)
                  ·
                    refine ⟨1998231875479589966353129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2664309167306119955137505 1998231875479589966353129)
                    ·
                      refine ⟨1498673906609692474764847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1998231875479589966353129 1498673906609692474764847)
                      ·
                        rfl

theorem cell23_2918657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_2918657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918657 prefixEnd_2918657 := by exact prefixLift 2918657
  have htrace : WordTrace (prefixWord ++ tailWord_2918657) baseStart_2918657 baseEnd_2918657 := by
    simpa [prefixWord, tailWord_2918657, baseEnd_2918657] using wordTrace_append hprefix tailTrace_2918657
  have hstable : (prefixWord ++ tailWord_2918657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918657).length < 2 ^ (prefixWord ++ tailWord_2918657).sum := by decide
  have hdescent : baseEnd_2918657 < baseStart_2918657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918677 : List Nat := [1, 3, 2, 1, 2, 1, 6, 1, 1, 2, 3]
def baseStart_2918677 : Nat := 118140960795 + 2918677 * 2 ^ 59
def prefixEnd_2918677 : Nat := 4983230072969 + 3 ^ 40 * 2918677 * 2
def baseEnd_2918677 : Nat := 1498684176222782396514755

theorem tailTrace_2918677 : CollatzResearch.WordTrace tailWord_2918677 prefixEnd_2918677 1498684176222782396514755 := by
  unfold tailWord_2918677
  simp only [CollatzResearch.WordTrace]
  refine ⟨106452895647139174191458285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70968597098092782794305523 106452895647139174191458285)
  ·
    refine ⟨39919835867677190321796857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106452895647139174191458285 39919835867677190321796857)
    ·
      refine ⟨29939876900757892741347643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39919835867677190321796857 29939876900757892741347643)
      ·
        refine ⟨44909815351136839112021465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29939876900757892741347643 44909815351136839112021465)
        ·
          refine ⟨33682361513352629334016099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44909815351136839112021465 33682361513352629334016099)
          ·
            refine ⟨50523542270028944001024149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33682361513352629334016099 50523542270028944001024149)
            ·
              refine ⟨2368291043907606750048007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50523542270028944001024149 2368291043907606750048007)
              ·
                refine ⟨3552436565861410125072011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2368291043907606750048007 3552436565861410125072011)
                ·
                  refine ⟨5328654848792115187608017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3552436565861410125072011 5328654848792115187608017)
                  ·
                    refine ⟨3996491136594086390706013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5328654848792115187608017 3996491136594086390706013)
                    ·
                      refine ⟨1498684176222782396514755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3996491136594086390706013 1498684176222782396514755)
                      ·
                        rfl

theorem cell23_2918677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_2918677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918677 prefixEnd_2918677 := by exact prefixLift 2918677
  have htrace : WordTrace (prefixWord ++ tailWord_2918677) baseStart_2918677 baseEnd_2918677 := by
    simpa [prefixWord, tailWord_2918677, baseEnd_2918677] using wordTrace_append hprefix tailTrace_2918677
  have hstable : (prefixWord ++ tailWord_2918677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918677).length < 2 ^ (prefixWord ++ tailWord_2918677).sum := by decide
  have hdescent : baseEnd_2918677 < baseStart_2918677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918700 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 5, 3, 2]
def baseStart_2918700 : Nat := 118140960795 + 2918700 * 2 ^ 59
def prefixEnd_2918700 : Nat := 4983230072969 + 3 ^ 40 * 2918700 * 2
def baseEnd_2918700 : Nat := 1498695986277835806527149

theorem tailTrace_2918700 : CollatzResearch.WordTrace tailWord_2918700 prefixEnd_2918700 1498695986277835806527149 := by
  unfold tailWord_2918700
  simp only [CollatzResearch.WordTrace]
  refine ⟨53226867263027924559772777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70969156350703899413030369 53226867263027924559772777)
  ·
    refine ⟨39920150447270943419829583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53226867263027924559772777 39920150447270943419829583)
    ·
      refine ⟨59880225670906415129744375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39920150447270943419829583 59880225670906415129744375)
      ·
        refine ⟨89820338506359622694616563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59880225670906415129744375 89820338506359622694616563)
        ·
          refine ⟨134730507759539434041924845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89820338506359622694616563 134730507759539434041924845)
          ·
            refine ⟨50523940409827287765721817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134730507759539434041924845 50523940409827287765721817)
            ·
              refine ⟨37892955307370465824291363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50523940409827287765721817 37892955307370465824291363)
              ·
                refine ⟨56839432961055698736437045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37892955307370465824291363 56839432961055698736437045)
                ·
                  refine ⟨5328696840098971756540973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56839432961055698736437045 5328696840098971756540973)
                  ·
                    refine ⟨1998261315037114408702865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5328696840098971756540973 1998261315037114408702865)
                    ·
                      refine ⟨1498695986277835806527149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1998261315037114408702865 1498695986277835806527149)
                      ·
                        rfl

theorem cell23_2918700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 3, 2].length) (baseStart_2918700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918700 prefixEnd_2918700 := by exact prefixLift 2918700
  have htrace : WordTrace (prefixWord ++ tailWord_2918700) baseStart_2918700 baseEnd_2918700 := by
    simpa [prefixWord, tailWord_2918700, baseEnd_2918700] using wordTrace_append hprefix tailTrace_2918700
  have hstable : (prefixWord ++ tailWord_2918700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918700).length < 2 ^ (prefixWord ++ tailWord_2918700).sum := by decide
  have hdescent : baseEnd_2918700 < baseStart_2918700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918701 : List Nat := [1, 5, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_2918701 : Nat := 118140960795 + 2918701 * 2 ^ 59
def prefixEnd_2918701 : Nat := 4983230072969 + 3 ^ 40 * 2918701 * 2
def baseEnd_2918701 : Nat := 499565499919496767538215

theorem tailTrace_2918701 : CollatzResearch.WordTrace tailWord_2918701 prefixEnd_2918701 499565499919496767538215 := by
  unfold tailWord_2918701
  simp only [CollatzResearch.WordTrace]
  refine ⟨106453770999052226290331957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70969180666034817526887971 106453770999052226290331957)
  ·
    refine ⟨9980041031161146214718621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106453770999052226290331957 9980041031161146214718621)
    ·
      refine ⟨3742515386685429830519483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9980041031161146214718621 3742515386685429830519483)
      ·
        refine ⟨5613773080028144745779225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3742515386685429830519483 5613773080028144745779225)
        ·
          refine ⟨4210329810021108559334419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5613773080028144745779225 4210329810021108559334419)
          ·
            refine ⟨6315494715031662839001629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210329810021108559334419 6315494715031662839001629)
            ·
              refine ⟨2368310518136873564625611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6315494715031662839001629 2368310518136873564625611)
              ·
                refine ⟨3552465777205310346938417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2368310518136873564625611 3552465777205310346938417)
                ·
                  refine ⟨2664349332903982760203813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3552465777205310346938417 2664349332903982760203813)
                  ·
                    refine ⟨499565499919496767538215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2664349332903982760203813 499565499919496767538215)
                    ·
                      rfl

theorem cell23_2918701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_2918701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918701 prefixEnd_2918701 := by exact prefixLift 2918701
  have htrace : WordTrace (prefixWord ++ tailWord_2918701) baseStart_2918701 baseEnd_2918701 := by
    simpa [prefixWord, tailWord_2918701, baseEnd_2918701] using wordTrace_append hprefix tailTrace_2918701
  have hstable : (prefixWord ++ tailWord_2918701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918701).length < 2 ^ (prefixWord ++ tailWord_2918701).sum := by decide
  have hdescent : baseEnd_2918701 < baseStart_2918701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918783 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 6, 5]
def baseStart_2918783 : Nat := 118140960795 + 2918783 * 2 ^ 59
def prefixEnd_2918783 : Nat := 4983230072969 + 3 ^ 40 * 2918783 * 2
def baseEnd_2918783 : Nat := 499579535057386327263089

theorem tailTrace_2918783 : CollatzResearch.WordTrace tailWord_2918783 prefixEnd_2918783 499579535057386327263089 := by
  unfold tailWord_2918783
  simp only [CollatzResearch.WordTrace]
  refine ⟨106456761784755154294817003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70971174523170102863211335 106456761784755154294817003)
  ·
    refine ⟨159685142677132731442225505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106456761784755154294817003 159685142677132731442225505)
    ·
      refine ⟨119763857007849548581669129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159685142677132731442225505 119763857007849548581669129)
      ·
        refine ⟨89822892755887161436251847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119763857007849548581669129 89822892755887161436251847)
        ·
          refine ⟨134734339133830742154377771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89822892755887161436251847 134734339133830742154377771)
          ·
            refine ⟨202101508700746113231566657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134734339133830742154377771 202101508700746113231566657)
            ·
              refine ⟨151576131525559584923674993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202101508700746113231566657 151576131525559584923674993)
              ·
                refine ⟨113682098644169688692756245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151576131525559584923674993 113682098644169688692756245)
                ·
                  refine ⟨5328848373945454157472949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 113682098644169688692756245 5328848373945454157472949)
                  ·
                    refine ⟨499579535057386327263089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5328848373945454157472949 499579535057386327263089)
                    ·
                      rfl

theorem cell23_2918783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 5].length) (baseStart_2918783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918783 prefixEnd_2918783 := by exact prefixLift 2918783
  have htrace : WordTrace (prefixWord ++ tailWord_2918783) baseStart_2918783 baseEnd_2918783 := by
    simpa [prefixWord, tailWord_2918783, baseEnd_2918783] using wordTrace_append hprefix tailTrace_2918783
  have hstable : (prefixWord ++ tailWord_2918783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918783).length < 2 ^ (prefixWord ++ tailWord_2918783).sum := by decide
  have hdescent : baseEnd_2918783 < baseStart_2918783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918804 : List Nat := [2, 4, 2, 1, 3, 1, 1, 4, 5]
def baseStart_2918804 : Nat := 118140960795 + 2918804 * 2 ^ 59
def prefixEnd_2918804 : Nat := 4983230072969 + 3 ^ 40 * 2918804 * 2
def baseEnd_2918804 : Nat := 166527709807322599958519

theorem tailTrace_2918804 : CollatzResearch.WordTrace tailWord_2918804 prefixEnd_2918804 166527709807322599958519 := by
  unfold tailWord_2918804
  simp only [CollatzResearch.WordTrace]
  refine ⟨53228763858839537440665733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70971685145119383254220977 53228763858839537440665733)
  ·
    refine ⟨9980393223532413270124825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53228763858839537440665733 9980393223532413270124825)
    ·
      refine ⟨7485294917649309952593619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9980393223532413270124825 7485294917649309952593619)
      ·
        refine ⟨11227942376473964928890429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7485294917649309952593619 11227942376473964928890429)
        ·
          refine ⟨4210478391177736848333911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11227942376473964928890429 4210478391177736848333911)
          ·
            refine ⟨6315717586766605272500867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210478391177736848333911 6315717586766605272500867)
            ·
              refine ⟨9473576380149907908751301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6315717586766605272500867 9473576380149907908751301)
              ·
                refine ⟨1776295571278107732890869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9473576380149907908751301 1776295571278107732890869)
                ·
                  refine ⟨166527709807322599958519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1776295571278107732890869 166527709807322599958519)
                  ·
                    rfl

theorem cell23_2918804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_2918804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918804 prefixEnd_2918804 := by exact prefixLift 2918804
  have htrace : WordTrace (prefixWord ++ tailWord_2918804) baseStart_2918804 baseEnd_2918804 := by
    simpa [prefixWord, tailWord_2918804, baseEnd_2918804] using wordTrace_append hprefix tailTrace_2918804
  have hstable : (prefixWord ++ tailWord_2918804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918804).length < 2 ^ (prefixWord ++ tailWord_2918804).sum := by decide
  have hdescent : baseEnd_2918804 < baseStart_2918804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918810 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5]
def baseStart_2918810 : Nat := 118140960795 + 2918810 * 2 ^ 59
def prefixEnd_2918810 : Nat := 4983230072969 + 3 ^ 40 * 2918810 * 2
def baseEnd_2918810 : Nat := 1498752469149830376151643

theorem tailTrace_2918810 : CollatzResearch.WordTrace tailWord_2918810 prefixEnd_2918810 1498752469149830376151643 := by
  unfold tailWord_2918810
  simp only [CollatzResearch.WordTrace]
  refine ⟨26614436638914334476512471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70971831037104891937366589 26614436638914334476512471)
  ·
    refine ⟨39921654958371501714768707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26614436638914334476512471 39921654958371501714768707)
    ·
      refine ⟨59882482437557252572153061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39921654958371501714768707 59882482437557252572153061)
      ·
        refine ⟨11227965457041984857278699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59882482437557252572153061 11227965457041984857278699)
        ·
          refine ⟨16841948185562977285918049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11227965457041984857278699 16841948185562977285918049)
          ·
            refine ⟨12631461139172232964438537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16841948185562977285918049 12631461139172232964438537)
            ·
              refine ⟨9473595854379174723328903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12631461139172232964438537 9473595854379174723328903)
              ·
                refine ⟨14210393781568762084993355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9473595854379174723328903 14210393781568762084993355)
                ·
                  refine ⟨21315590672353143127490033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14210393781568762084993355 21315590672353143127490033)
                  ·
                    refine ⟨15986693004264857345617525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21315590672353143127490033 15986693004264857345617525)
                    ·
                      refine ⟨1498752469149830376151643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15986693004264857345617525 1498752469149830376151643)
                      ·
                        rfl

theorem cell23_2918810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_2918810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918810 prefixEnd_2918810 := by exact prefixLift 2918810
  have htrace : WordTrace (prefixWord ++ tailWord_2918810) baseStart_2918810 baseEnd_2918810 := by
    simpa [prefixWord, tailWord_2918810, baseEnd_2918810] using wordTrace_append hprefix tailTrace_2918810
  have hstable : (prefixWord ++ tailWord_2918810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918810).length < 2 ^ (prefixWord ++ tailWord_2918810).sum := by decide
  have hdescent : baseEnd_2918810 < baseStart_2918810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918814 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_2918814 : Nat := 118140960795 + 2918814 * 2 ^ 59
def prefixEnd_2918814 : Nat := 4983230072969 + 3 ^ 40 * 2918814 * 2
def baseEnd_2918814 : Nat := 1498754523072448360501625

theorem tailTrace_2918814 : CollatzResearch.WordTrace tailWord_2918814 prefixEnd_2918814 1498754523072448360501625 := by
  unfold tailWord_2918814
  simp only [CollatzResearch.WordTrace]
  refine ⟨13307236555955355823649437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70971928298428564392796997 13307236555955355823649437)
  ·
    refine ⟨4990213708483258433868539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13307236555955355823649437 4990213708483258433868539)
    ·
      refine ⟨7485320562724887650802809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4990213708483258433868539 7485320562724887650802809)
      ·
        refine ⟨5613990422043665738102107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7485320562724887650802809 5613990422043665738102107)
        ·
          refine ⟨8420985633065498607153161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5613990422043665738102107 8420985633065498607153161)
          ·
            refine ⟨6315739224799123955364871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8420985633065498607153161 6315739224799123955364871)
            ·
              refine ⟨9473608837198685933047307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6315739224799123955364871 9473608837198685933047307)
              ·
                refine ⟨14210413255798028899570961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9473608837198685933047307 14210413255798028899570961)
                ·
                  refine ⟨10657809941848521674678221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14210413255798028899570961 10657809941848521674678221)
                  ·
                    refine ⟨3996678728193195628004333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10657809941848521674678221 3996678728193195628004333)
                    ·
                      refine ⟨1498754523072448360501625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3996678728193195628004333 1498754523072448360501625)
                      ·
                        rfl

theorem cell23_2918814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_2918814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918814 prefixEnd_2918814 := by exact prefixLift 2918814
  have htrace : WordTrace (prefixWord ++ tailWord_2918814) baseStart_2918814 baseEnd_2918814 := by
    simpa [prefixWord, tailWord_2918814, baseEnd_2918814] using wordTrace_append hprefix tailTrace_2918814
  have hstable : (prefixWord ++ tailWord_2918814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918814).length < 2 ^ (prefixWord ++ tailWord_2918814).sum := by decide
  have hdescent : baseEnd_2918814 < baseStart_2918814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918820 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_2918820 : Nat := 118140960795 + 2918820 * 2 ^ 59
def prefixEnd_2918820 : Nat := 4983230072969 + 3 ^ 40 * 2918820 * 2
def baseEnd_2918820 : Nat := 1498757603956375337026597

theorem tailTrace_2918820 : CollatzResearch.WordTrace tailWord_2918820 prefixEnd_2918820 1498757603956375337026597 := by
  unfold tailWord_2918820
  simp only [CollatzResearch.WordTrace]
  refine ⟨53229055642810554806956957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70972074190414073075942609 53229055642810554806956957)
  ·
    refine ⟨19960895866053958052608859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53229055642810554806956957 19960895866053958052608859)
    ·
      refine ⟨29941343799080937078913289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19960895866053958052608859 29941343799080937078913289)
      ·
        refine ⟨22456007849310702809184967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29941343799080937078913289 22456007849310702809184967)
        ·
          refine ⟨33684011773966054213777451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22456007849310702809184967 33684011773966054213777451)
          ·
            refine ⟨50526017660949081320666177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33684011773966054213777451 50526017660949081320666177)
            ·
              refine ⟨37894513245711810990499633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50526017660949081320666177 37894513245711810990499633)
              ·
                refine ⟨28420884934283858242874725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37894513245711810990499633 28420884934283858242874725)
                ·
                  refine ⟨5328915925178223420539011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28420884934283858242874725 5328915925178223420539011)
                  ·
                    refine ⟨7993373887767335130808517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5328915925178223420539011 7993373887767335130808517)
                    ·
                      refine ⟨1498757603956375337026597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7993373887767335130808517 1498757603956375337026597)
                      ·
                        rfl

theorem cell23_2918820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_2918820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918820 prefixEnd_2918820 := by exact prefixLift 2918820
  have htrace : WordTrace (prefixWord ++ tailWord_2918820) baseStart_2918820 baseEnd_2918820 := by
    simpa [prefixWord, tailWord_2918820, baseEnd_2918820] using wordTrace_append hprefix tailTrace_2918820
  have hstable : (prefixWord ++ tailWord_2918820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918820).length < 2 ^ (prefixWord ++ tailWord_2918820).sum := by decide
  have hdescent : baseEnd_2918820 < baseStart_2918820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918837 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_2918837 : Nat := 118140960795 + 2918837 * 2 ^ 59
def prefixEnd_2918837 : Nat := 4983230072969 + 3 ^ 40 * 2918837 * 2
def baseEnd_2918837 : Nat := 1498766333127501770514019

theorem tailTrace_2918837 : CollatzResearch.WordTrace tailWord_2918837 prefixEnd_2918837 1498766333127501770514019 := by
  unfold tailWord_2918837
  simp only [CollatzResearch.WordTrace]
  refine ⟨106458731326559521517282765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70972487551039681011521843 106458731326559521517282765)
  ·
    refine ⟨39922024247459820568981037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106458731326559521517282765 39922024247459820568981037)
    ·
      refine ⟨14970759092797432713367889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39922024247459820568981037 14970759092797432713367889)
      ·
        refine ⟨11228069319598074535025917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14970759092797432713367889 11228069319598074535025917)
        ·
          refine ⟨4210525994849277950634719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11228069319598074535025917 4210525994849277950634719)
          ·
            refine ⟨6315788992273916925952079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210525994849277950634719 6315788992273916925952079)
            ·
              refine ⟨9473683488410875388928119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6315788992273916925952079 9473683488410875388928119)
              ·
                refine ⟨14210525232616313083392179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9473683488410875388928119 14210525232616313083392179)
                ·
                  refine ⟨21315787848924469625088269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14210525232616313083392179 21315787848924469625088269)
                  ·
                    refine ⟨7993420443346676109408101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21315787848924469625088269 7993420443346676109408101)
                    ·
                      refine ⟨1498766333127501770514019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7993420443346676109408101 1498766333127501770514019)
                      ·
                        rfl

theorem cell23_2918837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_2918837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918837 prefixEnd_2918837 := by exact prefixLift 2918837
  have htrace : WordTrace (prefixWord ++ tailWord_2918837) baseStart_2918837 baseEnd_2918837 := by
    simpa [prefixWord, tailWord_2918837, baseEnd_2918837] using wordTrace_append hprefix tailTrace_2918837
  have hstable : (prefixWord ++ tailWord_2918837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918837).length < 2 ^ (prefixWord ++ tailWord_2918837).sum := by decide
  have hdescent : baseEnd_2918837 < baseStart_2918837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918853 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 2, 4, 7]
def baseStart_2918853 : Nat := 118140960795 + 2918853 * 2 ^ 59
def prefixEnd_2918853 : Nat := 4983230072969 + 3 ^ 40 * 2918853 * 2
def baseEnd_2918853 : Nat := 1498774548817973707913945

theorem tailTrace_2918853 : CollatzResearch.WordTrace tailWord_2918853 prefixEnd_2918853 1498774548817973707913945 := by
  unfold tailWord_2918853
  simp only [CollatzResearch.WordTrace]
  refine ⟨106459314894501556249865213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70972876596334370833243475 106459314894501556249865213)
  ·
    refine ⟨39922243085438083593699455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106459314894501556249865213 39922243085438083593699455)
    ·
      refine ⟨59883364628157125390549183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39922243085438083593699455 59883364628157125390549183)
      ·
        refine ⟨89825046942235688085823775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59883364628157125390549183 89825046942235688085823775)
        ·
          refine ⟨134737570413353532128735663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89825046942235688085823775 134737570413353532128735663)
          ·
            refine ⟨202106355620030298193103495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134737570413353532128735663 202106355620030298193103495)
            ·
              refine ⟨303159533430045447289655243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202106355620030298193103495 303159533430045447289655243)
              ·
                refine ⟨454739300145068170934482865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303159533430045447289655243 454739300145068170934482865)
                ·
                  refine ⟨341054475108801128200862149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454739300145068170934482865 341054475108801128200862149)
                  ·
                    refine ⟨63947714082900211537661653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 341054475108801128200862149 63947714082900211537661653)
                    ·
                      refine ⟨1498774548817973707913945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63947714082900211537661653 1498774548817973707913945)
                      ·
                        rfl

theorem cell23_2918853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_2918853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918853 prefixEnd_2918853 := by exact prefixLift 2918853
  have htrace : WordTrace (prefixWord ++ tailWord_2918853) baseStart_2918853 baseEnd_2918853 := by
    simpa [prefixWord, tailWord_2918853, baseEnd_2918853] using wordTrace_append hprefix tailTrace_2918853
  have hstable : (prefixWord ++ tailWord_2918853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918853).length < 2 ^ (prefixWord ++ tailWord_2918853).sum := by decide
  have hdescent : baseEnd_2918853 < baseStart_2918853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918897 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 1, 5, 2]
def baseStart_2918897 : Nat := 118140960795 + 2918897 * 2 ^ 59
def prefixEnd_2918897 : Nat := 4983230072969 + 3 ^ 40 * 2918897 * 2
def baseEnd_2918897 : Nat := 1498797141966771535763743

theorem tailTrace_2918897 : CollatzResearch.WordTrace tailWord_2918897 prefixEnd_2918897 1498797141966771535763743 := by
  unfold tailWord_2918897
  simp only [CollatzResearch.WordTrace]
  refine ⟨106460919706342151764466945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70973946470894767842977963 106460919706342151764466945)
  ·
    refine ⟨79845689779756613823350209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106460919706342151764466945 79845689779756613823350209)
    ·
      refine ⟨59884267334817460367512657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79845689779756613823350209 59884267334817460367512657)
      ·
        refine ⟨44913200501113095275634493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59884267334817460367512657 44913200501113095275634493)
        ·
          refine ⟨16842450187917410728362935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44913200501113095275634493 16842450187917410728362935)
          ·
            refine ⟨25263675281876116092544403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16842450187917410728362935 25263675281876116092544403)
            ·
              refine ⟨37895512922814174138816605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25263675281876116092544403 37895512922814174138816605)
              ·
                refine ⟨14210817346055315302056227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37895512922814174138816605 14210817346055315302056227)
                ·
                  refine ⟨21316226019082972953084341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14210817346055315302056227 21316226019082972953084341)
                  ·
                    refine ⟨1998396189289028714351657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21316226019082972953084341 1998396189289028714351657)
                    ·
                      refine ⟨1498797141966771535763743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1998396189289028714351657 1498797141966771535763743)
                      ·
                        rfl

theorem cell23_2918897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_2918897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918897 prefixEnd_2918897 := by exact prefixLift 2918897
  have htrace : WordTrace (prefixWord ++ tailWord_2918897) baseStart_2918897 baseEnd_2918897 := by
    simpa [prefixWord, tailWord_2918897, baseEnd_2918897] using wordTrace_append hprefix tailTrace_2918897
  have hstable : (prefixWord ++ tailWord_2918897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918897).length < 2 ^ (prefixWord ++ tailWord_2918897).sum := by decide
  have hdescent : baseEnd_2918897 < baseStart_2918897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918898 : List Nat := [3, 2, 1, 4, 2, 2, 1, 3, 1, 4]
def baseStart_2918898 : Nat := 118140960795 + 2918898 * 2 ^ 59
def prefixEnd_2918898 : Nat := 4983230072969 + 3 ^ 40 * 2918898 * 2
def baseEnd_2918898 : Nat := 499599218482475343950413

theorem tailTrace_2918898 : CollatzResearch.WordTrace tailWord_2918898 prefixEnd_2918898 499599218482475343950413 := by
  unfold tailWord_2918898
  simp only [CollatzResearch.WordTrace]
  refine ⟨26615239044834632233813337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70973970786225685956835565 26615239044834632233813337)
  ·
    refine ⟨19961429283625974175360003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26615239044834632233813337 19961429283625974175360003)
    ·
      refine ⟨29942143925438961263040005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19961429283625974175360003 29942143925438961263040005)
      ·
        refine ⟨5614151986019805236820001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29942143925438961263040005 5614151986019805236820001)
        ·
          refine ⟨4210613989514853927615001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5614151986019805236820001 4210613989514853927615001)
          ·
            refine ⟨3157960492136140445711251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4210613989514853927615001 3157960492136140445711251)
            ·
              refine ⟨4736940738204210668566877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3157960492136140445711251 4736940738204210668566877)
              ·
                refine ⟨1776352776826579000712579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4736940738204210668566877 1776352776826579000712579)
                ·
                  refine ⟨2664529165239868501068869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776352776826579000712579 2664529165239868501068869)
                  ·
                    refine ⟨499599218482475343950413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2664529165239868501068869 499599218482475343950413)
                    ·
                      rfl

theorem cell23_2918898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_2918898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918898 prefixEnd_2918898 := by exact prefixLift 2918898
  have htrace : WordTrace (prefixWord ++ tailWord_2918898) baseStart_2918898 baseEnd_2918898 := by
    simpa [prefixWord, tailWord_2918898, baseEnd_2918898] using wordTrace_append hprefix tailTrace_2918898
  have hstable : (prefixWord ++ tailWord_2918898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918898).length < 2 ^ (prefixWord ++ tailWord_2918898).sum := by decide
  have hdescent : baseEnd_2918898 < baseStart_2918898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918937 : List Nat := [1, 2, 1, 2, 1, 1, 2, 7, 2, 4]
def baseStart_2918937 : Nat := 118140960795 + 2918937 * 2 ^ 59
def prefixEnd_2918937 : Nat := 4983230072969 + 3 ^ 40 * 2918937 * 2
def baseEnd_2918937 : Nat := 499605893730983793087853

theorem tailTrace_2918937 : CollatzResearch.WordTrace tailWord_2918937 prefixEnd_2918937 499605893730983793087853 := by
  unfold tailWord_2918937
  simp only [CollatzResearch.WordTrace]
  refine ⟨106462378626197238595923065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70974919084131492397282043 106462378626197238595923065)
  ·
    refine ⟨79846783969647928946942299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106462378626197238595923065 79846783969647928946942299)
    ·
      refine ⟨119770175954471893420413449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79846783969647928946942299 119770175954471893420413449)
      ·
        refine ⟨89827631965853920065310087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119770175954471893420413449 89827631965853920065310087)
        ·
          refine ⟨134741447948780880097965131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89827631965853920065310087 134741447948780880097965131)
          ·
            refine ⟨202112171923171320146947697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134741447948780880097965131 202112171923171320146947697)
            ·
              refine ⟨151584128942378490110210773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202112171923171320146947697 151584128942378490110210773)
              ·
                refine ⟨3552753022086995861958065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 151584128942378490110210773 3552753022086995861958065)
                ·
                  refine ⟨2664564766565246896468549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3552753022086995861958065 2664564766565246896468549)
                  ·
                    refine ⟨499605893730983793087853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2664564766565246896468549 499605893730983793087853)
                    ·
                      rfl

theorem cell23_2918937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 4].length) (baseStart_2918937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918937 prefixEnd_2918937 := by exact prefixLift 2918937
  have htrace : WordTrace (prefixWord ++ tailWord_2918937) baseStart_2918937 baseEnd_2918937 := by
    simpa [prefixWord, tailWord_2918937, baseEnd_2918937] using wordTrace_append hprefix tailTrace_2918937
  have hstable : (prefixWord ++ tailWord_2918937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918937).length < 2 ^ (prefixWord ++ tailWord_2918937).sum := by decide
  have hdescent : baseEnd_2918937 < baseStart_2918937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918944 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2918944 : Nat := 118140960795 + 2918944 * 2 ^ 59
def prefixEnd_2918944 : Nat := 4983230072969 + 3 ^ 40 * 2918944 * 2
def baseEnd_2918944 : Nat := 1498821275557532851876027

theorem tailTrace_2918944 : CollatzResearch.WordTrace tailWord_2918944 prefixEnd_2918944 1498821275557532851876027 := by
  unfold tailWord_2918944
  simp only [CollatzResearch.WordTrace]
  refine ⟨53231316968585939395713943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70975089291447919194285257 53231316968585939395713943)
  ·
    refine ⟨79846975452878909093570915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53231316968585939395713943 79846975452878909093570915)
    ·
      refine ⟨119770463179318363640356373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79846975452878909093570915 119770463179318363640356373)
      ·
        refine ⟨5614240461530548295641705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 119770463179318363640356373 5614240461530548295641705)
        ·
          refine ⟨4210680346147911221731279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5614240461530548295641705 4210680346147911221731279)
          ·
            refine ⟨6316020519221866832596919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210680346147911221731279 6316020519221866832596919)
            ·
              refine ⟨9474030778832800248895379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6316020519221866832596919 9474030778832800248895379)
              ·
                refine ⟨14211046168249200373343069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9474030778832800248895379 14211046168249200373343069)
                ·
                  refine ⟨5329142313093450140003651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14211046168249200373343069 5329142313093450140003651)
                  ·
                    refine ⟨7993713469640175210005477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5329142313093450140003651 7993713469640175210005477)
                    ·
                      refine ⟨1498821275557532851876027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7993713469640175210005477 1498821275557532851876027)
                      ·
                        rfl

theorem cell23_2918944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2918944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918944 prefixEnd_2918944 := by exact prefixLift 2918944
  have htrace : WordTrace (prefixWord ++ tailWord_2918944) baseStart_2918944 baseEnd_2918944 := by
    simpa [prefixWord, tailWord_2918944, baseEnd_2918944] using wordTrace_append hprefix tailTrace_2918944
  have hstable : (prefixWord ++ tailWord_2918944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918944).length < 2 ^ (prefixWord ++ tailWord_2918944).sum := by decide
  have hdescent : baseEnd_2918944 < baseStart_2918944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918948 : List Nat := [2, 3, 1, 5, 1, 1, 2, 1, 2, 3, 2]
def baseStart_2918948 : Nat := 118140960795 + 2918948 * 2 ^ 59
def prefixEnd_2918948 : Nat := 4983230072969 + 3 ^ 40 * 2918948 * 2
def baseEnd_2918948 : Nat := 1498823329480150836226009

theorem tailTrace_2918948 : CollatzResearch.WordTrace tailWord_2918948 prefixEnd_2918948 1498823329480150836226009 := by
  unfold tailWord_2918948
  simp only [CollatzResearch.WordTrace]
  refine ⟨53231389914578693737286749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70975186552771591649715665 53231389914578693737286749)
  ·
    refine ⟨19961771217967010151482531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53231389914578693737286749 19961771217967010151482531)
    ·
      refine ⟨29942656826950515227223797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19961771217967010151482531 29942656826950515227223797)
      ·
        refine ⟨2807124077526610802552231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29942656826950515227223797 2807124077526610802552231)
        ·
          refine ⟨4210686116289916203828347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2807124077526610802552231 4210686116289916203828347)
          ·
            refine ⟨6316029174434874305742521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210686116289916203828347 6316029174434874305742521)
            ·
              refine ⟨4737021880826155729306891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6316029174434874305742521 4737021880826155729306891)
              ·
                refine ⟨7105532821239233593960337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4737021880826155729306891 7105532821239233593960337)
                ·
                  refine ⟨5329149615929425195470253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7105532821239233593960337 5329149615929425195470253)
                  ·
                    refine ⟨1998431105973534448301345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5329149615929425195470253 1998431105973534448301345)
                    ·
                      refine ⟨1498823329480150836226009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1998431105973534448301345 1498823329480150836226009)
                      ·
                        rfl

theorem cell23_2918948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_2918948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918948 prefixEnd_2918948 := by exact prefixLift 2918948
  have htrace : WordTrace (prefixWord ++ tailWord_2918948) baseStart_2918948 baseEnd_2918948 := by
    simpa [prefixWord, tailWord_2918948, baseEnd_2918948] using wordTrace_append hprefix tailTrace_2918948
  have hstable : (prefixWord ++ tailWord_2918948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918948).length < 2 ^ (prefixWord ++ tailWord_2918948).sum := by decide
  have hdescent : baseEnd_2918948 < baseStart_2918948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918994 : List Nat := [3, 2, 2, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_2918994 : Nat := 118140960795 + 2918994 * 2 ^ 59
def prefixEnd_2918994 : Nat := 4983230072969 + 3 ^ 40 * 2918994 * 2
def baseEnd_2918994 : Nat := 1498846949590257656250797

theorem tailTrace_2918994 : CollatzResearch.WordTrace tailWord_2918994 prefixEnd_2918994 1498846949590257656250797 := by
  unfold tailWord_2918994
  simp only [CollatzResearch.WordTrace]
  refine ⟨26616114396747684332687009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70976305057993824887165357 26616114396747684332687009)
  ·
    refine ⟨19962085797560763249515257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26616114396747684332687009 19962085797560763249515257)
    ·
      refine ⟨14971564348170572437136443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19962085797560763249515257 14971564348170572437136443)
      ·
        refine ⟨22457346522255858655704665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14971564348170572437136443 22457346522255858655704665)
        ·
          refine ⟨16843009891691893991778499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22457346522255858655704665 16843009891691893991778499)
          ·
            refine ⟨25264514837537840987667749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16843009891691893991778499 25264514837537840987667749)
            ·
              refine ⟨4737096532038345185187703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25264514837537840987667749 4737096532038345185187703)
              ·
                refine ⟨7105644798057517777781555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4737096532038345185187703 7105644798057517777781555)
                ·
                  refine ⟨10658467197086276666672333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7105644798057517777781555 10658467197086276666672333)
                  ·
                    refine ⟨3996925198907353750002125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10658467197086276666672333 3996925198907353750002125)
                    ·
                      refine ⟨1498846949590257656250797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3996925198907353750002125 1498846949590257656250797)
                      ·
                        rfl

theorem cell23_2918994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_2918994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2918994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2918994 prefixEnd_2918994 := by exact prefixLift 2918994
  have htrace : WordTrace (prefixWord ++ tailWord_2918994) baseStart_2918994 baseEnd_2918994 := by
    simpa [prefixWord, tailWord_2918994, baseEnd_2918994] using wordTrace_append hprefix tailTrace_2918994
  have hstable : (prefixWord ++ tailWord_2918994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918994).length < 2 ^ (prefixWord ++ tailWord_2918994).sum := by decide
  have hdescent : baseEnd_2918994 < baseStart_2918994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919042 : List Nat := [3, 4, 3, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_2919042 : Nat := 118140960795 + 2919042 * 2 ^ 59
def prefixEnd_2919042 : Nat := 4983230072969 + 3 ^ 40 * 2919042 * 2
def baseEnd_2919042 : Nat := 1498871596661673468450577

theorem tailTrace_2919042 : CollatzResearch.WordTrace tailWord_2919042 prefixEnd_2919042 1498871596661673468450577 := by
  unfold tailWord_2919042
  simp only [CollatzResearch.WordTrace]
  refine ⟨26616552072704210382123845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70977472193877894352330253 26616552072704210382123845)
  ·
    refine ⟨4990603513632039446648221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26616552072704210382123845 4990603513632039446648221)
    ·
      refine ⟨1871476317612014792493083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4990603513632039446648221 1871476317612014792493083)
      ·
        refine ⟨2807214476418022188739625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1871476317612014792493083 2807214476418022188739625)
        ·
          refine ⟨2105410857313516641554719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2807214476418022188739625 2105410857313516641554719)
          ·
            refine ⟨3158116285970274962332079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2105410857313516641554719 3158116285970274962332079)
            ·
              refine ⟨4737174428955412443498119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3158116285970274962332079 4737174428955412443498119)
              ·
                refine ⟨7105761643433118665247179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4737174428955412443498119 7105761643433118665247179)
                ·
                  refine ⟨10658642465149677997870769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7105761643433118665247179 10658642465149677997870769)
                  ·
                    refine ⟨7993981848862258498403077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10658642465149677997870769 7993981848862258498403077)
                    ·
                      refine ⟨1498871596661673468450577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7993981848862258498403077 1498871596661673468450577)
                      ·
                        rfl

theorem cell23_2919042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_2919042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919042 prefixEnd_2919042 := by exact prefixLift 2919042
  have htrace : WordTrace (prefixWord ++ tailWord_2919042) baseStart_2919042 baseEnd_2919042 := by
    simpa [prefixWord, tailWord_2919042, baseEnd_2919042] using wordTrace_append hprefix tailTrace_2919042
  have hstable : (prefixWord ++ tailWord_2919042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919042).length < 2 ^ (prefixWord ++ tailWord_2919042).sum := by decide
  have hdescent : baseEnd_2919042 < baseStart_2919042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919047 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_2919047 : Nat := 118140960795 + 2919047 * 2 ^ 59
def prefixEnd_2919047 : Nat := 4983230072969 + 3 ^ 40 * 2919047 * 2
def baseEnd_2919047 : Nat := 1498874164064945948888053

theorem tailTrace_2919047 : CollatzResearch.WordTrace tailWord_2919047 prefixEnd_2919047 1498874164064945948888053 := by
  unfold tailWord_2919047
  simp only [CollatzResearch.WordTrace]
  refine ⟨106466390655798727382427395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70977593770532484921618263 106466390655798727382427395)
  ·
    refine ⟨159699585983698091073641093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106466390655798727382427395 159699585983698091073641093)
    ·
      refine ⟨29943672371943392076307705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159699585983698091073641093 29943672371943392076307705)
      ·
        refine ⟨22457754278957544057230779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29943672371943392076307705 22457754278957544057230779)
        ·
          refine ⟨33686631418436316085846169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22457754278957544057230779 33686631418436316085846169)
          ·
            refine ⟨25264973563827237064384627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33686631418436316085846169 25264973563827237064384627)
            ·
              refine ⟨37897460345740855596576941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25264973563827237064384627 37897460345740855596576941)
              ·
                refine ⟨14211547629652820848716353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37897460345740855596576941 14211547629652820848716353)
                ·
                  refine ⟨10658660722239615636537265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14211547629652820848716353 10658660722239615636537265)
                  ·
                    refine ⟨7993995541679711727402949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10658660722239615636537265 7993995541679711727402949)
                    ·
                      refine ⟨1498874164064945948888053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7993995541679711727402949 1498874164064945948888053)
                      ·
                        rfl

theorem cell23_2919047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_2919047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919047 prefixEnd_2919047 := by exact prefixLift 2919047
  have htrace : WordTrace (prefixWord ++ tailWord_2919047) baseStart_2919047 baseEnd_2919047 := by
    simpa [prefixWord, tailWord_2919047, baseEnd_2919047] using wordTrace_append hprefix tailTrace_2919047
  have hstable : (prefixWord ++ tailWord_2919047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919047).length < 2 ^ (prefixWord ++ tailWord_2919047).sum := by decide
  have hdescent : baseEnd_2919047 < baseStart_2919047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919087 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 4, 5]
def baseStart_2919087 : Nat := 118140960795 + 2919087 * 2 ^ 59
def prefixEnd_2919087 : Nat := 4983230072969 + 3 ^ 40 * 2919087 * 2
def baseEnd_2919087 : Nat := 499631567763708597462623

theorem tailTrace_2919087 : CollatzResearch.WordTrace tailWord_2919087 prefixEnd_2919087 499631567763708597462623 := by
  unfold tailWord_2919087
  simp only [CollatzResearch.WordTrace]
  refine ⟨106467849575653814213883515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70978566383769209475922343 106467849575653814213883515)
  ·
    refine ⟨159701774363480721320825273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106467849575653814213883515 159701774363480721320825273)
    ·
      refine ⟨119776330772610540990618955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159701774363480721320825273 119776330772610540990618955)
      ·
        refine ⟨179664496158915811485928433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119776330772610540990618955 179664496158915811485928433)
        ·
          refine ⟨134748372119186858614446325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179664496158915811485928433 134748372119186858614446325)
          ·
            refine ⟨12632659886173767995104343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134748372119186858614446325 12632659886173767995104343)
            ·
              refine ⟨18948989829260651992656515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12632659886173767995104343 18948989829260651992656515)
              ·
                refine ⟨28423484743890977988984773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18948989829260651992656515 28423484743890977988984773)
                ·
                  refine ⟨5329403389479558372934645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28423484743890977988984773 5329403389479558372934645)
                  ·
                    refine ⟨499631567763708597462623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5329403389479558372934645 499631567763708597462623)
                    ·
                      rfl

theorem cell23_2919087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 5].length) (baseStart_2919087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919087 prefixEnd_2919087 := by exact prefixLift 2919087
  have htrace : WordTrace (prefixWord ++ tailWord_2919087) baseStart_2919087 baseEnd_2919087 := by
    simpa [prefixWord, tailWord_2919087, baseEnd_2919087] using wordTrace_append hprefix tailTrace_2919087
  have hstable : (prefixWord ++ tailWord_2919087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919087).length < 2 ^ (prefixWord ++ tailWord_2919087).sum := by decide
  have hdescent : baseEnd_2919087 < baseStart_2919087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919091 : List Nat := [1, 1, 1, 2, 3, 5, 3, 2, 5]
def baseStart_2919091 : Nat := 118140960795 + 2919091 * 2 ^ 59
def prefixEnd_2919091 : Nat := 4983230072969 + 3 ^ 40 * 2919091 * 2
def baseEnd_2919091 : Nat := 166544084134860419637539

theorem tailTrace_2919091 : CollatzResearch.WordTrace tailWord_2919091 prefixEnd_2919091 166544084134860419637539 := by
  unfold tailWord_2919091
  simp only [CollatzResearch.WordTrace]
  refine ⟨106467995467639322897029127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70978663645092881931352751 106467995467639322897029127)
  ·
    refine ⟨159701993201458984345543691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106467995467639322897029127 159701993201458984345543691)
    ·
      refine ⟨239552989802188476518315537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159701993201458984345543691 239552989802188476518315537)
      ·
        refine ⟨179664742351641357388736653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239552989802188476518315537 179664742351641357388736653)
        ·
          refine ⟨67374278381865509020776245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179664742351641357388736653 67374278381865509020776245)
          ·
            refine ⟨6316338598299891470697773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67374278381865509020776245 6316338598299891470697773)
            ·
              refine ⟨2368626974362459301511665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6316338598299891470697773 2368626974362459301511665)
              ·
                refine ⟨1776470230771844476133749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2368626974362459301511665 1776470230771844476133749)
                ·
                  refine ⟨166544084134860419637539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1776470230771844476133749 166544084134860419637539)
                  ·
                    rfl

theorem cell23_2919091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 5].length) (baseStart_2919091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919091 prefixEnd_2919091 := by exact prefixLift 2919091
  have htrace : WordTrace (prefixWord ++ tailWord_2919091) baseStart_2919091 baseEnd_2919091 := by
    simpa [prefixWord, tailWord_2919091, baseEnd_2919091] using wordTrace_append hprefix tailTrace_2919091
  have hstable : (prefixWord ++ tailWord_2919091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919091).length < 2 ^ (prefixWord ++ tailWord_2919091).sum := by decide
  have hdescent : baseEnd_2919091 < baseStart_2919091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919164 : List Nat := [2, 2, 2, 1, 3, 2, 2, 3, 6]
def baseStart_2919164 : Nat := 118140960795 + 2919164 * 2 ^ 59
def prefixEnd_2919164 : Nat := 4983230072969 + 3 ^ 40 * 2919164 * 2
def baseEnd_2919164 : Nat := 166548249033502443458335

theorem tailTrace_2919164 : CollatzResearch.WordTrace tailWord_2919164 prefixEnd_2919164 166548249033502443458335 := by
  unfold tailWord_2919164
  simp only [CollatzResearch.WordTrace]
  refine ⟨53235328998187428182218273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70980438664249904242957697 53235328998187428182218273)
  ·
    refine ⟨39926496748640571136663705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53235328998187428182218273 39926496748640571136663705)
    ·
      refine ⟨29944872561480428352497779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39926496748640571136663705 29944872561480428352497779)
      ·
        refine ⟨44917308842220642528746669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29944872561480428352497779 44917308842220642528746669)
        ·
          refine ⟨16843990815832740948280001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44917308842220642528746669 16843990815832740948280001)
          ·
            refine ⟨12632993111874555711210001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16843990815832740948280001 12632993111874555711210001)
            ·
              refine ⟨9474744833905916783407501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12632993111874555711210001 9474744833905916783407501)
              ·
                refine ⟨3553029312714718793777813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9474744833905916783407501 3553029312714718793777813)
                ·
                  refine ⟨166548249033502443458335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3553029312714718793777813 166548249033502443458335)
                  ·
                    rfl

theorem cell23_2919164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 6].length) (baseStart_2919164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919164 prefixEnd_2919164 := by exact prefixLift 2919164
  have htrace : WordTrace (prefixWord ++ tailWord_2919164) baseStart_2919164 baseEnd_2919164 := by
    simpa [prefixWord, tailWord_2919164, baseEnd_2919164] using wordTrace_append hprefix tailTrace_2919164
  have hstable : (prefixWord ++ tailWord_2919164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919164).length < 2 ^ (prefixWord ++ tailWord_2919164).sum := by decide
  have hdescent : baseEnd_2919164 < baseStart_2919164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919201 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 4, 3, 2]
def baseStart_2919201 : Nat := 118140960795 + 2919201 * 2 ^ 59
def prefixEnd_2919201 : Nat := 4983230072969 + 3 ^ 40 * 2919201 * 2
def baseEnd_2919201 : Nat := 1498953240085738346362345

theorem tailTrace_2919201 : CollatzResearch.WordTrace tailWord_2919201 prefixEnd_2919201 1498953240085738346362345 := by
  unfold tailWord_2919201
  simp only [CollatzResearch.WordTrace]
  refine ⟨106472007497240811683533457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70981338331493874455688971 106472007497240811683533457)
  ·
    refine ⟨79854005622930608762650093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106472007497240811683533457 79854005622930608762650093)
    ·
      refine ⟨29945252108598978285993785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79854005622930608762650093 29945252108598978285993785)
      ·
        refine ⟨22458939081449233714495339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29945252108598978285993785 22458939081449233714495339)
        ·
          refine ⟨33688408622173850571743009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22458939081449233714495339 33688408622173850571743009)
          ·
            refine ⟨25266306466630387928807257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33688408622173850571743009 25266306466630387928807257)
            ·
              refine ⟨18949729849972790946605443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25266306466630387928807257 18949729849972790946605443)
              ·
                refine ⟨28424594774959186419908165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18949729849972790946605443 28424594774959186419908165)
                ·
                  refine ⟨5329611520304847453732781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28424594774959186419908165 5329611520304847453732781)
                  ·
                    refine ⟨1998604320114317795149793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5329611520304847453732781 1998604320114317795149793)
                    ·
                      refine ⟨1498953240085738346362345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1998604320114317795149793 1498953240085738346362345)
                      ·
                        rfl

theorem cell23_2919201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_2919201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919201 prefixEnd_2919201 := by exact prefixLift 2919201
  have htrace : WordTrace (prefixWord ++ tailWord_2919201) baseStart_2919201 baseEnd_2919201 := by
    simpa [prefixWord, tailWord_2919201, baseEnd_2919201] using wordTrace_append hprefix tailTrace_2919201
  have hstable : (prefixWord ++ tailWord_2919201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919201).length < 2 ^ (prefixWord ++ tailWord_2919201).sum := by decide
  have hdescent : baseEnd_2919201 < baseStart_2919201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919208 : List Nat := [2, 1, 5, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_2919208 : Nat := 118140960795 + 2919208 * 2 ^ 59
def prefixEnd_2919208 : Nat := 4983230072969 + 3 ^ 40 * 2919208 * 2
def baseEnd_2919208 : Nat := 1498956834450319818974813

theorem tailTrace_2919208 : CollatzResearch.WordTrace tailWord_2919208 prefixEnd_2919208 1498956834450319818974813 := by
  unfold tailWord_2919208
  simp only [CollatzResearch.WordTrace]
  refine ⟨53236131404107725939519139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70981508538810301252692185 53236131404107725939519139)
  ·
    refine ⟨79854197106161588909278709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53236131404107725939519139 79854197106161588909278709)
    ·
      refine ⟨7486330978702648960244879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79854197106161588909278709 7486330978702648960244879)
      ·
        refine ⟨11229496468053973440367319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7486330978702648960244879 11229496468053973440367319)
        ·
          refine ⟨16844244702080960160550979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11229496468053973440367319 16844244702080960160550979)
          ·
            refine ⟨25266367053121440240826469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16844244702080960160550979 25266367053121440240826469)
            ·
              refine ⟨4737443822460270045154963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25266367053121440240826469 4737443822460270045154963)
              ·
                refine ⟨7106165733690405067732445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4737443822460270045154963 7106165733690405067732445)
                ·
                  refine ⟨2664812150133901900399667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7106165733690405067732445 2664812150133901900399667)
                  ·
                    refine ⟨3997218225200852850599501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2664812150133901900399667 3997218225200852850599501)
                    ·
                      refine ⟨1498956834450319818974813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3997218225200852850599501 1498956834450319818974813)
                      ·
                        rfl

theorem cell23_2919208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_2919208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919208 prefixEnd_2919208 := by exact prefixLift 2919208
  have htrace : WordTrace (prefixWord ++ tailWord_2919208) baseStart_2919208 baseEnd_2919208 := by
    simpa [prefixWord, tailWord_2919208, baseEnd_2919208] using wordTrace_append hprefix tailTrace_2919208
  have hstable : (prefixWord ++ tailWord_2919208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919208).length < 2 ^ (prefixWord ++ tailWord_2919208).sum := by decide
  have hdescent : baseEnd_2919208 < baseStart_2919208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919231 : List Nat := [1, 1, 2, 2, 5, 1, 1, 4, 1, 1, 4]
def baseStart_2919231 : Nat := 118140960795 + 2919231 * 2 ^ 59
def prefixEnd_2919231 : Nat := 4983230072969 + 3 ^ 40 * 2919231 * 2
def baseEnd_2919231 : Nat := 1498968644505373228987207

theorem tailTrace_2919231 : CollatzResearch.WordTrace tailWord_2919231 prefixEnd_2919231 1498968644505373228987207 := by
  unfold tailWord_2919231
  simp only [CollatzResearch.WordTrace]
  refine ⟨106473101687132126807125547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70982067791421417871417031 106473101687132126807125547)
  ·
    refine ⟨159709652530698190210688321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106473101687132126807125547 159709652530698190210688321)
    ·
      refine ⟨119782239398023642658016241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159709652530698190210688321 119782239398023642658016241)
      ·
        refine ⟨89836679548517731993512181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119782239398023642658016241 89836679548517731993512181)
        ·
          refine ⟨8422188707673537374391767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89836679548517731993512181 8422188707673537374391767)
          ·
            refine ⟨12633283061510306061587651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8422188707673537374391767 12633283061510306061587651)
            ·
              refine ⟨18949924592265459092381477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12633283061510306061587651 18949924592265459092381477)
              ·
                refine ⟨3553110861049773579821527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18949924592265459092381477 3553110861049773579821527)
                ·
                  refine ⟨5329666291574660369732291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3553110861049773579821527 5329666291574660369732291)
                  ·
                    refine ⟨7994499437361990554598437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5329666291574660369732291 7994499437361990554598437)
                    ·
                      refine ⟨1498968644505373228987207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7994499437361990554598437 1498968644505373228987207)
                      ·
                        rfl

theorem cell23_2919231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 1, 4].length) (baseStart_2919231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919231 prefixEnd_2919231 := by exact prefixLift 2919231
  have htrace : WordTrace (prefixWord ++ tailWord_2919231) baseStart_2919231 baseEnd_2919231 := by
    simpa [prefixWord, tailWord_2919231, baseEnd_2919231] using wordTrace_append hprefix tailTrace_2919231
  have hstable : (prefixWord ++ tailWord_2919231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919231).length < 2 ^ (prefixWord ++ tailWord_2919231).sum := by decide
  have hdescent : baseEnd_2919231 < baseStart_2919231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919285 : List Nat := [1, 3, 4, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_2919285 : Nat := 118140960795 + 2919285 * 2 ^ 59
def prefixEnd_2919285 : Nat := 4983230072969 + 3 ^ 40 * 2919285 * 2
def baseEnd_2919285 : Nat := 1498996372460716017711959

theorem tailTrace_2919285 : CollatzResearch.WordTrace tailWord_2919285 prefixEnd_2919285 1498996372460716017711959 := by
  unfold tailWord_2919285
  simp only [CollatzResearch.WordTrace]
  refine ⟨106475071228936494029591309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70983380819290996019727539 106475071228936494029591309)
  ·
    refine ⟨39928151710851185261096741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106475071228936494029591309 39928151710851185261096741)
    ·
      refine ⟨7486528445784597236455639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39928151710851185261096741 7486528445784597236455639)
      ·
        refine ⟨11229792668676895854683459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7486528445784597236455639 11229792668676895854683459)
        ·
          refine ⟨16844689003015343782025189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11229792668676895854683459 16844689003015343782025189)
          ·
            refine ⟨3158379188065376959129723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16844689003015343782025189 3158379188065376959129723)
            ·
              refine ⟨4737568782098065438694585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3158379188065376959129723 4737568782098065438694585)
              ·
                refine ⟨3553176586573549079020939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4737568782098065438694585 3553176586573549079020939)
                ·
                  refine ⟨5329764879860323618531409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3553176586573549079020939 5329764879860323618531409)
                  ·
                    refine ⟨3997323659895242713898557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5329764879860323618531409 3997323659895242713898557)
                    ·
                      refine ⟨1498996372460716017711959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3997323659895242713898557 1498996372460716017711959)
                      ·
                        rfl

theorem cell23_2919285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_2919285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919285 prefixEnd_2919285 := by exact prefixLift 2919285
  have htrace : WordTrace (prefixWord ++ tailWord_2919285) baseStart_2919285 baseEnd_2919285 := by
    simpa [prefixWord, tailWord_2919285, baseEnd_2919285] using wordTrace_append hprefix tailTrace_2919285
  have hstable : (prefixWord ++ tailWord_2919285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919285).length < 2 ^ (prefixWord ++ tailWord_2919285).sum := by decide
  have hdescent : baseEnd_2919285 < baseStart_2919285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919308 : List Nat := [2, 2, 1, 2, 1, 2, 2, 5, 1, 3, 2]
def baseStart_2919308 : Nat := 118140960795 + 2919308 * 2 ^ 59
def prefixEnd_2919308 : Nat := 4983230072969 + 3 ^ 40 * 2919308 * 2
def baseEnd_2919308 : Nat := 1499008182515769427724353

theorem tailTrace_2919308 : CollatzResearch.WordTrace tailWord_2919308 prefixEnd_2919308 1499008182515769427724353 := by
  unfold tailWord_2919308
  simp only [CollatzResearch.WordTrace]
  refine ⟨53237955053926584478839289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70983940071902112638452385 53237955053926584478839289)
  ·
    refine ⟨39928466290444938359129467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53237955053926584478839289 39928466290444938359129467)
    ·
      refine ⟨59892699435667407538694201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39928466290444938359129467 59892699435667407538694201)
      ·
        refine ⟨44919524576750555654020651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59892699435667407538694201 44919524576750555654020651)
        ·
          refine ⟨67379286865125833481030977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44919524576750555654020651 67379286865125833481030977)
          ·
            refine ⟨50534465148844375110773233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67379286865125833481030977 50534465148844375110773233)
            ·
              refine ⟨37900848861633281333079925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50534465148844375110773233 37900848861633281333079925)
              ·
                refine ⟨3553204580778120124976243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37900848861633281333079925 3553204580778120124976243)
                ·
                  refine ⟨5329806871167180187464365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3553204580778120124976243 5329806871167180187464365)
                  ·
                    refine ⟨1998677576687692570299137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5329806871167180187464365 1998677576687692570299137)
                    ·
                      refine ⟨1499008182515769427724353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1998677576687692570299137 1499008182515769427724353)
                      ·
                        rfl

theorem cell23_2919308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_2919308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919308 prefixEnd_2919308 := by exact prefixLift 2919308
  have htrace : WordTrace (prefixWord ++ tailWord_2919308) baseStart_2919308 baseEnd_2919308 := by
    simpa [prefixWord, tailWord_2919308, baseEnd_2919308] using wordTrace_append hprefix tailTrace_2919308
  have hstable : (prefixWord ++ tailWord_2919308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919308).length < 2 ^ (prefixWord ++ tailWord_2919308).sum := by decide
  have hdescent : baseEnd_2919308 < baseStart_2919308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919321 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 5, 4, 2]
def baseStart_2919321 : Nat := 118140960795 + 2919321 * 2 ^ 59
def prefixEnd_2919321 : Nat := 4983230072969 + 3 ^ 40 * 2919321 * 2
def baseEnd_2919321 : Nat := 1499014857764277876861793

theorem tailTrace_2919321 : CollatzResearch.WordTrace tailWord_2919321 prefixEnd_2919321 1499014857764277876861793 := by
  unfold tailWord_2919321
  simp only [CollatzResearch.WordTrace]
  refine ⟨106476384256806072177901817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70984256171204048118601211 106476384256806072177901817)
  ·
    refine ⟨79857288192604554133426363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106476384256806072177901817 79857288192604554133426363)
    ·
      refine ⟨119785932288906831200139545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79857288192604554133426363 119785932288906831200139545)
      ·
        refine ⟨89839449216680123400104659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119785932288906831200139545 89839449216680123400104659)
        ·
          refine ⟨134759173825020185100156989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89839449216680123400104659 134759173825020185100156989)
          ·
            refine ⟨50534690184382569412558871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134759173825020185100156989 50534690184382569412558871)
            ·
              refine ⟨75802035276573854118838307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50534690184382569412558871 75802035276573854118838307)
              ·
                refine ⟨113703052914860781178257461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75802035276573854118838307 113703052914860781178257461)
                ·
                  refine ⟨10659661210768198235461637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113703052914860781178257461 10659661210768198235461637)
                  ·
                    refine ⟨1998686477019037169149057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10659661210768198235461637 1998686477019037169149057)
                    ·
                      refine ⟨1499014857764277876861793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1998686477019037169149057 1499014857764277876861793)
                      ·
                        rfl

theorem cell23_2919321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 4, 2].length) (baseStart_2919321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919321 prefixEnd_2919321 := by exact prefixLift 2919321
  have htrace : WordTrace (prefixWord ++ tailWord_2919321) baseStart_2919321 baseEnd_2919321 := by
    simpa [prefixWord, tailWord_2919321, baseEnd_2919321] using wordTrace_append hprefix tailTrace_2919321
  have hstable : (prefixWord ++ tailWord_2919321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919321).length < 2 ^ (prefixWord ++ tailWord_2919321).sum := by decide
  have hdescent : baseEnd_2919321 < baseStart_2919321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919366 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_2919366 : Nat := 118140960795 + 2919366 * 2 ^ 59
def prefixEnd_2919366 : Nat := 4983230072969 + 3 ^ 40 * 2919366 * 2
def baseEnd_2919366 : Nat := 1499037964393730200799087

theorem tailTrace_2919366 : CollatzResearch.WordTrace tailWord_2919366 prefixEnd_2919366 1499037964393730200799087 := by
  unfold tailWord_2919366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3327438298176345151977811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70985350361095363242193301 3327438298176345151977811)
  ·
    refine ⟨4991157447264517727966717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3327438298176345151977811 4991157447264517727966717)
    ·
      refine ⟨1871684042724194147987519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4991157447264517727966717 1871684042724194147987519)
      ·
        refine ⟨2807526064086291221981279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1871684042724194147987519 2807526064086291221981279)
        ·
          refine ⟨4211289096129436832971919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2807526064086291221981279 4211289096129436832971919)
          ·
            refine ⟨6316933644194155249457879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4211289096129436832971919 6316933644194155249457879)
            ·
              refine ⟨9475400466291232874186819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6316933644194155249457879 9475400466291232874186819)
              ·
                refine ⟨14213100699436849311280229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9475400466291232874186819 14213100699436849311280229)
                ·
                  refine ⟨2664956381144409245865043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14213100699436849311280229 2664956381144409245865043)
                  ·
                    refine ⟨3997434571716613868797565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2664956381144409245865043 3997434571716613868797565)
                    ·
                      refine ⟨1499037964393730200799087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3997434571716613868797565 1499037964393730200799087)
                      ·
                        rfl

theorem cell23_2919366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_2919366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919366 prefixEnd_2919366 := by exact prefixLift 2919366
  have htrace : WordTrace (prefixWord ++ tailWord_2919366) baseStart_2919366 baseEnd_2919366 := by
    simpa [prefixWord, tailWord_2919366, baseEnd_2919366] using wordTrace_append hprefix tailTrace_2919366
  have hstable : (prefixWord ++ tailWord_2919366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919366).length < 2 ^ (prefixWord ++ tailWord_2919366).sum := by decide
  have hdescent : baseEnd_2919366 < baseStart_2919366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919371 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 3]
def baseStart_2919371 : Nat := 118140960795 + 2919371 * 2 ^ 59
def prefixEnd_2919371 : Nat := 4983230072969 + 3 ^ 40 * 2919371 * 2
def baseEnd_2919371 : Nat := 1499040531797002681236563

theorem tailTrace_2919371 : CollatzResearch.WordTrace tailWord_2919371 prefixEnd_2919371 1499040531797002681236563 := by
  unfold tailWord_2919371
  simp only [CollatzResearch.WordTrace]
  refine ⟨106478207906624930717221967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70985471937749953811481311 106478207906624930717221967)
  ·
    refine ⟨159717311859937396075832951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106478207906624930717221967 159717311859937396075832951)
    ·
      refine ⟨239575967789906094113749427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159717311859937396075832951 239575967789906094113749427)
      ·
        refine ⟨359363951684859141170624141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239575967789906094113749427 359363951684859141170624141)
        ·
          refine ⟨134761481881822177938984053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359363951684859141170624141 134761481881822177938984053)
          ·
            refine ⟨12633888926420829181779755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134761481881822177938984053 12633888926420829181779755)
            ·
              refine ⟨18950833389631243772669633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12633888926420829181779755 18950833389631243772669633)
              ·
                refine ⟨14213125042223432829502225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18950833389631243772669633 14213125042223432829502225)
                ·
                  refine ⟨10659843781667574622126669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14213125042223432829502225 10659843781667574622126669)
                  ·
                    refine ⟨3997441418125340483297501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10659843781667574622126669 3997441418125340483297501)
                    ·
                      refine ⟨1499040531797002681236563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3997441418125340483297501 1499040531797002681236563)
                      ·
                        rfl

theorem cell23_2919371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 3].length) (baseStart_2919371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919371 prefixEnd_2919371 := by exact prefixLift 2919371
  have htrace : WordTrace (prefixWord ++ tailWord_2919371) baseStart_2919371 baseEnd_2919371 := by
    simpa [prefixWord, tailWord_2919371, baseEnd_2919371] using wordTrace_append hprefix tailTrace_2919371
  have hstable : (prefixWord ++ tailWord_2919371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919371).length < 2 ^ (prefixWord ++ tailWord_2919371).sum := by decide
  have hdescent : baseEnd_2919371 < baseStart_2919371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919378 : List Nat := [3, 2, 2, 3, 1, 2, 2, 1, 7]
def baseStart_2919378 : Nat := 118140960795 + 2919378 * 2 ^ 59
def prefixEnd_2919378 : Nat := 4983230072969 + 3 ^ 40 * 2919378 * 2
def baseEnd_2919378 : Nat := 166560458462398239316559

theorem tailTrace_2919378 : CollatzResearch.WordTrace tailWord_2919378 prefixEnd_2919378 166560458462398239316559 := by
  unfold tailWord_2919378
  simp only [CollatzResearch.WordTrace]
  refine ⟨26619615804399892728181697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70985642145066380608484525 26619615804399892728181697)
  ·
    refine ⟨19964711853299919546136273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26619615804399892728181697 19964711853299919546136273)
    ·
      refine ⟨14973533889974939659602205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19964711853299919546136273 14973533889974939659602205)
      ·
        refine ⟨5615075208740602372350827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14973533889974939659602205 5615075208740602372350827)
        ·
          refine ⟨8422612813110903558526241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5615075208740602372350827 8422612813110903558526241)
          ·
            refine ⟨6316959609833177668894681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8422612813110903558526241 6316959609833177668894681)
            ·
              refine ⟨4737719707374883251671011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6316959609833177668894681 4737719707374883251671011)
              ·
                refine ⟨7106579561062324877506517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4737719707374883251671011 7106579561062324877506517)
                ·
                  refine ⟨166560458462398239316559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7106579561062324877506517 166560458462398239316559)
                  ·
                    rfl

theorem cell23_2919378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_2919378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919378 prefixEnd_2919378 := by exact prefixLift 2919378
  have htrace : WordTrace (prefixWord ++ tailWord_2919378) baseStart_2919378 baseEnd_2919378 := by
    simpa [prefixWord, tailWord_2919378, baseEnd_2919378] using wordTrace_append hprefix tailTrace_2919378
  have hstable : (prefixWord ++ tailWord_2919378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919378).length < 2 ^ (prefixWord ++ tailWord_2919378).sum := by decide
  have hdescent : baseEnd_2919378 < baseStart_2919378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919389 : List Nat := [1, 4, 3, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_2919389 : Nat := 118140960795 + 2919389 * 2 ^ 59
def prefixEnd_2919389 : Nat := 4983230072969 + 3 ^ 40 * 2919389 * 2
def baseEnd_2919389 : Nat := 1499049774448783610811481

theorem tailTrace_2919389 : CollatzResearch.WordTrace tailWord_2919389 prefixEnd_2919389 1499049774448783610811481 := by
  unfold tailWord_2919389
  simp only [CollatzResearch.WordTrace]
  refine ⟨106478864420559719791377221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70985909613706479860918147 106478864420559719791377221)
  ·
    refine ⟨19964787078854947460883229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106478864420559719791377221 19964787078854947460883229)
    ·
      refine ⟨7486795154570605297831211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19964787078854947460883229 7486795154570605297831211)
      ·
        refine ⟨11230192731855907946746817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7486795154570605297831211 11230192731855907946746817)
        ·
          refine ⟨8422644548891930960060113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11230192731855907946746817 8422644548891930960060113)
          ·
            refine ⟨6316983411668948220045085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8422644548891930960060113 6316983411668948220045085)
            ·
              refine ⟨2368868779375855582516907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6316983411668948220045085 2368868779375855582516907)
              ·
                refine ⟨3553303169063783373775361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2368868779375855582516907 3553303169063783373775361)
                ·
                  refine ⟨2664977376797837530331521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3553303169063783373775361 2664977376797837530331521)
                  ·
                    refine ⟨1998733032598378147748641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2664977376797837530331521 1998733032598378147748641)
                    ·
                      refine ⟨1499049774448783610811481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1998733032598378147748641 1499049774448783610811481)
                      ·
                        rfl

theorem cell23_2919389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_2919389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919389 prefixEnd_2919389 := by exact prefixLift 2919389
  have htrace : WordTrace (prefixWord ++ tailWord_2919389) baseStart_2919389 baseEnd_2919389 := by
    simpa [prefixWord, tailWord_2919389, baseEnd_2919389] using wordTrace_append hprefix tailTrace_2919389
  have hstable : (prefixWord ++ tailWord_2919389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919389).length < 2 ^ (prefixWord ++ tailWord_2919389).sum := by decide
  have hdescent : baseEnd_2919389 < baseStart_2919389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919522 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_2919522 : Nat := 118140960795 + 2919522 * 2 ^ 59
def prefixEnd_2919522 : Nat := 4983230072969 + 3 ^ 40 * 2919522 * 2
def baseEnd_2919522 : Nat := 1499118067375831590448369

theorem tailTrace_2919522 : CollatzResearch.WordTrace tailWord_2919522 prefixEnd_2919522 1499118067375831590448369 := by
  unfold tailWord_2919522
  simp only [CollatzResearch.WordTrace]
  refine ⟨26620928832269470876492205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70989143552718589003979213 26620928832269470876492205)
  ·
    refine ⟨9982848312101051578684577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26620928832269470876492205 9982848312101051578684577)
    ·
      refine ⟨7487136234075788684013433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9982848312101051578684577 7487136234075788684013433)
      ·
        refine ⟨5615352175556841513010075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7487136234075788684013433 5615352175556841513010075)
        ·
          refine ⟨8423028263335262269515113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5615352175556841513010075 8423028263335262269515113)
          ·
            refine ⟨6317271197501446702136335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8423028263335262269515113 6317271197501446702136335)
            ·
              refine ⟨9475906796252170053204503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6317271197501446702136335 9475906796252170053204503)
              ·
                refine ⟨14213860194378255079806755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9475906796252170053204503 14213860194378255079806755)
                ·
                  refine ⟨21320790291567382619710133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14213860194378255079806755 21320790291567382619710133)
                  ·
                    refine ⟨1998824089834442120597825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21320790291567382619710133 1998824089834442120597825)
                    ·
                      refine ⟨1499118067375831590448369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1998824089834442120597825 1499118067375831590448369)
                      ·
                        rfl

theorem cell23_2919522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_2919522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919522 prefixEnd_2919522 := by exact prefixLift 2919522
  have htrace : WordTrace (prefixWord ++ tailWord_2919522) baseStart_2919522 baseEnd_2919522 := by
    simpa [prefixWord, tailWord_2919522, baseEnd_2919522] using wordTrace_append hprefix tailTrace_2919522
  have hstable : (prefixWord ++ tailWord_2919522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919522).length < 2 ^ (prefixWord ++ tailWord_2919522).sum := by decide
  have hdescent : baseEnd_2919522 < baseStart_2919522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919535 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 5, 2, 2]
def baseStart_2919535 : Nat := 118140960795 + 2919535 * 2 ^ 59
def prefixEnd_2919535 : Nat := 4983230072969 + 3 ^ 40 * 2919535 * 2
def baseEnd_2919535 : Nat := 1499124742624340039585809

theorem tailTrace_2919535 : CollatzResearch.WordTrace tailWord_2919535 prefixEnd_2919535 1499124742624340039585809 := by
  unfold tailWord_2919535
  simp only [CollatzResearch.WordTrace]
  refine ⟨106484189478030786726192059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70989459652020524484128039 106484189478030786726192059)
  ·
    refine ⟨159726284217046180089288089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106484189478030786726192059 159726284217046180089288089)
    ·
      refine ⟨119794713162784635066966067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159726284217046180089288089 119794713162784635066966067)
      ·
        refine ⟨179692069744176952600449101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119794713162784635066966067 179692069744176952600449101)
        ·
          refine ⟨67384526154066357225168413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179692069744176952600449101 67384526154066357225168413)
          ·
            refine ⟨25269197307774883959438155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67384526154066357225168413 25269197307774883959438155)
            ·
              refine ⟨37903795961662325939157233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25269197307774883959438155 37903795961662325939157233)
              ·
                refine ⟨28427846971246744454367925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37903795961662325939157233 28427846971246744454367925)
                ·
                  refine ⟨2665110653554382292596993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28427846971246744454367925 2665110653554382292596993)
                  ·
                    refine ⟨1998832990165786719447745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2665110653554382292596993 1998832990165786719447745)
                    ·
                      refine ⟨1499124742624340039585809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1998832990165786719447745 1499124742624340039585809)
                      ·
                        rfl

theorem cell23_2919535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 2, 2].length) (baseStart_2919535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919535 prefixEnd_2919535 := by exact prefixLift 2919535
  have htrace : WordTrace (prefixWord ++ tailWord_2919535) baseStart_2919535 baseEnd_2919535 := by
    simpa [prefixWord, tailWord_2919535, baseEnd_2919535] using wordTrace_append hprefix tailTrace_2919535
  have hstable : (prefixWord ++ tailWord_2919535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919535).length < 2 ^ (prefixWord ++ tailWord_2919535).sum := by decide
  have hdescent : baseEnd_2919535 < baseStart_2919535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919538 : List Nat := [3, 2, 1, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_2919538 : Nat := 118140960795 + 2919538 * 2 ^ 59
def prefixEnd_2919538 : Nat := 4983230072969 + 3 ^ 40 * 2919538 * 2
def baseEnd_2919538 : Nat := 1499126283066303527848295

theorem tailTrace_2919538 : CollatzResearch.WordTrace tailWord_2919538 prefixEnd_2919538 1499126283066303527848295 := by
  unfold tailWord_2919538
  simp only [CollatzResearch.WordTrace]
  refine ⟨26621074724254979559637817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70989532598013278825700845 26621074724254979559637817)
  ·
    refine ⟨19965806043191234669728363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26621074724254979559637817 19965806043191234669728363)
    ·
      refine ⟨29948709064786852004592545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19965806043191234669728363 29948709064786852004592545)
      ·
        refine ⟨22461531798590139003444409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29948709064786852004592545 22461531798590139003444409)
        ·
          refine ⟨16846148848942604252583307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22461531798590139003444409 16846148848942604252583307)
          ·
            refine ⟨25269223273413906378874961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16846148848942604252583307 25269223273413906378874961)
            ·
              refine ⟨18951917455060429784156221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25269223273413906378874961 18951917455060429784156221)
              ·
                refine ⟨7106969045647661169058583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18951917455060429784156221 7106969045647661169058583)
                ·
                  refine ⟨10660453568471491753587875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7106969045647661169058583 10660453568471491753587875)
                  ·
                    refine ⟨15990680352707237630381813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10660453568471491753587875 15990680352707237630381813)
                    ·
                      refine ⟨1499126283066303527848295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15990680352707237630381813 1499126283066303527848295)
                      ·
                        rfl

theorem cell23_2919538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_2919538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919538 prefixEnd_2919538 := by exact prefixLift 2919538
  have htrace : WordTrace (prefixWord ++ tailWord_2919538) baseStart_2919538 baseEnd_2919538 := by
    simpa [prefixWord, tailWord_2919538, baseEnd_2919538] using wordTrace_append hprefix tailTrace_2919538
  have hstable : (prefixWord ++ tailWord_2919538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919538).length < 2 ^ (prefixWord ++ tailWord_2919538).sum := by decide
  have hdescent : baseEnd_2919538 < baseStart_2919538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919545 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 4, 4]
def baseStart_2919545 : Nat := 118140960795 + 2919545 * 2 ^ 59
def prefixEnd_2919545 : Nat := 4983230072969 + 3 ^ 40 * 2919545 * 2
def baseEnd_2919545 : Nat := 499709959143628333486921

theorem tailTrace_2919545 : CollatzResearch.WordTrace tailWord_2919545 prefixEnd_2919545 499709959143628333486921 := by
  unfold tailWord_2919545
  simp only [CollatzResearch.WordTrace]
  refine ⟨106484554207994558434056089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70989702805329705622704059 106484554207994558434056089)
  ·
    refine ⟨79863415655995918825542067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106484554207994558434056089 79863415655995918825542067)
    ·
      refine ⟨119795123483993878238313101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79863415655995918825542067 119795123483993878238313101)
      ·
        refine ⟨44923171306497704339367413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119795123483993878238313101 44923171306497704339367413)
        ·
          refine ⟨4211547309984159781815695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44923171306497704339367413 4211547309984159781815695)
          ·
            refine ⟨6317320964976239672723543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4211547309984159781815695 6317320964976239672723543)
            ·
              refine ⟨9475981447464359509085315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6317320964976239672723543 9475981447464359509085315)
              ·
                refine ⟨14213972171196539263627973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9475981447464359509085315 14213972171196539263627973)
                ·
                  refine ⟨2665119782099351111930245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14213972171196539263627973 2665119782099351111930245)
                  ·
                    refine ⟨499709959143628333486921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2665119782099351111930245 499709959143628333486921)
                    ·
                      rfl

theorem cell23_2919545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 4].length) (baseStart_2919545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919545 prefixEnd_2919545 := by exact prefixLift 2919545
  have htrace : WordTrace (prefixWord ++ tailWord_2919545) baseStart_2919545 baseEnd_2919545 := by
    simpa [prefixWord, tailWord_2919545, baseEnd_2919545] using wordTrace_append hprefix tailTrace_2919545
  have hstable : (prefixWord ++ tailWord_2919545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919545).length < 2 ^ (prefixWord ++ tailWord_2919545).sum := by decide
  have hdescent : baseEnd_2919545 < baseStart_2919545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919562 : List Nat := [3, 1, 2, 3, 1, 1, 5, 1, 2, 4]
def baseStart_2919562 : Nat := 118140960795 + 2919562 * 2 ^ 59
def prefixEnd_2919562 : Nat := 4983230072969 + 3 ^ 40 * 2919562 * 2
def baseEnd_2919562 : Nat := 499712868867337144649395

theorem tailTrace_2919562 : CollatzResearch.WordTrace tailWord_2919562 prefixEnd_2919562 499712868867337144649395 := by
  unfold tailWord_2919562
  simp only [CollatzResearch.WordTrace]
  refine ⟨26621293562233242584356235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70990116165955313558283293 26621293562233242584356235)
  ·
    refine ⟨39931940343349863876534353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26621293562233242584356235 39931940343349863876534353)
    ·
      refine ⟨29948955257512397907400765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39931940343349863876534353 29948955257512397907400765)
      ·
        refine ⟨11230858221567149215275287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29948955257512397907400765 11230858221567149215275287)
        ·
          refine ⟨16846287332350723822912931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11230858221567149215275287 16846287332350723822912931)
          ·
            refine ⟨25269430998526085734369397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16846287332350723822912931 25269430998526085734369397)
            ·
              refine ⟨2369009156111820537597131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25269430998526085734369397 2369009156111820537597131)
              ·
                refine ⟨3553513734167730806395697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2369009156111820537597131 3553513734167730806395697)
                ·
                  refine ⟨2665135300625798104796773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3553513734167730806395697 2665135300625798104796773)
                  ·
                    refine ⟨499712868867337144649395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2665135300625798104796773 499712868867337144649395)
                    ·
                      rfl

theorem cell23_2919562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_2919562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919562 prefixEnd_2919562 := by exact prefixLift 2919562
  have htrace : WordTrace (prefixWord ++ tailWord_2919562) baseStart_2919562 baseEnd_2919562 := by
    simpa [prefixWord, tailWord_2919562, baseEnd_2919562] using wordTrace_append hprefix tailTrace_2919562
  have hstable : (prefixWord ++ tailWord_2919562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919562).length < 2 ^ (prefixWord ++ tailWord_2919562).sum := by decide
  have hdescent : baseEnd_2919562 < baseStart_2919562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919568 : List Nat := [2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 3]
def baseStart_2919568 : Nat := 118140960795 + 2919568 * 2 ^ 59
def prefixEnd_2919568 : Nat := 4983230072969 + 3 ^ 40 * 2919568 * 2
def baseEnd_2919568 : Nat := 1499141687485938410473157

theorem tailTrace_2919568 : CollatzResearch.WordTrace tailWord_2919568 prefixEnd_2919568 1499141687485938410473157 := by
  unfold tailWord_2919568
  simp only [CollatzResearch.WordTrace]
  refine ⟨53242696543455616681071679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70990262057940822241428905 53242696543455616681071679)
  ·
    refine ⟨79864044815183425021607519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53242696543455616681071679 79864044815183425021607519)
    ·
      refine ⟨119796067222775137532411279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79864044815183425021607519 119796067222775137532411279)
      ·
        refine ⟨179694100834162706298616919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119796067222775137532411279 179694100834162706298616919)
        ·
          refine ⟨269541151251244059447925379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179694100834162706298616919 269541151251244059447925379)
          ·
            refine ⟨404311726876866089171888069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269541151251244059447925379 404311726876866089171888069)
            ·
              refine ⟨75808448789412391719729013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 404311726876866089171888069 75808448789412391719729013)
              ·
                refine ⟨7107042074007411723724595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75808448789412391719729013 7107042074007411723724595)
                ·
                  refine ⟨10660563111011117585586893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7107042074007411723724595 10660563111011117585586893)
                  ·
                    refine ⟨3997711166629169094595085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10660563111011117585586893 3997711166629169094595085)
                    ·
                      refine ⟨1499141687485938410473157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3997711166629169094595085 1499141687485938410473157)
                      ·
                        rfl

theorem cell23_2919568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 3].length) (baseStart_2919568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919568 prefixEnd_2919568 := by exact prefixLift 2919568
  have htrace : WordTrace (prefixWord ++ tailWord_2919568) baseStart_2919568 baseEnd_2919568 := by
    simpa [prefixWord, tailWord_2919568, baseEnd_2919568] using wordTrace_append hprefix tailTrace_2919568
  have hstable : (prefixWord ++ tailWord_2919568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919568).length < 2 ^ (prefixWord ++ tailWord_2919568).sum := by decide
  have hdescent : baseEnd_2919568 < baseStart_2919568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919571 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 2, 7]
def baseStart_2919571 : Nat := 118140960795 + 2919571 * 2 ^ 59
def prefixEnd_2919571 : Nat := 4983230072969 + 3 ^ 40 * 2919571 * 2
def baseEnd_2919571 : Nat := 499714409309300632911881

theorem tailTrace_2919571 : CollatzResearch.WordTrace tailWord_2919571 prefixEnd_2919571 499714409309300632911881 := by
  unfold tailWord_2919571
  simp only [CollatzResearch.WordTrace]
  refine ⟨106485502505900364874502567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70990335003933576583001711 106485502505900364874502567)
  ·
    refine ⟨159728253758850547311753851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106485502505900364874502567 159728253758850547311753851)
    ·
      refine ⟨239592380638275820967630777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159728253758850547311753851 239592380638275820967630777)
      ·
        refine ⟨179694285478706865725723083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239592380638275820967630777 179694285478706865725723083)
        ·
          refine ⟨269541428218060298588584625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179694285478706865725723083 269541428218060298588584625)
          ·
            refine ⟨202156071163545223941438469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269541428218060298588584625 202156071163545223941438469)
            ·
              refine ⟨37904263343164729489019713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202156071163545223941438469 37904263343164729489019713)
              ·
                refine ⟨28428197507373547116764785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37904263343164729489019713 28428197507373547116764785)
                ·
                  refine ⟨21321148130530160337573589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28428197507373547116764785 21321148130530160337573589)
                  ·
                    refine ⟨499714409309300632911881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21321148130530160337573589 499714409309300632911881)
                    ·
                      rfl

theorem cell23_2919571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 7].length) (baseStart_2919571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919571 prefixEnd_2919571 := by exact prefixLift 2919571
  have htrace : WordTrace (prefixWord ++ tailWord_2919571) baseStart_2919571 baseEnd_2919571 := by
    simpa [prefixWord, tailWord_2919571, baseEnd_2919571] using wordTrace_append hprefix tailTrace_2919571
  have hstable : (prefixWord ++ tailWord_2919571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919571).length < 2 ^ (prefixWord ++ tailWord_2919571).sum := by decide
  have hdescent : baseEnd_2919571 < baseStart_2919571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919575 : List Nat := [1, 1, 3, 3, 3, 3, 2, 7]
def baseStart_2919575 : Nat := 118140960795 + 2919575 * 2 ^ 59
def prefixEnd_2919575 : Nat := 4983230072969 + 3 ^ 40 * 2919575 * 2
def baseEnd_2919575 : Nat := 55523899327797032706875

theorem tailTrace_2919575 : CollatzResearch.WordTrace tailWord_2919575 prefixEnd_2919575 55523899327797032706875 := by
  unfold tailWord_2919575
  simp only [CollatzResearch.WordTrace]
  refine ⟨106485648397885873557648179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70990432265257249038432119 106485648397885873557648179)
  ·
    refine ⟨159728472596828810336472269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106485648397885873557648179 159728472596828810336472269)
    ·
      refine ⟨59898177223810803876177101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159728472596828810336472269 59898177223810803876177101)
      ·
        refine ⟨22461816458929051453566413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59898177223810803876177101 22461816458929051453566413)
        ·
          refine ⟨8423181172098394295087405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22461816458929051453566413 8423181172098394295087405)
          ·
            refine ⟨3158692939536897860657777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8423181172098394295087405 3158692939536897860657777)
            ·
              refine ⟨2369019704652673395493333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3158692939536897860657777 2369019704652673395493333)
              ·
                refine ⟨55523899327797032706875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2369019704652673395493333 55523899327797032706875)
                ·
                  rfl

theorem cell23_2919575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 7].length) (baseStart_2919575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919575 prefixEnd_2919575 := by exact prefixLift 2919575
  have htrace : WordTrace (prefixWord ++ tailWord_2919575) baseStart_2919575 baseEnd_2919575 := by
    simpa [prefixWord, tailWord_2919575, baseEnd_2919575] using wordTrace_append hprefix tailTrace_2919575
  have hstable : (prefixWord ++ tailWord_2919575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919575).length < 2 ^ (prefixWord ++ tailWord_2919575).sum := by decide
  have hdescent : baseEnd_2919575 < baseStart_2919575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919585 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 6, 1, 3]
def baseStart_2919585 : Nat := 118140960795 + 2919585 * 2 ^ 59
def prefixEnd_2919585 : Nat := 4983230072969 + 3 ^ 40 * 2919585 * 2
def baseEnd_2919585 : Nat := 1499150416657064843960579

theorem tailTrace_2919585 : CollatzResearch.WordTrace tailWord_2919585 prefixEnd_2919585 1499150416657064843960579 := by
  unfold tailWord_2919585
  simp only [CollatzResearch.WordTrace]
  refine ⟨106486013127849645265512209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70990675418566430177008139 106486013127849645265512209)
  ·
    refine ⟨79864509845887233949134157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106486013127849645265512209 79864509845887233949134157)
    ·
      refine ⟨29949191192207712730925309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79864509845887233949134157 29949191192207712730925309)
      ·
        refine ⟨11230946697077892274096991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29949191192207712730925309 11230946697077892274096991)
        ·
          refine ⟨16846420045616838411145487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11230946697077892274096991 16846420045616838411145487)
          ·
            refine ⟨25269630068425257616718231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16846420045616838411145487 25269630068425257616718231)
            ·
              refine ⟨37904445102637886425077347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25269630068425257616718231 37904445102637886425077347)
              ·
                refine ⟨56856667653956829637616021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37904445102637886425077347 56856667653956829637616021)
                ·
                  refine ⟨2665156296279226389263251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56856667653956829637616021 2665156296279226389263251)
                  ·
                    refine ⟨3997734444418839583894877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2665156296279226389263251 3997734444418839583894877)
                    ·
                      refine ⟨1499150416657064843960579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3997734444418839583894877 1499150416657064843960579)
                      ·
                        rfl

theorem cell23_2919585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_2919585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919585 prefixEnd_2919585 := by exact prefixLift 2919585
  have htrace : WordTrace (prefixWord ++ tailWord_2919585) baseStart_2919585 baseEnd_2919585 := by
    simpa [prefixWord, tailWord_2919585, baseEnd_2919585] using wordTrace_append hprefix tailTrace_2919585
  have hstable : (prefixWord ++ tailWord_2919585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919585).length < 2 ^ (prefixWord ++ tailWord_2919585).sum := by decide
  have hdescent : baseEnd_2919585 < baseStart_2919585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919659 : List Nat := [1, 1, 1, 1, 2, 7, 2, 2, 2, 2, 2]
def baseStart_2919659 : Nat := 118140960795 + 2919659 * 2 ^ 59
def prefixEnd_2919659 : Nat := 4983230072969 + 3 ^ 40 * 2919659 * 2
def baseEnd_2919659 : Nat := 1499188414225497554435239

theorem tailTrace_2919659 : CollatzResearch.WordTrace tailWord_2919659 prefixEnd_2919659 1499188414225497554435239 := by
  unfold tailWord_2919659
  simp only [CollatzResearch.WordTrace]
  refine ⟨106488712129581555903706031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70992474753054370602470687 106488712129581555903706031)
  ·
    refine ⟨159733068194372333855559047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106488712129581555903706031 159733068194372333855559047)
    ·
      refine ⟨239599602291558500783338571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159733068194372333855559047 239599602291558500783338571)
      ·
        refine ⟨359399403437337751175007857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239599602291558500783338571 359399403437337751175007857)
        ·
          refine ⟨269549552578003313381255893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359399403437337751175007857 269549552578003313381255893)
          ·
            refine ⟨6317567638546952657373185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 269549552578003313381255893 6317567638546952657373185)
            ·
              refine ⟨4738175728910214493029889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6317567638546952657373185 4738175728910214493029889)
              ·
                refine ⟨3553631796682660869772417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4738175728910214493029889 3553631796682660869772417)
                ·
                  refine ⟨2665223847511995652329313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3553631796682660869772417 2665223847511995652329313)
                  ·
                    refine ⟨1998917885633996739246985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2665223847511995652329313 1998917885633996739246985)
                    ·
                      refine ⟨1499188414225497554435239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1998917885633996739246985 1499188414225497554435239)
                      ·
                        rfl

theorem cell23_2919659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 2, 2].length) (baseStart_2919659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919659 prefixEnd_2919659 := by exact prefixLift 2919659
  have htrace : WordTrace (prefixWord ++ tailWord_2919659) baseStart_2919659 baseEnd_2919659 := by
    simpa [prefixWord, tailWord_2919659, baseEnd_2919659] using wordTrace_append hprefix tailTrace_2919659
  have hstable : (prefixWord ++ tailWord_2919659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919659).length < 2 ^ (prefixWord ++ tailWord_2919659).sum := by decide
  have hdescent : baseEnd_2919659 < baseStart_2919659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919682 : List Nat := [3, 4, 1, 1, 3, 1, 1, 2, 7]
def baseStart_2919682 : Nat := 118140960795 + 2919682 * 2 ^ 59
def prefixEnd_2919682 : Nat := 4983230072969 + 3 ^ 40 * 2919682 * 2
def baseEnd_2919682 : Nat := 166577802697838996049737

theorem tailTrace_2919682 : CollatzResearch.WordTrace tailWord_2919682 prefixEnd_2919682 166577802697838996049737 := by
  unfold tailWord_2919682
  simp only [CollatzResearch.WordTrace]
  refine ⟨26622387752124557707948325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70993034005665487221195533 26622387752124557707948325)
  ·
    refine ⟨4991697703523354570240311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26622387752124557707948325 4991697703523354570240311)
    ·
      refine ⟨7487546555285031855360467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4991697703523354570240311 7487546555285031855360467)
      ·
        refine ⟨11231319832927547783040701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7487546555285031855360467 11231319832927547783040701)
        ·
          refine ⟨4211744937347830418640263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11231319832927547783040701 4211744937347830418640263)
          ·
            refine ⟨6317617406021745627960395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4211744937347830418640263 6317617406021745627960395)
            ·
              refine ⟨9476426109032618441940593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6317617406021745627960395 9476426109032618441940593)
              ·
                refine ⟨7107319581774463831455445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9476426109032618441940593 7107319581774463831455445)
                ·
                  refine ⟨166577802697838996049737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7107319581774463831455445 166577802697838996049737)
                  ·
                    rfl

theorem cell23_2919682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_2919682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919682 prefixEnd_2919682 := by exact prefixLift 2919682
  have htrace : WordTrace (prefixWord ++ tailWord_2919682) baseStart_2919682 baseEnd_2919682 := by
    simpa [prefixWord, tailWord_2919682, baseEnd_2919682] using wordTrace_append hprefix tailTrace_2919682
  have hstable : (prefixWord ++ tailWord_2919682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919682).length < 2 ^ (prefixWord ++ tailWord_2919682).sum := by decide
  have hdescent : baseEnd_2919682 < baseStart_2919682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919685 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 2, 5, 2]
def baseStart_2919685 : Nat := 118140960795 + 2919685 * 2 ^ 59
def prefixEnd_2919685 : Nat := 4983230072969 + 3 ^ 40 * 2919685 * 2
def baseEnd_2919685 : Nat := 1499201764722514452710119

theorem tailTrace_2919685 : CollatzResearch.WordTrace tailWord_2919685 prefixEnd_2919685 1499201764722514452710119 := by
  unfold tailWord_2919685
  simp only [CollatzResearch.WordTrace]
  refine ⟨106489660427487362344152509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70993106951658241562768339 106489660427487362344152509)
  ·
    refine ⟨39933622660307760879057191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106489660427487362344152509 39933622660307760879057191)
    ·
      refine ⟨59900433990461641318585787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39933622660307760879057191 59900433990461641318585787)
      ·
        refine ⟨89850650985692461977878681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59900433990461641318585787 89850650985692461977878681)
        ·
          refine ⟨67387988239269346483409011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89850650985692461977878681 67387988239269346483409011)
          ·
            refine ⟨101081982358904019725113517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67387988239269346483409011 101081982358904019725113517)
            ·
              refine ⟨37905743384589007396917569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101081982358904019725113517 37905743384589007396917569)
              ·
                refine ⟨28429307538441755547688177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37905743384589007396917569 28429307538441755547688177)
                ·
                  refine ⟨21321980653831316660766133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28429307538441755547688177 21321980653831316660766133)
                  ·
                    refine ⟨1998935686296685936946825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21321980653831316660766133 1998935686296685936946825)
                    ·
                      refine ⟨1499201764722514452710119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1998935686296685936946825 1499201764722514452710119)
                      ·
                        rfl

theorem cell23_2919685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 5, 2].length) (baseStart_2919685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919685 prefixEnd_2919685 := by exact prefixLift 2919685
  have htrace : WordTrace (prefixWord ++ tailWord_2919685) baseStart_2919685 baseEnd_2919685 := by
    simpa [prefixWord, tailWord_2919685, baseEnd_2919685] using wordTrace_append hprefix tailTrace_2919685
  have hstable : (prefixWord ++ tailWord_2919685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919685).length < 2 ^ (prefixWord ++ tailWord_2919685).sum := by decide
  have hdescent : baseEnd_2919685 < baseStart_2919685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919710 : List Nat := [4, 3, 2, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_2919710 : Nat := 118140960795 + 2919710 * 2 ^ 59
def prefixEnd_2919710 : Nat := 4983230072969 + 3 ^ 40 * 2919710 * 2
def baseEnd_2919710 : Nat := 1499214601738876854897505

theorem tailTrace_2919710 : CollatzResearch.WordTrace tailWord_2919710 prefixEnd_2919710 1499214601738876854897505 := by
  unfold tailWord_2919710
  simp only [CollatzResearch.WordTrace]
  refine ⟨13311321531549598951726573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70993714834931194409208389 13311321531549598951726573)
  ·
    refine ⟨4991745574331099606897465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13311321531549598951726573 4991745574331099606897465)
    ·
      refine ⟨3743809180748324705173099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4991745574331099606897465 3743809180748324705173099)
      ·
        refine ⟨5615713771122487057759649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3743809180748324705173099 5615713771122487057759649)
        ·
          refine ⟨4211785328341865293319737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5615713771122487057759649 4211785328341865293319737)
          ·
            refine ⟨3158838996256398969989803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4211785328341865293319737 3158838996256398969989803)
            ·
              refine ⟨4738258494384598454984705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3158838996256398969989803 4738258494384598454984705)
              ·
                refine ⟨3553693870788448841238529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4738258494384598454984705 3553693870788448841238529)
                ·
                  refine ⟨2665270403091336630928897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3553693870788448841238529 2665270403091336630928897)
                  ·
                    refine ⟨1998952802318502473196673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2665270403091336630928897 1998952802318502473196673)
                    ·
                      refine ⟨1499214601738876854897505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1998952802318502473196673 1499214601738876854897505)
                      ·
                        rfl

theorem cell23_2919710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_2919710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919710 prefixEnd_2919710 := by exact prefixLift 2919710
  have htrace : WordTrace (prefixWord ++ tailWord_2919710) baseStart_2919710 baseEnd_2919710 := by
    simpa [prefixWord, tailWord_2919710, baseEnd_2919710] using wordTrace_append hprefix tailTrace_2919710
  have hstable : (prefixWord ++ tailWord_2919710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919710).length < 2 ^ (prefixWord ++ tailWord_2919710).sum := by decide
  have hdescent : baseEnd_2919710 < baseStart_2919710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919728 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 6]
def baseStart_2919728 : Nat := 118140960795 + 2919728 * 2 ^ 59
def prefixEnd_2919728 : Nat := 4983230072969 + 3 ^ 40 * 2919728 * 2
def baseEnd_2919728 : Nat := 1499223844390657784472421

theorem tailTrace_2919728 : CollatzResearch.WordTrace tailWord_2919728 prefixEnd_2919728 1499223844390657784472421 := by
  unfold tailWord_2919728
  simp only [CollatzResearch.WordTrace]
  refine ⟨53245614383165790343983919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70994152510887720458645225 53245614383165790343983919)
  ·
    refine ⟨79868421574748685515975879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53245614383165790343983919 79868421574748685515975879)
    ·
      refine ⟨119802632362123028273963819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79868421574748685515975879 119802632362123028273963819)
      ·
        refine ⟨179703948543184542410945729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119802632362123028273963819 179703948543184542410945729)
        ·
          refine ⟨134777961407388406808209297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179703948543184542410945729 134777961407388406808209297)
          ·
            refine ⟨101083471055541305106156973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134777961407388406808209297 101083471055541305106156973)
            ·
              refine ⟨37906301645827989414808865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101083471055541305106156973 37906301645827989414808865)
              ·
                refine ⟨28429726234370992061106649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37906301645827989414808865 28429726234370992061106649)
                ·
                  refine ⟨21322294675778244045829987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28429726234370992061106649 21322294675778244045829987)
                  ·
                    refine ⟨31983442013667366068744981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21322294675778244045829987 31983442013667366068744981)
                    ·
                      refine ⟨1499223844390657784472421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31983442013667366068744981 1499223844390657784472421)
                      ·
                        rfl

theorem cell23_2919728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_2919728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919728 prefixEnd_2919728 := by exact prefixLift 2919728
  have htrace : WordTrace (prefixWord ++ tailWord_2919728) baseStart_2919728 baseEnd_2919728 := by
    simpa [prefixWord, tailWord_2919728, baseEnd_2919728] using wordTrace_append hprefix tailTrace_2919728
  have hstable : (prefixWord ++ tailWord_2919728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919728).length < 2 ^ (prefixWord ++ tailWord_2919728).sum := by decide
  have hdescent : baseEnd_2919728 < baseStart_2919728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919742 : List Nat := [4, 2, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_2919742 : Nat := 118140960795 + 2919742 * 2 ^ 59
def prefixEnd_2919742 : Nat := 4983230072969 + 3 ^ 40 * 2919742 * 2
def baseEnd_2919742 : Nat := 499743677706606909899119

theorem tailTrace_2919742 : CollatzResearch.WordTrace tailWord_2919742 prefixEnd_2919742 499743677706606909899119 := by
  unfold tailWord_2919742
  simp only [CollatzResearch.WordTrace]
  refine ⟨13311467423535107634872185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70994492925520574052651653 13311467423535107634872185)
  ·
    refine ⟨9983600567651330726154139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13311467423535107634872185 9983600567651330726154139)
    ·
      refine ⟨14975400851476996089231209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9983600567651330726154139 14975400851476996089231209)
      ·
        refine ⟨11231550638607747066923407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14975400851476996089231209 11231550638607747066923407)
        ·
          refine ⟨16847325957911620600385111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11231550638607747066923407 16847325957911620600385111)
          ·
            refine ⟨25270988936867430900577667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16847325957911620600385111 25270988936867430900577667)
            ·
              refine ⟨37906483405301146350866501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25270988936867430900577667 37906483405301146350866501)
              ·
                refine ⟨7107465638493964940787469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37906483405301146350866501 7107465638493964940787469)
                ·
                  refine ⟨2665299614435236852795301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7107465638493964940787469 2665299614435236852795301)
                  ·
                    refine ⟨499743677706606909899119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2665299614435236852795301 499743677706606909899119)
                    ·
                      rfl

theorem cell23_2919742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_2919742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919742 prefixEnd_2919742 := by exact prefixLift 2919742
  have htrace : WordTrace (prefixWord ++ tailWord_2919742) baseStart_2919742 baseEnd_2919742 := by
    simpa [prefixWord, tailWord_2919742, baseEnd_2919742] using wordTrace_append hprefix tailTrace_2919742
  have hstable : (prefixWord ++ tailWord_2919742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919742).length < 2 ^ (prefixWord ++ tailWord_2919742).sum := by decide
  have hdescent : baseEnd_2919742 < baseStart_2919742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919750 : List Nat := [6, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_2919750 : Nat := 118140960795 + 2919750 * 2 ^ 59
def prefixEnd_2919750 : Nat := 4983230072969 + 3 ^ 40 * 2919750 * 2
def baseEnd_2919750 : Nat := 166581682329450744266369

theorem tailTrace_2919750 : CollatzResearch.WordTrace tailWord_2919750 prefixEnd_2919750 166581682329450744266369 := by
  unfold tailWord_2919750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3327875974132871201414647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70994687448167918963512469 3327875974132871201414647)
  ·
    refine ⟨4991813961199306802121971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3327875974132871201414647 4991813961199306802121971)
    ·
      refine ⟨7487720941798960203182957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4991813961199306802121971 7487720941798960203182957)
      ·
        refine ⟨2807895353174610076193609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7487720941798960203182957 2807895353174610076193609)
        ·
          refine ⟨2105921514880957557145207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2807895353174610076193609 2105921514880957557145207)
          ·
            refine ⟨3158882272321436335717811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2105921514880957557145207 3158882272321436335717811)
            ·
              refine ⟨4738323408482154503576717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3158882272321436335717811 4738323408482154503576717)
              ·
                refine ⟨1776871278180807938841269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4738323408482154503576717 1776871278180807938841269)
                ·
                  refine ⟨166581682329450744266369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1776871278180807938841269 166581682329450744266369)
                  ·
                    rfl

theorem cell23_2919750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_2919750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919750 prefixEnd_2919750 := by exact prefixLift 2919750
  have htrace : WordTrace (prefixWord ++ tailWord_2919750) baseStart_2919750 baseEnd_2919750 := by
    simpa [prefixWord, tailWord_2919750, baseEnd_2919750] using wordTrace_append hprefix tailTrace_2919750
  have hstable : (prefixWord ++ tailWord_2919750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919750).length < 2 ^ (prefixWord ++ tailWord_2919750).sum := by decide
  have hdescent : baseEnd_2919750 < baseStart_2919750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919776 : List Nat := [2, 1, 1, 3, 4, 2, 3, 2, 1, 4]
def baseStart_2919776 : Nat := 118140960795 + 2919776 * 2 ^ 59
def prefixEnd_2919776 : Nat := 4983230072969 + 3 ^ 40 * 2919776 * 2
def baseEnd_2919776 : Nat := 499749497154024532224067

theorem tailTrace_2919776 : CollatzResearch.WordTrace tailWord_2919776 prefixEnd_2919776 499749497154024532224067 := by
  unfold tailWord_2919776
  simp only [CollatzResearch.WordTrace]
  refine ⟨53246489735078842442857591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70995319646771789923810121 53246489735078842442857591)
  ·
    refine ⟨79869734602618263664286387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53246489735078842442857591 79869734602618263664286387)
    ·
      refine ⟨119804601903927395496429581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79869734602618263664286387 119804601903927395496429581)
      ·
        refine ⟨44926725713972773311161093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119804601903927395496429581 44926725713972773311161093)
        ·
          refine ⟨8423761071369894995842705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44926725713972773311161093 8423761071369894995842705)
          ·
            refine ⟨6317820803527421246882029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8423761071369894995842705 6317820803527421246882029)
            ·
              refine ⟨2369182801322782967580761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6317820803527421246882029 2369182801322782967580761)
              ·
                refine ⟨1776887100992087225685571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2369182801322782967580761 1776887100992087225685571)
                ·
                  refine ⟨2665330651488130838528357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776887100992087225685571 2665330651488130838528357)
                  ·
                    refine ⟨499749497154024532224067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2665330651488130838528357 499749497154024532224067)
                    ·
                      rfl

theorem cell23_2919776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 1, 4].length) (baseStart_2919776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919776 prefixEnd_2919776 := by exact prefixLift 2919776
  have htrace : WordTrace (prefixWord ++ tailWord_2919776) baseStart_2919776 baseEnd_2919776 := by
    simpa [prefixWord, tailWord_2919776, baseEnd_2919776] using wordTrace_append hprefix tailTrace_2919776
  have hstable : (prefixWord ++ tailWord_2919776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919776).length < 2 ^ (prefixWord ++ tailWord_2919776).sum := by decide
  have hdescent : baseEnd_2919776 < baseStart_2919776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919789 : List Nat := [1, 5, 1, 1, 1, 5, 2, 1, 6]
def baseStart_2919789 : Nat := 118140960795 + 2919789 * 2 ^ 59
def prefixEnd_2919789 : Nat := 4983230072969 + 3 ^ 40 * 2919789 * 2
def baseEnd_2919789 : Nat := 166583907412286893978849

theorem tailTrace_2919789 : CollatzResearch.WordTrace tailWord_2919789 prefixEnd_2919789 166583907412286893978849 := by
  unfold tailWord_2919789
  simp only [CollatzResearch.WordTrace]
  refine ⟨106493453619110588105938421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70995635746073725403958947 106493453619110588105938421)
  ·
    refine ⟨9983761276791617634931727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106493453619110588105938421 9983761276791617634931727)
    ·
      refine ⟨14975641915187426452397591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9983761276791617634931727 14975641915187426452397591)
      ·
        refine ⟨22463462872781139678596387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14975641915187426452397591 22463462872781139678596387)
        ·
          refine ⟨33695194309171709517894581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22463462872781139678596387 33695194309171709517894581)
          ·
            refine ⟨3158924466484847767302617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33695194309171709517894581 3158924466484847767302617)
            ·
              refine ⟨2369193349863635825476963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3158924466484847767302617 2369193349863635825476963)
              ·
                refine ⟨3553790024795453738215445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2369193349863635825476963 3553790024795453738215445)
                ·
                  refine ⟨166583907412286893978849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3553790024795453738215445 166583907412286893978849)
                  ·
                    rfl

theorem cell23_2919789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_2919789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919789 prefixEnd_2919789 := by exact prefixLift 2919789
  have htrace : WordTrace (prefixWord ++ tailWord_2919789) baseStart_2919789 baseEnd_2919789 := by
    simpa [prefixWord, tailWord_2919789, baseEnd_2919789] using wordTrace_append hprefix tailTrace_2919789
  have hstable : (prefixWord ++ tailWord_2919789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919789).length < 2 ^ (prefixWord ++ tailWord_2919789).sum := by decide
  have hdescent : baseEnd_2919789 < baseStart_2919789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919792 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 4, 3, 2]
def baseStart_2919792 : Nat := 118140960795 + 2919792 * 2 ^ 59
def prefixEnd_2919792 : Nat := 4983230072969 + 3 ^ 40 * 2919792 * 2
def baseEnd_2919792 : Nat := 1499256707152545534072127

theorem tailTrace_2919792 : CollatzResearch.WordTrace tailWord_2919792 prefixEnd_2919792 1499256707152545534072127 := by
  unfold tailWord_2919792
  simp only [CollatzResearch.WordTrace]
  refine ⟨53246781519049859809148815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70995708692066479745531753 53246781519049859809148815)
  ·
    refine ⟨79870172278574789713723223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53246781519049859809148815 79870172278574789713723223)
    ·
      refine ⟨119805258417862184570584835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79870172278574789713723223 119805258417862184570584835)
      ·
        refine ⟨179707887626793276855877253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119805258417862184570584835 179707887626793276855877253)
        ·
          refine ⟨33695228930023739410476985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179707887626793276855877253 33695228930023739410476985)
          ·
            refine ⟨25271421697517804557857739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33695228930023739410476985 25271421697517804557857739)
            ·
              refine ⟨37907132546276706836786609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25271421697517804557857739 37907132546276706836786609)
              ·
                refine ⟨28430349409707530127589957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37907132546276706836786609 28430349409707530127589957)
                ·
                  refine ⟨5330690514320161898923117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28430349409707530127589957 5330690514320161898923117)
                  ·
                    refine ⟨1999008942870060712096169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5330690514320161898923117 1999008942870060712096169)
                    ·
                      refine ⟨1499256707152545534072127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1999008942870060712096169 1499256707152545534072127)
                      ·
                        rfl

theorem cell23_2919792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 4, 3, 2].length) (baseStart_2919792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919792 prefixEnd_2919792 := by exact prefixLift 2919792
  have htrace : WordTrace (prefixWord ++ tailWord_2919792) baseStart_2919792 baseEnd_2919792 := by
    simpa [prefixWord, tailWord_2919792, baseEnd_2919792] using wordTrace_append hprefix tailTrace_2919792
  have hstable : (prefixWord ++ tailWord_2919792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919792).length < 2 ^ (prefixWord ++ tailWord_2919792).sum := by decide
  have hdescent : baseEnd_2919792 < baseStart_2919792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919815 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 3, 6]
def baseStart_2919815 : Nat := 118140960795 + 2919815 * 2 ^ 59
def prefixEnd_2919815 : Nat := 4983230072969 + 3 ^ 40 * 2919815 * 2
def baseEnd_2919815 : Nat := 499756172402532981361507

theorem tailTrace_2919815 : CollatzResearch.WordTrace tailWord_2919815 prefixEnd_2919815 499756172402532981361507 := by
  unfold tailWord_2919815
  simp only [CollatzResearch.WordTrace]
  refine ⟨106494401917016394546384899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70996267944677596364256599 106494401917016394546384899)
  ·
    refine ⟨159741602875524591819577349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106494401917016394546384899 159741602875524591819577349)
    ·
      refine ⟨29951550539160860966170753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159741602875524591819577349 29951550539160860966170753)
      ·
        refine ⟨22463662904370645724628065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29951550539160860966170753 22463662904370645724628065)
        ·
          refine ⟨16847747178277984293471049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22463662904370645724628065 16847747178277984293471049)
          ·
            refine ⟨12635810383708488220103287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16847747178277984293471049 12635810383708488220103287)
            ·
              refine ⟨18953715575562732330154931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12635810383708488220103287 18953715575562732330154931)
              ·
                refine ⟨28430573363344098495232397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18953715575562732330154931 28430573363344098495232397)
                ·
                  refine ⟨10661465011254036935712149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28430573363344098495232397 10661465011254036935712149)
                  ·
                    refine ⟨499756172402532981361507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10661465011254036935712149 499756172402532981361507)
                    ·
                      rfl

theorem cell23_2919815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_2919815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919815 prefixEnd_2919815 := by exact prefixLift 2919815
  have htrace : WordTrace (prefixWord ++ tailWord_2919815) baseStart_2919815 baseEnd_2919815 := by
    simpa [prefixWord, tailWord_2919815, baseEnd_2919815] using wordTrace_append hprefix tailTrace_2919815
  have hstable : (prefixWord ++ tailWord_2919815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919815).length < 2 ^ (prefixWord ++ tailWord_2919815).sum := by decide
  have hdescent : baseEnd_2919815 < baseStart_2919815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919833 : List Nat := [1, 2, 1, 2, 1, 7, 2, 2, 1, 1, 3]
def baseStart_2919833 : Nat := 118140960795 + 2919833 * 2 ^ 59
def prefixEnd_2919833 : Nat := 4983230072969 + 3 ^ 40 * 2919833 * 2
def baseEnd_2919833 : Nat := 1499277759859379873659439

theorem tailTrace_2919833 : CollatzResearch.WordTrace tailWord_2919833 prefixEnd_2919833 1499277759859379873659439 := by
  unfold tailWord_2919833
  simp only [CollatzResearch.WordTrace]
  refine ⟨106495058430951183620540153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70996705620634122413693435 106495058430951183620540153)
  ·
    refine ⟨79871293823213387715405115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106495058430951183620540153 79871293823213387715405115)
    ·
      refine ⟨119806940734820081573107673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79871293823213387715405115 119806940734820081573107673)
      ·
        refine ⟨89855205551115061179830755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119806940734820081573107673 89855205551115061179830755)
        ·
          refine ⟨134782808326672591769746133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89855205551115061179830755 134782808326672591769746133)
          ·
            refine ⟨3158972070156388869603425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 134782808326672591769746133 3158972070156388869603425)
            ·
              refine ⟨2369229052617291652202569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3158972070156388869603425 2369229052617291652202569)
              ·
                refine ⟨1776921789462968739151927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2369229052617291652202569 1776921789462968739151927)
                ·
                  refine ⟨2665382684194453108727891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776921789462968739151927 2665382684194453108727891)
                  ·
                    refine ⟨3998074026291679663091837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2665382684194453108727891 3998074026291679663091837)
                    ·
                      refine ⟨1499277759859379873659439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3998074026291679663091837 1499277759859379873659439)
                      ·
                        rfl

theorem cell23_2919833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 1, 1, 3].length) (baseStart_2919833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919833 prefixEnd_2919833 := by exact prefixLift 2919833
  have htrace : WordTrace (prefixWord ++ tailWord_2919833) baseStart_2919833 baseEnd_2919833 := by
    simpa [prefixWord, tailWord_2919833, baseEnd_2919833] using wordTrace_append hprefix tailTrace_2919833
  have hstable : (prefixWord ++ tailWord_2919833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919833).length < 2 ^ (prefixWord ++ tailWord_2919833).sum := by decide
  have hdescent : baseEnd_2919833 < baseStart_2919833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919872 : List Nat := [2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 3]
def baseStart_2919872 : Nat := 118140960795 + 2919872 * 2 ^ 59
def prefixEnd_2919872 : Nat := 4983230072969 + 3 ^ 40 * 2919872 * 2
def baseEnd_2919872 : Nat := 1499297785604905221071759

theorem tailTrace_2919872 : CollatzResearch.WordTrace tailWord_2919872 prefixEnd_2919872 1499297785604905221071759 := by
  unfold tailWord_2919872
  simp only [CollatzResearch.WordTrace]
  refine ⟨53248240438904946640604935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70997653918539928854139913 53248240438904946640604935)
  ·
    refine ⟨79872360658357419960907403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53248240438904946640604935 79872360658357419960907403)
    ·
      refine ⟨119808540987536129941361105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79872360658357419960907403 119808540987536129941361105)
      ·
        refine ⟨89856405740652097456020829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119808540987536129941361105 89856405740652097456020829)
        ·
          refine ⟨33696152152744536546007811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89856405740652097456020829 33696152152744536546007811)
          ·
            refine ⟨50544228229116804819011717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33696152152744536546007811 50544228229116804819011717)
            ·
              refine ⟨9477042792959400903564697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50544228229116804819011717 9477042792959400903564697)
              ·
                refine ⟨7107782094719550677673523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9477042792959400903564697 7107782094719550677673523)
                ·
                  refine ⟨10661673142079326016510285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7107782094719550677673523 10661673142079326016510285)
                  ·
                    refine ⟨3998127428279747256191357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10661673142079326016510285 3998127428279747256191357)
                    ·
                      refine ⟨1499297785604905221071759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3998127428279747256191357 1499297785604905221071759)
                      ·
                        rfl

theorem cell23_2919872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_2919872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919872 prefixEnd_2919872 := by exact prefixLift 2919872
  have htrace : WordTrace (prefixWord ++ tailWord_2919872) baseStart_2919872 baseEnd_2919872 := by
    simpa [prefixWord, tailWord_2919872, baseEnd_2919872] using wordTrace_append hprefix tailTrace_2919872
  have hstable : (prefixWord ++ tailWord_2919872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919872).length < 2 ^ (prefixWord ++ tailWord_2919872).sum := by decide
  have hdescent : baseEnd_2919872 < baseStart_2919872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919876 : List Nat := [2, 3, 3, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_2919876 : Nat := 118140960795 + 2919876 * 2 ^ 59
def prefixEnd_2919876 : Nat := 4983230072969 + 3 ^ 40 * 2919876 * 2
def baseEnd_2919876 : Nat := 1499299839527523205421741

theorem tailTrace_2919876 : CollatzResearch.WordTrace tailWord_2919876 prefixEnd_2919876 1499299839527523205421741 := by
  unfold tailWord_2919876
  simp only [CollatzResearch.WordTrace]
  refine ⟨53248313384897700982177741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70997751179863601309570321 53248313384897700982177741)
  ·
    refine ⟨19968117519336637868316653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53248313384897700982177741 19968117519336637868316653)
    ·
      refine ⟨7488044069751239200618745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19968117519336637868316653 7488044069751239200618745)
      ·
        refine ⟨5616033052313429400464059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7488044069751239200618745 5616033052313429400464059)
        ·
          refine ⟨8424049578470144100696089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5616033052313429400464059 8424049578470144100696089)
          ·
            refine ⟨6318037183852608075522067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8424049578470144100696089 6318037183852608075522067)
            ·
              refine ⟨9477055775778912113283101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6318037183852608075522067 9477055775778912113283101)
              ·
                refine ⟨3553895915917092042481163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9477055775778912113283101 3553895915917092042481163)
                ·
                  refine ⟨5330843873875638063721745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3553895915917092042481163 5330843873875638063721745)
                  ·
                    refine ⟨3998132905406728547791309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5330843873875638063721745 3998132905406728547791309)
                    ·
                      refine ⟨1499299839527523205421741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3998132905406728547791309 1499299839527523205421741)
                      ·
                        rfl

theorem cell23_2919876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_2919876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919876 prefixEnd_2919876 := by exact prefixLift 2919876
  have htrace : WordTrace (prefixWord ++ tailWord_2919876) baseStart_2919876 baseEnd_2919876 := by
    simpa [prefixWord, tailWord_2919876, baseEnd_2919876] using wordTrace_append hprefix tailTrace_2919876
  have hstable : (prefixWord ++ tailWord_2919876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919876).length < 2 ^ (prefixWord ++ tailWord_2919876).sum := by decide
  have hdescent : baseEnd_2919876 < baseStart_2919876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919895 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 4]
def baseStart_2919895 : Nat := 118140960795 + 2919895 * 2 ^ 59
def prefixEnd_2919895 : Nat := 4983230072969 + 3 ^ 40 * 2919895 * 2
def baseEnd_2919895 : Nat := 1499309595659958631084153

theorem tailTrace_2919895 : CollatzResearch.WordTrace tailWord_2919895 prefixEnd_2919895 1499309595659958631084153 := by
  unfold tailWord_2919895
  simp only [CollatzResearch.WordTrace]
  refine ⟨106497319756726568209297139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70998213171151045472864759 106497319756726568209297139)
  ·
    refine ⟨159745979635089852313945709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106497319756726568209297139 159745979635089852313945709)
    ·
      refine ⟨59904742363158694617729641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159745979635089852313945709 59904742363158694617729641)
      ·
        refine ⟨44928556772369020963297231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59904742363158694617729641 44928556772369020963297231)
        ·
          refine ⟨67392835158553531444945847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44928556772369020963297231 67392835158553531444945847)
          ·
            refine ⟨101089252737830297167418771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67392835158553531444945847 101089252737830297167418771)
            ·
              refine ⟨151633879106745445751128157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101089252737830297167418771 151633879106745445751128157)
              ·
                refine ⟨56862704665029542156673059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151633879106745445751128157 56862704665029542156673059)
                ·
                  refine ⟨85294056997544313235009589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56862704665029542156673059 85294056997544313235009589)
                  ·
                    refine ⟨7996317843519779365782149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85294056997544313235009589 7996317843519779365782149)
                    ·
                      refine ⟨1499309595659958631084153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7996317843519779365782149 1499309595659958631084153)
                      ·
                        rfl

theorem cell23_2919895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_2919895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919895 prefixEnd_2919895 := by exact prefixLift 2919895
  have htrace : WordTrace (prefixWord ++ tailWord_2919895) baseStart_2919895 baseEnd_2919895 := by
    simpa [prefixWord, tailWord_2919895, baseEnd_2919895] using wordTrace_append hprefix tailTrace_2919895
  have hstable : (prefixWord ++ tailWord_2919895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919895).length < 2 ^ (prefixWord ++ tailWord_2919895).sum := by decide
  have hdescent : baseEnd_2919895 < baseStart_2919895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919945 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 1, 2, 7]
def baseStart_2919945 : Nat := 118140960795 + 2919945 * 2 ^ 59
def prefixEnd_2919945 : Nat := 4983230072969 + 3 ^ 40 * 2919945 * 2
def baseEnd_2919945 : Nat := 1499335269692683435458923

theorem tailTrace_2919945 : CollatzResearch.WordTrace tailWord_2919945 prefixEnd_2919945 1499335269692683435458923 := by
  unfold tailWord_2919945
  simp only [CollatzResearch.WordTrace]
  refine ⟨106499143406545426748617289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70999428937696951165744859 106499143406545426748617289)
  ·
    refine ⟨79874357554909070061462967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106499143406545426748617289 79874357554909070061462967)
    ·
      refine ⟨119811536332363605092194451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79874357554909070061462967 119811536332363605092194451)
      ·
        refine ⟨179717304498545407638291677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119811536332363605092194451 179717304498545407638291677)
        ·
          refine ⟨67393989186954527864359379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179717304498545407638291677 67393989186954527864359379)
          ·
            refine ⟨101090983780431791796539069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67393989186954527864359379 101090983780431791796539069)
            ·
              refine ⟨37909118917661921923702151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101090983780431791796539069 37909118917661921923702151)
              ·
                refine ⟨56863678376492882885553227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37909118917661921923702151 56863678376492882885553227)
                ·
                  refine ⟨85295517564739324328329841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56863678376492882885553227 85295517564739324328329841)
                  ·
                    refine ⟨63971638173554493246247381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85295517564739324328329841 63971638173554493246247381)
                    ·
                      refine ⟨1499335269692683435458923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63971638173554493246247381 1499335269692683435458923)
                      ·
                        rfl

theorem cell23_2919945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_2919945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919945 prefixEnd_2919945 := by exact prefixLift 2919945
  have htrace : WordTrace (prefixWord ++ tailWord_2919945) baseStart_2919945 baseEnd_2919945 := by
    simpa [prefixWord, tailWord_2919945, baseEnd_2919945] using wordTrace_append hprefix tailTrace_2919945
  have hstable : (prefixWord ++ tailWord_2919945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919945).length < 2 ^ (prefixWord ++ tailWord_2919945).sum := by decide
  have hdescent : baseEnd_2919945 < baseStart_2919945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919946 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 4, 2, 2]
def baseStart_2919946 : Nat := 118140960795 + 2919946 * 2 ^ 59
def prefixEnd_2919946 : Nat := 4983230072969 + 3 ^ 40 * 2919946 * 2
def baseEnd_2919946 : Nat := 1499335783173337931546419

theorem tailTrace_2919946 : CollatzResearch.WordTrace tailWord_2919946 prefixEnd_2919946 1499335783173337931546419 := by
  unfold tailWord_2919946
  simp only [CollatzResearch.WordTrace]
  refine ⟨26624794969885450979850923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70999453253027869279602461 26624794969885450979850923)
  ·
    refine ⟨39937192454828176469776385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26624794969885450979850923 39937192454828176469776385)
    ·
      refine ⟨29952894341121132352332289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39937192454828176469776385 29952894341121132352332289)
      ·
        refine ⟨22464670755840849264249217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29952894341121132352332289 22464670755840849264249217)
        ·
          refine ⟨16848503066880636948186913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22464670755840849264249217 16848503066880636948186913)
          ·
            refine ⟨12636377300160477711140185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16848503066880636948186913 12636377300160477711140185)
            ·
              refine ⟨9477282975120358283355139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12636377300160477711140185 9477282975120358283355139)
              ·
                refine ⟨14215924462680537425032709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9477282975120358283355139 14215924462680537425032709)
                ·
                  refine ⟨2665485836752600767193633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14215924462680537425032709 2665485836752600767193633)
                  ·
                    refine ⟨1999114377564450575395225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2665485836752600767193633 1999114377564450575395225)
                    ·
                      refine ⟨1499335783173337931546419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1999114377564450575395225 1499335783173337931546419)
                      ·
                        rfl

theorem cell23_2919946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_2919946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919946 prefixEnd_2919946 := by exact prefixLift 2919946
  have htrace : WordTrace (prefixWord ++ tailWord_2919946) baseStart_2919946 baseEnd_2919946 := by
    simpa [prefixWord, tailWord_2919946, baseEnd_2919946] using wordTrace_append hprefix tailTrace_2919946
  have hstable : (prefixWord ++ tailWord_2919946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919946).length < 2 ^ (prefixWord ++ tailWord_2919946).sum := by decide
  have hdescent : baseEnd_2919946 < baseStart_2919946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919962 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3]
def baseStart_2919962 : Nat := 118140960795 + 2919962 * 2 ^ 59
def prefixEnd_2919962 : Nat := 4983230072969 + 3 ^ 40 * 2919962 * 2
def baseEnd_2919962 : Nat := 1499343998863809868946345

theorem tailTrace_2919962 : CollatzResearch.WordTrace tailWord_2919962 prefixEnd_2919962 1499343998863809868946345 := by
  unfold tailWord_2919962
  simp only [CollatzResearch.WordTrace]
  refine ⟨26624940861870959662996535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70999842298322559101324093 26624940861870959662996535)
  ·
    refine ⟨39937411292806439494494803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26624940861870959662996535 39937411292806439494494803)
    ·
      refine ⟨59906116939209659241742205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39937411292806439494494803 59906116939209659241742205)
      ·
        refine ⟨22464793852203622215653327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59906116939209659241742205 22464793852203622215653327)
        ·
          refine ⟨33697190778305433323479991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22464793852203622215653327 33697190778305433323479991)
          ·
            refine ⟨50545786167458149985219987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33697190778305433323479991 50545786167458149985219987)
            ·
              refine ⟨75818679251187224977829981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50545786167458149985219987 75818679251187224977829981)
              ·
                refine ⟨28432004719195209366686243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75818679251187224977829981 28432004719195209366686243)
                ·
                  refine ⟨42648007078792814050029365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28432004719195209366686243 42648007078792814050029365)
                  ·
                    refine ⟨3998250663636826317190253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42648007078792814050029365 3998250663636826317190253)
                    ·
                      refine ⟨1499343998863809868946345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3998250663636826317190253 1499343998863809868946345)
                      ·
                        rfl

theorem cell23_2919962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_2919962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919962 prefixEnd_2919962 := by exact prefixLift 2919962
  have htrace : WordTrace (prefixWord ++ tailWord_2919962) baseStart_2919962 baseEnd_2919962 := by
    simpa [prefixWord, tailWord_2919962, baseEnd_2919962] using wordTrace_append hprefix tailTrace_2919962
  have hstable : (prefixWord ++ tailWord_2919962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919962).length < 2 ^ (prefixWord ++ tailWord_2919962).sum := by decide
  have hdescent : baseEnd_2919962 < baseStart_2919962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2919992 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 1, 2, 5]
def baseStart_2919992 : Nat := 118140960795 + 2919992 * 2 ^ 59
def prefixEnd_2919992 : Nat := 4983230072969 + 3 ^ 40 * 2919992 * 2
def baseEnd_2919992 : Nat := 1499359403283444751571207

theorem tailTrace_2919992 : CollatzResearch.WordTrace tailWord_2919992 prefixEnd_2919992 1499359403283444751571207 := by
  unfold tailWord_2919992
  simp only [CollatzResearch.WordTrace]
  refine ⟨53250428818687576887789115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71000571758250102517052153 53250428818687576887789115)
  ·
    refine ⟨79875643228031365331683673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53250428818687576887789115 79875643228031365331683673)
    ·
      refine ⟨59906732421023523998762755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79875643228031365331683673 59906732421023523998762755)
      ·
        refine ⟨89860098631535285998144133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59906732421023523998762755 89860098631535285998144133)
        ·
          refine ⟨16848768493412866124652025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89860098631535285998144133 16848768493412866124652025)
          ·
            refine ⟨12636576370059649593489019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16848768493412866124652025 12636576370059649593489019)
            ·
              refine ⟨18954864555089474390233529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12636576370059649593489019 18954864555089474390233529)
              ·
                refine ⟨14216148416317105792675147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18954864555089474390233529 14216148416317105792675147)
                ·
                  refine ⟨21324222624475658689012721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14216148416317105792675147 21324222624475658689012721)
                  ·
                    refine ⟨15993166968356744016759541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21324222624475658689012721 15993166968356744016759541)
                    ·
                      refine ⟨1499359403283444751571207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15993166968356744016759541 1499359403283444751571207)
                      ·
                        rfl

theorem cell23_2919992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_2919992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2919992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2919992 prefixEnd_2919992 := by exact prefixLift 2919992
  have htrace : WordTrace (prefixWord ++ tailWord_2919992) baseStart_2919992 baseEnd_2919992 := by
    simpa [prefixWord, tailWord_2919992, baseEnd_2919992] using wordTrace_append hprefix tailTrace_2919992
  have hstable : (prefixWord ++ tailWord_2919992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2919992).length < 2 ^ (prefixWord ++ tailWord_2919992).sum := by decide
  have hdescent : baseEnd_2919992 < baseStart_2919992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2919992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920036 : List Nat := [2, 3, 1, 1, 2, 5, 1, 1, 2, 1, 4]
def baseStart_2920036 : Nat := 118140960795 + 2920036 * 2 ^ 59
def prefixEnd_2920036 : Nat := 4983230072969 + 3 ^ 40 * 2920036 * 2
def baseEnd_2920036 : Nat := 1499381996432242579421005

theorem tailTrace_2920036 : CollatzResearch.WordTrace tailWord_2920036 prefixEnd_2920036 1499381996432242579421005 := by
  unfold tailWord_2920036
  simp only [CollatzResearch.WordTrace]
  refine ⟨53251231224607874645089981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71001641632810499526786641 53251231224607874645089981)
  ·
    refine ⟨19969211709227952991908743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53251231224607874645089981 19969211709227952991908743)
    ·
      refine ⟨29953817563841929487863115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19969211709227952991908743 29953817563841929487863115)
      ·
        refine ⟨44930726345762894231794673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29953817563841929487863115 44930726345762894231794673)
        ·
          refine ⟨33698044759322170673846005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44930726345762894231794673 33698044759322170673846005)
          ·
            refine ⟨3159191696186453500673063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33698044759322170673846005 3159191696186453500673063)
            ·
              refine ⟨4738787544279680251009595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159191696186453500673063 4738787544279680251009595)
              ·
                refine ⟨7108181316419520376514393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4738787544279680251009595 7108181316419520376514393)
                ·
                  refine ⟨5331135987314640282385795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7108181316419520376514393 5331135987314640282385795)
                  ·
                    refine ⟨7996703980971960423578693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5331135987314640282385795 7996703980971960423578693)
                    ·
                      refine ⟨1499381996432242579421005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7996703980971960423578693 1499381996432242579421005)
                      ·
                        rfl

theorem cell23_2920036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_2920036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920036 prefixEnd_2920036 := by exact prefixLift 2920036
  have htrace : WordTrace (prefixWord ++ tailWord_2920036) baseStart_2920036 baseEnd_2920036 := by
    simpa [prefixWord, tailWord_2920036, baseEnd_2920036] using wordTrace_append hprefix tailTrace_2920036
  have hstable : (prefixWord ++ tailWord_2920036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920036).length < 2 ^ (prefixWord ++ tailWord_2920036).sum := by decide
  have hdescent : baseEnd_2920036 < baseStart_2920036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920096 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 1, 5, 2]
def baseStart_2920096 : Nat := 118140960795 + 2920096 * 2 ^ 59
def prefixEnd_2920096 : Nat := 4983230072969 + 3 ^ 40 * 2920096 * 2
def baseEnd_2920096 : Nat := 1499412805271512344670729

theorem tailTrace_2920096 : CollatzResearch.WordTrace tailWord_2920096 prefixEnd_2920096 1499412805271512344670729 := by
  unfold tailWord_2920096
  simp only [CollatzResearch.WordTrace]
  refine ⟨53252325414499189768682071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71003100552665586358242761 53252325414499189768682071)
  ·
    refine ⟨79878488121748784653023107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53252325414499189768682071 79878488121748784653023107)
    ·
      refine ⟨119817732182623176979534661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79878488121748784653023107 119817732182623176979534661)
      ·
        refine ⟨22465824784241845683662749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119817732182623176979534661 22465824784241845683662749)
        ·
          refine ⟨8424684294090692131373531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22465824784241845683662749 8424684294090692131373531)
          ·
            refine ⟨12637026441136038197060297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8424684294090692131373531 12637026441136038197060297)
            ·
              refine ⟨9477769830852028647795223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12637026441136038197060297 9477769830852028647795223)
              ·
                refine ⟨14216654746278042971692835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9477769830852028647795223 14216654746278042971692835)
                ·
                  refine ⟨21324982119417064457539253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14216654746278042971692835 21324982119417064457539253)
                  ·
                    refine ⟨1999217073695349792894305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21324982119417064457539253 1999217073695349792894305)
                    ·
                      refine ⟨1499412805271512344670729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1999217073695349792894305 1499412805271512344670729)
                      ·
                        rfl

theorem cell23_2920096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_2920096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920096 prefixEnd_2920096 := by exact prefixLift 2920096
  have htrace : WordTrace (prefixWord ++ tailWord_2920096) baseStart_2920096 baseEnd_2920096 := by
    simpa [prefixWord, tailWord_2920096, baseEnd_2920096] using wordTrace_append hprefix tailTrace_2920096
  have hstable : (prefixWord ++ tailWord_2920096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920096).length < 2 ^ (prefixWord ++ tailWord_2920096).sum := by decide
  have hdescent : baseEnd_2920096 < baseStart_2920096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920136 : List Nat := [2, 1, 3, 1, 2, 2, 3, 3, 2, 4]
def baseStart_2920136 : Nat := 118140960795 + 2920136 * 2 ^ 59
def prefixEnd_2920136 : Nat := 4983230072969 + 3 ^ 40 * 2920136 * 2
def baseEnd_2920136 : Nat := 499811114832564062723515

theorem tailTrace_2920136 : CollatzResearch.WordTrace tailWord_2920136 prefixEnd_2920136 499811114832564062723515 := by
  unfold tailWord_2920136
  simp only [CollatzResearch.WordTrace]
  refine ⟨53253054874426733184410131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71004073165902310912546841 53253054874426733184410131)
  ·
    refine ⟨79879582311640099776615197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53253054874426733184410131 79879582311640099776615197)
    ·
      refine ⟨29954843366865037416230699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79879582311640099776615197 29954843366865037416230699)
      ·
        refine ⟨44932265050297556124346049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29954843366865037416230699 44932265050297556124346049)
        ·
          refine ⟨33699198787723167093259537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44932265050297556124346049 33699198787723167093259537)
          ·
            refine ⟨25274399090792375319944653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33699198787723167093259537 25274399090792375319944653)
            ·
              refine ⟨9477899659047140744979245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25274399090792375319944653 9477899659047140744979245)
              ·
                refine ⟨3554212372142677779367217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9477899659047140744979245 3554212372142677779367217)
                ·
                  refine ⟨2665659279107008334525413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3554212372142677779367217 2665659279107008334525413)
                  ·
                    refine ⟨499811114832564062723515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2665659279107008334525413 499811114832564062723515)
                    ·
                      rfl

theorem cell23_2920136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_2920136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920136 prefixEnd_2920136 := by exact prefixLift 2920136
  have htrace : WordTrace (prefixWord ++ tailWord_2920136) baseStart_2920136 baseEnd_2920136 := by
    simpa [prefixWord, tailWord_2920136, baseEnd_2920136] using wordTrace_append hprefix tailTrace_2920136
  have hstable : (prefixWord ++ tailWord_2920136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920136).length < 2 ^ (prefixWord ++ tailWord_2920136).sum := by decide
  have hdescent : baseEnd_2920136 < baseStart_2920136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920140 : List Nat := [2, 2, 1, 5, 3, 1, 1, 2, 1, 5]
def baseStart_2920140 : Nat := 118140960795 + 2920140 * 2 ^ 59
def prefixEnd_2920140 : Nat := 4983230072969 + 3 ^ 40 * 2920140 * 2
def baseEnd_2920140 : Nat := 499811799473436724173509

theorem tailTrace_2920140 : CollatzResearch.WordTrace tailWord_2920140 prefixEnd_2920140 499811799473436724173509 := by
  unfold tailWord_2920140
  simp only [CollatzResearch.WordTrace]
  refine ⟨53253127820419487525982937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71004170427225983367977249 53253127820419487525982937)
  ·
    refine ⟨39939845865314615644487203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53253127820419487525982937 39939845865314615644487203)
    ·
      refine ⟨59909768797971923466730805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39939845865314615644487203 59909768797971923466730805)
      ·
        refine ⟨5616540824809867825006013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59909768797971923466730805 5616540824809867825006013)
        ·
          refine ⟨2106202809303700434377255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5616540824809867825006013 2106202809303700434377255)
          ·
            refine ⟨3159304213955550651565883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2106202809303700434377255 3159304213955550651565883)
            ·
              refine ⟨4738956320933325977348825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159304213955550651565883 4738956320933325977348825)
              ·
                refine ⟨3554217240699994483011619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4738956320933325977348825 3554217240699994483011619)
                ·
                  refine ⟨5331325861049991724517429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554217240699994483011619 5331325861049991724517429)
                  ·
                    refine ⟨499811799473436724173509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5331325861049991724517429 499811799473436724173509)
                    ·
                      rfl

theorem cell23_2920140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 1, 5].length) (baseStart_2920140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920140 prefixEnd_2920140 := by exact prefixLift 2920140
  have htrace : WordTrace (prefixWord ++ tailWord_2920140) baseStart_2920140 baseEnd_2920140 := by
    simpa [prefixWord, tailWord_2920140, baseEnd_2920140] using wordTrace_append hprefix tailTrace_2920140
  have hstable : (prefixWord ++ tailWord_2920140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920140).length < 2 ^ (prefixWord ++ tailWord_2920140).sum := by decide
  have hdescent : baseEnd_2920140 < baseStart_2920140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920163 : List Nat := [1, 1, 1, 7, 2, 2, 1, 1, 1, 1, 5]
def baseStart_2920163 : Nat := 118140960795 + 2920163 * 2 ^ 59
def prefixEnd_2920163 : Nat := 4983230072969 + 3 ^ 40 * 2920163 * 2
def baseEnd_2920163 : Nat := 1499447208475363582532921

theorem tailTrace_2920163 : CollatzResearch.WordTrace tailWord_2920163 prefixEnd_2920163 1499447208475363582532921 := by
  unfold tailWord_2920163
  simp only [CollatzResearch.WordTrace]
  refine ⟨106507094519755649980053143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71004729679837099986702095 106507094519755649980053143)
  ·
    refine ⟨159760641779633474970079715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106507094519755649980053143 159760641779633474970079715)
    ·
      refine ⟨239640962669450212455119573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159760641779633474970079715 239640962669450212455119573)
      ·
        refine ⟨5616585062565239354416865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 239640962669450212455119573 5616585062565239354416865)
        ·
          refine ⟨4212438796923929515812649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5616585062565239354416865 4212438796923929515812649)
          ·
            refine ⟨3159329097692947136859487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4212438796923929515812649 3159329097692947136859487)
            ·
              refine ⟨4738993646539420705289231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159329097692947136859487 4738993646539420705289231)
              ·
                refine ⟨7108490469809131057933847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4738993646539420705289231 7108490469809131057933847)
                ·
                  refine ⟨10662735704713696586900771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7108490469809131057933847 10662735704713696586900771)
                  ·
                    refine ⟨15994103557070544880351157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10662735704713696586900771 15994103557070544880351157)
                    ·
                      refine ⟨1499447208475363582532921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15994103557070544880351157 1499447208475363582532921)
                      ·
                        rfl

theorem cell23_2920163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_2920163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920163 prefixEnd_2920163 := by exact prefixLift 2920163
  have htrace : WordTrace (prefixWord ++ tailWord_2920163) baseStart_2920163 baseEnd_2920163 := by
    simpa [prefixWord, tailWord_2920163, baseEnd_2920163] using wordTrace_append hprefix tailTrace_2920163
  have hstable : (prefixWord ++ tailWord_2920163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920163).length < 2 ^ (prefixWord ++ tailWord_2920163).sum := by decide
  have hdescent : baseEnd_2920163 < baseStart_2920163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920177 : List Nat := [1, 2, 2, 2, 2, 3, 4, 2, 1, 2, 2]
def baseStart_2920177 : Nat := 118140960795 + 2920177 * 2 ^ 59
def prefixEnd_2920177 : Nat := 4983230072969 + 3 ^ 40 * 2920177 * 2
def baseEnd_2920177 : Nat := 1499454397204526527757857

theorem tailTrace_2920177 : CollatzResearch.WordTrace tailWord_2920177 prefixEnd_2920177 1499454397204526527757857 := by
  unfold tailWord_2920177
  simp only [CollatzResearch.WordTrace]
  refine ⟨106507605141704930371062785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71005070094469953580708523 106507605141704930371062785)
  ·
    refine ⟨79880703856278697778297089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106507605141704930371062785 79880703856278697778297089)
    ·
      refine ⟨59910527892209023333722817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79880703856278697778297089 59910527892209023333722817)
      ·
        refine ⟨44932895919156767500292113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59910527892209023333722817 44932895919156767500292113)
        ·
          refine ⟨33699671939367575625219085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44932895919156767500292113 33699671939367575625219085)
          ·
            refine ⟨12637376977262840859457157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33699671939367575625219085 12637376977262840859457157)
            ·
              refine ⟨2369508183236782661148217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12637376977262840859457157 2369508183236782661148217)
              ·
                refine ⟨1777131137427586995861163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2369508183236782661148217 1777131137427586995861163)
                ·
                  refine ⟨2665696706141380493791745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1777131137427586995861163 2665696706141380493791745)
                  ·
                    refine ⟨1999272529606035370343809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2665696706141380493791745 1999272529606035370343809)
                    ·
                      refine ⟨1499454397204526527757857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1999272529606035370343809 1499454397204526527757857)
                      ·
                        rfl

theorem cell23_2920177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_2920177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920177 prefixEnd_2920177 := by exact prefixLift 2920177
  have htrace : WordTrace (prefixWord ++ tailWord_2920177) baseStart_2920177 baseEnd_2920177 := by
    simpa [prefixWord, tailWord_2920177, baseEnd_2920177] using wordTrace_append hprefix tailTrace_2920177
  have hstable : (prefixWord ++ tailWord_2920177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920177).length < 2 ^ (prefixWord ++ tailWord_2920177).sum := by decide
  have hdescent : baseEnd_2920177 < baseStart_2920177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920180 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2920180 : Nat := 118140960795 + 2920180 * 2 ^ 59
def prefixEnd_2920180 : Nat := 4983230072969 + 3 ^ 40 * 2920180 * 2
def baseEnd_2920180 : Nat := 1499455937646490016020343

theorem tailTrace_2920180 : CollatzResearch.WordTrace tailWord_2920180 prefixEnd_2920180 1499455937646490016020343 := by
  unfold tailWord_2920180
  simp only [CollatzResearch.WordTrace]
  refine ⟨53253857280347030941710997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71005143040462707922281329 53253857280347030941710997)
  ·
    refine ⟨2496274560016267075392703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53253857280347030941710997 2496274560016267075392703)
    ·
      refine ⟨3744411840024400613089055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2496274560016267075392703 3744411840024400613089055)
      ·
        refine ⟨5616617760036600919633583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3744411840024400613089055 5616617760036600919633583)
        ·
          refine ⟨8424926640054901379450375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5616617760036600919633583 8424926640054901379450375)
          ·
            refine ⟨12637389960082352069175563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8424926640054901379450375 12637389960082352069175563)
            ·
              refine ⟨18956084940123528103763345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12637389960082352069175563 18956084940123528103763345)
              ·
                refine ⟨14217063705092646077822509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18956084940123528103763345 14217063705092646077822509)
                ·
                  refine ⟨5331398889409742279183441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14217063705092646077822509 5331398889409742279183441)
                  ·
                    refine ⟨3998549167057306709387581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5331398889409742279183441 3998549167057306709387581)
                    ·
                      refine ⟨1499455937646490016020343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3998549167057306709387581 1499455937646490016020343)
                      ·
                        rfl

theorem cell23_2920180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2920180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920180 prefixEnd_2920180 := by exact prefixLift 2920180
  have htrace : WordTrace (prefixWord ++ tailWord_2920180) baseStart_2920180 baseEnd_2920180 := by
    simpa [prefixWord, tailWord_2920180, baseEnd_2920180] using wordTrace_append hprefix tailTrace_2920180
  have hstable : (prefixWord ++ tailWord_2920180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920180).length < 2 ^ (prefixWord ++ tailWord_2920180).sum := by decide
  have hdescent : baseEnd_2920180 < baseStart_2920180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920193 : List Nat := [1, 2, 4, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_2920193 : Nat := 118140960795 + 2920193 * 2 ^ 59
def prefixEnd_2920193 : Nat := 4983230072969 + 3 ^ 40 * 2920193 * 2
def baseEnd_2920193 : Nat := 1499462612894998465157783

theorem tailTrace_2920193 : CollatzResearch.WordTrace tailWord_2920193 prefixEnd_2920193 1499462612894998465157783 := by
  unfold tailWord_2920193
  simp only [CollatzResearch.WordTrace]
  refine ⟨106508188709646965103645233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71005459139764643402430155 106508188709646965103645233)
  ·
    refine ⟨79881141532235223827733925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106508188709646965103645233 79881141532235223827733925)
    ·
      refine ⟨14977714037294104467700111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79881141532235223827733925 14977714037294104467700111)
      ·
        refine ⟨22466571055941156701550167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14977714037294104467700111 22466571055941156701550167)
        ·
          refine ⟨33699856583911735052325251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22466571055941156701550167 33699856583911735052325251)
          ·
            refine ⟨50549784875867602578487877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33699856583911735052325251 50549784875867602578487877)
            ·
              refine ⟨9478084664225175483466477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50549784875867602578487877 9478084664225175483466477)
              ·
                refine ⟨3554281749084440806299929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9478084664225175483466477 3554281749084440806299929)
                ·
                  refine ⟨2665711311813330604724947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3554281749084440806299929 2665711311813330604724947)
                  ·
                    refine ⟨3998566967719995907087421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2665711311813330604724947 3998566967719995907087421)
                    ·
                      refine ⟨1499462612894998465157783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3998566967719995907087421 1499462612894998465157783)
                      ·
                        rfl

theorem cell23_2920193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_2920193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920193 prefixEnd_2920193 := by exact prefixLift 2920193
  have htrace : WordTrace (prefixWord ++ tailWord_2920193) baseStart_2920193 baseEnd_2920193 := by
    simpa [prefixWord, tailWord_2920193, baseEnd_2920193] using wordTrace_append hprefix tailTrace_2920193
  have hstable : (prefixWord ++ tailWord_2920193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920193).length < 2 ^ (prefixWord ++ tailWord_2920193).sum := by decide
  have hdescent : baseEnd_2920193 < baseStart_2920193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920198 : List Nat := [6, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_2920198 : Nat := 118140960795 + 2920198 * 2 ^ 59
def prefixEnd_2920198 : Nat := 4983230072969 + 3 ^ 40 * 2920198 * 2
def baseEnd_2920198 : Nat := 1499465180298270945595261

theorem tailTrace_2920198 : CollatzResearch.WordTrace tailWord_2920198 prefixEnd_2920198 1499465180298270945595261 := by
  unfold tailWord_2920198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3328386596082151592424289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71005580716419233971718165 3328386596082151592424289)
  ·
    refine ⟨2496289947061613694318217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3328386596082151592424289 2496289947061613694318217)
    ·
      refine ⟨1872217460296210270738663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2496289947061613694318217 1872217460296210270738663)
      ·
        refine ⟨2808326190444315406107995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1872217460296210270738663 2808326190444315406107995)
        ·
          refine ⟨4212489285666473109161993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2808326190444315406107995 4212489285666473109161993)
          ·
            refine ⟨3159366964249854831871495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4212489285666473109161993 3159366964249854831871495)
            ·
              refine ⟨4739050446374782247807243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159366964249854831871495 4739050446374782247807243)
              ·
                refine ⟨7108575669562173371710865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4739050446374782247807243 7108575669562173371710865)
                ·
                  refine ⟨5331431752171630028783149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7108575669562173371710865 5331431752171630028783149)
                  ·
                    refine ⟨1999286907064361260793681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5331431752171630028783149 1999286907064361260793681)
                    ·
                      refine ⟨1499465180298270945595261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1999286907064361260793681 1499465180298270945595261)
                      ·
                        rfl

theorem cell23_2920198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_2920198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920198 prefixEnd_2920198 := by exact prefixLift 2920198
  have htrace : WordTrace (prefixWord ++ tailWord_2920198) baseStart_2920198 baseEnd_2920198 := by
    simpa [prefixWord, tailWord_2920198, baseEnd_2920198] using wordTrace_append hprefix tailTrace_2920198
  have hstable : (prefixWord ++ tailWord_2920198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920198).length < 2 ^ (prefixWord ++ tailWord_2920198).sum := by decide
  have hdescent : baseEnd_2920198 < baseStart_2920198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920219 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 3]
def baseStart_2920219 : Nat := 118140960795 + 2920219 * 2 ^ 59
def prefixEnd_2920219 : Nat := 4983230072969 + 3 ^ 40 * 2920219 * 2
def baseEnd_2920219 : Nat := 1499475963392015363432663

theorem tailTrace_2920219 : CollatzResearch.WordTrace tailWord_2920219 prefixEnd_2920219 1499475963392015363432663 := by
  unfold tailWord_2920219
  simp only [CollatzResearch.WordTrace]
  refine ⟨106509137007552771544091711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71006091338368514362727807 106509137007552771544091711)
  ·
    refine ⟨159763705511329157316137567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106509137007552771544091711 159763705511329157316137567)
    ·
      refine ⟨239645558266993735974206351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159763705511329157316137567 239645558266993735974206351)
      ·
        refine ⟨359468337400490603961309527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239645558266993735974206351 359468337400490603961309527)
        ·
          refine ⟨539202506100735905941964291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359468337400490603961309527 539202506100735905941964291)
          ·
            refine ⟨808803759151103858912946437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539202506100735905941964291 808803759151103858912946437)
            ·
              refine ⟨151650704840831973546177457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 808803759151103858912946437 151650704840831973546177457)
              ·
                refine ⟨113738028630623980159633093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151650704840831973546177457 113738028630623980159633093)
                ·
                  refine ⟨21325880368241996279931205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113738028630623980159633093 21325880368241996279931205)
                  ·
                    refine ⟨3998602569045374302487101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21325880368241996279931205 3998602569045374302487101)
                    ·
                      refine ⟨1499475963392015363432663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3998602569045374302487101 1499475963392015363432663)
                      ·
                        rfl

theorem cell23_2920219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 3].length) (baseStart_2920219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920219 prefixEnd_2920219 := by exact prefixLift 2920219
  have htrace : WordTrace (prefixWord ++ tailWord_2920219) baseStart_2920219 baseEnd_2920219 := by
    simpa [prefixWord, tailWord_2920219, baseEnd_2920219] using wordTrace_append hprefix tailTrace_2920219
  have hstable : (prefixWord ++ tailWord_2920219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920219).length < 2 ^ (prefixWord ++ tailWord_2920219).sum := by decide
  have hdescent : baseEnd_2920219 < baseStart_2920219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920250 : List Nat := [3, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2]
def baseStart_2920250 : Nat := 118140960795 + 2920250 * 2 ^ 59
def prefixEnd_2920250 : Nat := 4983230072969 + 3 ^ 40 * 2920250 * 2
def baseEnd_2920250 : Nat := 1499491881292304742145021

theorem tailTrace_2920250 : CollatzResearch.WordTrace tailWord_2920250 prefixEnd_2920250 1499491881292304742145021 := by
  unfold tailWord_2920250
  simp only [CollatzResearch.WordTrace]
  refine ⟨26627566917610115959617551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71006845113626975892313469 26627566917610115959617551)
  ·
    refine ⟨39941350376415173939426327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26627566917610115959617551 39941350376415173939426327)
    ·
      refine ⟨59912025564622760909139491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39941350376415173939426327 59912025564622760909139491)
      ·
        refine ⟨89868038346934141363709237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59912025564622760909139491 89868038346934141363709237)
        ·
          refine ⟨8425128595025075752847741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89868038346934141363709237 8425128595025075752847741)
          ·
            refine ⟨3159423223134403407317903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8425128595025075752847741 3159423223134403407317903)
            ·
              refine ⟨4739134834701605110976855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159423223134403407317903 4739134834701605110976855)
              ·
                refine ⟨7108702252052407666465283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4739134834701605110976855 7108702252052407666465283)
                ·
                  refine ⟨10663053378078611499697925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7108702252052407666465283 10663053378078611499697925)
                  ·
                    refine ⟨1999322508389739656193361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10663053378078611499697925 1999322508389739656193361)
                    ·
                      refine ⟨1499491881292304742145021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1999322508389739656193361 1499491881292304742145021)
                      ·
                        rfl

theorem cell23_2920250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2].length) (baseStart_2920250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920250 prefixEnd_2920250 := by exact prefixLift 2920250
  have htrace : WordTrace (prefixWord ++ tailWord_2920250) baseStart_2920250 baseEnd_2920250 := by
    simpa [prefixWord, tailWord_2920250, baseEnd_2920250] using wordTrace_append hprefix tailTrace_2920250
  have hstable : (prefixWord ++ tailWord_2920250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920250).length < 2 ^ (prefixWord ++ tailWord_2920250).sum := by decide
  have hdescent : baseEnd_2920250 < baseStart_2920250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920273 : List Nat := [1, 2, 2, 1, 5, 1, 3, 3, 5]
def baseStart_2920273 : Nat := 118140960795 + 2920273 * 2 ^ 59
def prefixEnd_2920273 : Nat := 4983230072969 + 3 ^ 40 * 2920273 * 2
def baseEnd_2920273 : Nat := 166611521260817572461935

theorem tailTrace_2920273 : CollatzResearch.WordTrace tailWord_2920273 prefixEnd_2920273 166611521260817572461935 := by
  unfold tailWord_2920273
  simp only [CollatzResearch.WordTrace]
  refine ⟨106511106549357138766557473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71007404366238092511038315 106511106549357138766557473)
  ·
    refine ⟨79883329912017854074918105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106511106549357138766557473 79883329912017854074918105)
    ·
      refine ⟨59912497434013390556188579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79883329912017854074918105 59912497434013390556188579)
      ·
        refine ⟨89868746151020085834282869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59912497434013390556188579 89868746151020085834282869)
        ·
          refine ⟨8425194951658133046964019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89868746151020085834282869 8425194951658133046964019)
          ·
            refine ⟨12637792427487199570446029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8425194951658133046964019 12637792427487199570446029)
            ·
              refine ⟨4739172160307699838917261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12637792427487199570446029 4739172160307699838917261)
              ·
                refine ⟨1777189560115387439593973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4739172160307699838917261 1777189560115387439593973)
                ·
                  refine ⟨166611521260817572461935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1777189560115387439593973 166611521260817572461935)
                  ·
                    rfl

theorem cell23_2920273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 5].length) (baseStart_2920273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920273 prefixEnd_2920273 := by exact prefixLift 2920273
  have htrace : WordTrace (prefixWord ++ tailWord_2920273) baseStart_2920273 baseEnd_2920273 := by
    simpa [prefixWord, tailWord_2920273, baseEnd_2920273] using wordTrace_append hprefix tailTrace_2920273
  have hstable : (prefixWord ++ tailWord_2920273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920273).length < 2 ^ (prefixWord ++ tailWord_2920273).sum := by decide
  have hdescent : baseEnd_2920273 < baseStart_2920273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920296 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_2920296 : Nat := 118140960795 + 2920296 * 2 ^ 59
def prefixEnd_2920296 : Nat := 4983230072969 + 3 ^ 40 * 2920296 * 2
def baseEnd_2920296 : Nat := 1499515501402411562169809

theorem tailTrace_2920296 : CollatzResearch.WordTrace tailWord_2920296 prefixEnd_2920296 1499515501402411562169809 := by
  unfold tailWord_2920296
  simp only [CollatzResearch.WordTrace]
  refine ⟨53255972714136906847322371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71007963618849209129763161 53255972714136906847322371)
  ·
    refine ⟨79883959071205360270983557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53255972714136906847322371 79883959071205360270983557)
    ·
      refine ⟨14978242325851005050809417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79883959071205360270983557 14978242325851005050809417)
      ·
        refine ⟨11233681744388253788107063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14978242325851005050809417 11233681744388253788107063)
        ·
          refine ⟨16850522616582380682160595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11233681744388253788107063 16850522616582380682160595)
          ·
            refine ⟨25275783924873571023240893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16850522616582380682160595 25275783924873571023240893)
            ·
              refine ⟨9478418971827589133715335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25275783924873571023240893 9478418971827589133715335)
              ·
                refine ⟨14217628457741383700573003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9478418971827589133715335 14217628457741383700573003)
                ·
                  refine ⟨21326442686612075550859505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14217628457741383700573003 21326442686612075550859505)
                  ·
                    refine ⟨15994832014959056663144629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21326442686612075550859505 15994832014959056663144629)
                    ·
                      refine ⟨1499515501402411562169809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15994832014959056663144629 1499515501402411562169809)
                      ·
                        rfl

theorem cell23_2920296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_2920296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920296 prefixEnd_2920296 := by exact prefixLift 2920296
  have htrace : WordTrace (prefixWord ++ tailWord_2920296) baseStart_2920296 baseEnd_2920296 := by
    simpa [prefixWord, tailWord_2920296, baseEnd_2920296] using wordTrace_append hprefix tailTrace_2920296
  have hstable : (prefixWord ++ tailWord_2920296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920296).length < 2 ^ (prefixWord ++ tailWord_2920296).sum := by decide
  have hdescent : baseEnd_2920296 < baseStart_2920296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920306 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_2920306 : Nat := 118140960795 + 2920306 * 2 ^ 59
def prefixEnd_2920306 : Nat := 4983230072969 + 3 ^ 40 * 2920306 * 2
def baseEnd_2920306 : Nat := 1499520636208956523044763

theorem tailTrace_2920306 : CollatzResearch.WordTrace tailWord_2920306 prefixEnd_2920306 1499520636208956523044763 := by
  unfold tailWord_2920306
  simp only [CollatzResearch.WordTrace]
  refine ⟨26628077539559396350627193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71008206772158390268339181 26628077539559396350627193)
  ·
    refine ⟨19971058154669547262970395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26628077539559396350627193 19971058154669547262970395)
    ·
      refine ⟨29956587232004320894455593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19971058154669547262970395 29956587232004320894455593)
      ·
        refine ⟨22467440424003240670841695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29956587232004320894455593 22467440424003240670841695)
        ·
          refine ⟨33701160636004861006262543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22467440424003240670841695 33701160636004861006262543)
          ·
            refine ⟨50551740954007291509393815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33701160636004861006262543 50551740954007291509393815)
            ·
              refine ⟨75827611431010937264090723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50551740954007291509393815 75827611431010937264090723)
              ·
                refine ⟨113741417146516405896136085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75827611431010937264090723 113741417146516405896136085)
                ·
                  refine ⟨5331628928742956526381379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 113741417146516405896136085 5331628928742956526381379)
                  ·
                    refine ⟨7997443393114434789572069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5331628928742956526381379 7997443393114434789572069)
                    ·
                      refine ⟨1499520636208956523044763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7997443393114434789572069 1499520636208956523044763)
                      ·
                        rfl

theorem cell23_2920306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_2920306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920306 prefixEnd_2920306 := by exact prefixLift 2920306
  have htrace : WordTrace (prefixWord ++ tailWord_2920306) baseStart_2920306 baseEnd_2920306 := by
    simpa [prefixWord, tailWord_2920306, baseEnd_2920306] using wordTrace_append hprefix tailTrace_2920306
  have hstable : (prefixWord ++ tailWord_2920306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920306).length < 2 ^ (prefixWord ++ tailWord_2920306).sum := by decide
  have hdescent : baseEnd_2920306 < baseStart_2920306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920319 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 6]
def baseStart_2920319 : Nat := 118140960795 + 2920319 * 2 ^ 59
def prefixEnd_2920319 : Nat := 4983230072969 + 3 ^ 40 * 2920319 * 2
def baseEnd_2920319 : Nat := 1499527311457464972182203

theorem tailTrace_2920319 : CollatzResearch.WordTrace tailWord_2920319 prefixEnd_2920319 1499527311457464972182203 := by
  unfold tailWord_2920319
  simp only [CollatzResearch.WordTrace]
  refine ⟨106512784307190488622732011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71008522871460325748488007 106512784307190488622732011)
  ·
    refine ⟨159769176460785732934098017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106512784307190488622732011 159769176460785732934098017)
    ·
      refine ⟨119826882345589299700573513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159769176460785732934098017 119826882345589299700573513)
      ·
        refine ⟨89870161759191974775430135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119826882345589299700573513 89870161759191974775430135)
        ·
          refine ⟨134805242638787962163145203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89870161759191974775430135 134805242638787962163145203)
          ·
            refine ⟨202207863958181943244717805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134805242638787962163145203 202207863958181943244717805)
            ·
              refine ⟨75827948984318228716769177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202207863958181943244717805 75827948984318228716769177)
              ·
                refine ⟨56870961738238671537576883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75827948984318228716769177 56870961738238671537576883)
                ·
                  refine ⟨85306442607358007306365325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56870961738238671537576883 85306442607358007306365325)
                  ·
                    refine ⟨31989915977759252739886997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85306442607358007306365325 31989915977759252739886997)
                    ·
                      refine ⟨1499527311457464972182203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31989915977759252739886997 1499527311457464972182203)
                      ·
                        rfl

theorem cell23_2920319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_2920319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920319 prefixEnd_2920319 := by exact prefixLift 2920319
  have htrace : WordTrace (prefixWord ++ tailWord_2920319) baseStart_2920319 baseEnd_2920319 := by
    simpa [prefixWord, tailWord_2920319, baseEnd_2920319] using wordTrace_append hprefix tailTrace_2920319
  have hstable : (prefixWord ++ tailWord_2920319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920319).length < 2 ^ (prefixWord ++ tailWord_2920319).sum := by decide
  have hdescent : baseEnd_2920319 < baseStart_2920319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920323 : List Nat := [1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 4]
def baseStart_2920323 : Nat := 118140960795 + 2920323 * 2 ^ 59
def prefixEnd_2920323 : Nat := 4983230072969 + 3 ^ 40 * 2920323 * 2
def baseEnd_2920323 : Nat := 1499529365380082956532185

theorem tailTrace_2920323 : CollatzResearch.WordTrace tailWord_2920323 prefixEnd_2920323 1499529365380082956532185 := by
  unfold tailWord_2920323
  simp only [CollatzResearch.WordTrace]
  refine ⟨106512930199175997305877623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71008620132783998203918415 106512930199175997305877623)
  ·
    refine ⟨159769395298763995958816435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106512930199175997305877623 159769395298763995958816435)
    ·
      refine ⟨239654092948145993938224653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159769395298763995958816435 239654092948145993938224653)
      ·
        refine ⟨89870284855554747726834245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239654092948145993938224653 89870284855554747726834245)
        ·
          refine ⟨16850678410416515198781421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89870284855554747726834245 16850678410416515198781421)
          ·
            refine ⟨6319004403906193199543033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16850678410416515198781421 6319004403906193199543033)
            ·
              refine ⟨4739253302929644899657275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6319004403906193199543033 4739253302929644899657275)
              ·
                refine ⟨7108879954394467349485913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4739253302929644899657275 7108879954394467349485913)
                ·
                  refine ⟨5331659965795850512114435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7108879954394467349485913 5331659965795850512114435)
                  ·
                    refine ⟨7997489948693775768171653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5331659965795850512114435 7997489948693775768171653)
                    ·
                      refine ⟨1499529365380082956532185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7997489948693775768171653 1499529365380082956532185)
                      ·
                        rfl

theorem cell23_2920323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_2920323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920323 prefixEnd_2920323 := by exact prefixLift 2920323
  have htrace : WordTrace (prefixWord ++ tailWord_2920323) baseStart_2920323 baseEnd_2920323 := by
    simpa [prefixWord, tailWord_2920323, baseEnd_2920323] using wordTrace_append hprefix tailTrace_2920323
  have hstable : (prefixWord ++ tailWord_2920323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920323).length < 2 ^ (prefixWord ++ tailWord_2920323).sum := by decide
  have hdescent : baseEnd_2920323 < baseStart_2920323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920343 : List Nat := [1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 3]
def baseStart_2920343 : Nat := 118140960795 + 2920343 * 2 ^ 59
def prefixEnd_2920343 : Nat := 4983230072969 + 3 ^ 40 * 2920343 * 2
def baseEnd_2920343 : Nat := 1499539634993172878282093

theorem tailTrace_2920343 : CollatzResearch.WordTrace tailWord_2920343 prefixEnd_2920343 1499539634993172878282093 := by
  unfold tailWord_2920343
  simp only [CollatzResearch.WordTrace]
  refine ⟨106513659659103540721605683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71009106439402360481070455 106513659659103540721605683)
  ·
    refine ⟨159770489488655311082408525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106513659659103540721605683 159770489488655311082408525)
    ·
      refine ⟨59913933558245741655903197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159770489488655311082408525 59913933558245741655903197)
      ·
        refine ⟨22467725084342153120963699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59913933558245741655903197 22467725084342153120963699)
        ·
          refine ⟨33701587626513229681445549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22467725084342153120963699 33701587626513229681445549)
          ·
            refine ⟨12638095359942461130542081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33701587626513229681445549 12638095359942461130542081)
            ·
              refine ⟨9478571519956845847906561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12638095359942461130542081 9478571519956845847906561)
              ·
                refine ⟨7108928639967634385929921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9478571519956845847906561 7108928639967634385929921)
                ·
                  refine ⟨5331696479975725789447441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7108928639967634385929921 5331696479975725789447441)
                  ·
                    refine ⟨3998772359981794342085581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5331696479975725789447441 3998772359981794342085581)
                    ·
                      refine ⟨1499539634993172878282093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3998772359981794342085581 1499539634993172878282093)
                      ·
                        rfl

theorem cell23_2920343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_2920343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920343 prefixEnd_2920343 := by exact prefixLift 2920343
  have htrace : WordTrace (prefixWord ++ tailWord_2920343) baseStart_2920343 baseEnd_2920343 := by
    simpa [prefixWord, tailWord_2920343, baseEnd_2920343] using wordTrace_append hprefix tailTrace_2920343
  have hstable : (prefixWord ++ tailWord_2920343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920343).length < 2 ^ (prefixWord ++ tailWord_2920343).sum := by decide
  have hdescent : baseEnd_2920343 < baseStart_2920343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920376 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 3, 5]
def baseStart_2920376 : Nat := 118140960795 + 2920376 * 2 ^ 59
def prefixEnd_2920376 : Nat := 4983230072969 + 3 ^ 40 * 2920376 * 2
def baseEnd_2920376 : Nat := 499852193284923749723147

theorem tailTrace_2920376 : CollatzResearch.WordTrace tailWord_2920376 prefixEnd_2920376 499852193284923749723147 := by
  unfold tailWord_2920376
  simp only [CollatzResearch.WordTrace]
  refine ⟨53257431633991993678778491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71009908845322658238371321 53257431633991993678778491)
  ·
    refine ⟨79886147450987990518167737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53257431633991993678778491 79886147450987990518167737)
    ·
      refine ⟨59914610588240992888625803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79886147450987990518167737 59914610588240992888625803)
      ·
        refine ⟨89871915882361489332938705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59914610588240992888625803 89871915882361489332938705)
        ·
          refine ⟨67403936911771116999704029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89871915882361489332938705 67403936911771116999704029)
          ·
            refine ⟨25276476341914168874889011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67403936911771116999704029 25276476341914168874889011)
            ·
              refine ⟨37914714512871253312333517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25276476341914168874889011 37914714512871253312333517)
              ·
                refine ⟨14218017942326719992125069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37914714512871253312333517 14218017942326719992125069)
                ·
                  refine ⟨5331756728372519997046901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14218017942326719992125069 5331756728372519997046901)
                  ·
                    refine ⟨499852193284923749723147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5331756728372519997046901 499852193284923749723147)
                    ·
                      rfl

theorem cell23_2920376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_2920376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920376 prefixEnd_2920376 := by exact prefixLift 2920376
  have htrace : WordTrace (prefixWord ++ tailWord_2920376) baseStart_2920376 baseEnd_2920376 := by
    simpa [prefixWord, tailWord_2920376, baseEnd_2920376] using wordTrace_append hprefix tailTrace_2920376
  have hstable : (prefixWord ++ tailWord_2920376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920376).length < 2 ^ (prefixWord ++ tailWord_2920376).sum := by decide
  have hdescent : baseEnd_2920376 < baseStart_2920376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920383 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 1, 5, 2]
def baseStart_2920383 : Nat := 118140960795 + 2920383 * 2 ^ 59
def prefixEnd_2920383 : Nat := 4983230072969 + 3 ^ 40 * 2920383 * 2
def baseEnd_2920383 : Nat := 1499560174219352721781909

theorem tailTrace_2920383 : CollatzResearch.WordTrace tailWord_2920383 prefixEnd_2920383 1499560174219352721781909 := by
  unfold tailWord_2920383
  simp only [CollatzResearch.WordTrace]
  refine ⟨106515118578958627553061803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71010079052639085035374535 106515118578958627553061803)
  ·
    refine ⟨159772677868437941329592705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106515118578958627553061803 159772677868437941329592705)
    ·
      refine ⟨119829508401328455997194529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159772677868437941329592705 119829508401328455997194529)
      ·
        refine ⟨89872131300996341997895897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119829508401328455997194529 89872131300996341997895897)
        ·
          refine ⟨67404098475747256498421923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89872131300996341997895897 67404098475747256498421923)
          ·
            refine ⟨101106147713620884747632885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67404098475747256498421923 101106147713620884747632885)
            ·
              refine ⟨9478701348151957945090583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101106147713620884747632885 9478701348151957945090583)
              ·
                refine ⟨14218052022227936917635875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9478701348151957945090583 14218052022227936917635875)
                ·
                  refine ⟨21327078033341905376453813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14218052022227936917635875 21327078033341905376453813)
                  ·
                    refine ⟨1999413565625803629042545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21327078033341905376453813 1999413565625803629042545)
                    ·
                      refine ⟨1499560174219352721781909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1999413565625803629042545 1499560174219352721781909)
                      ·
                        rfl

theorem cell23_2920383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 5, 2].length) (baseStart_2920383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920383 prefixEnd_2920383 := by exact prefixLift 2920383
  have htrace : WordTrace (prefixWord ++ tailWord_2920383) baseStart_2920383 baseEnd_2920383 := by
    simpa [prefixWord, tailWord_2920383, baseEnd_2920383] using wordTrace_append hprefix tailTrace_2920383
  have hstable : (prefixWord ++ tailWord_2920383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920383).length < 2 ^ (prefixWord ++ tailWord_2920383).sum := by decide
  have hdescent : baseEnd_2920383 < baseStart_2920383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920430 : List Nat := [4, 1, 2, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_2920430 : Nat := 118140960795 + 2920430 * 2 ^ 59
def prefixEnd_2920430 : Nat := 4983230072969 + 3 ^ 40 * 2920430 * 2
def baseEnd_2920430 : Nat := 1499584307810114037894193

theorem tailTrace_2920430 : CollatzResearch.WordTrace tailWord_2920430 prefixEnd_2920430 1499584307810114037894193 := by
  unfold tailWord_2920430
  simp only [CollatzResearch.WordTrace]
  refine ⟨13314604101223544322502843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71011221873192236386681829 13314604101223544322502843)
  ·
    refine ⟨19971906151835316483754265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13314604101223544322502843 19971906151835316483754265)
    ·
      refine ⟨14978929613876487362815699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19971906151835316483754265 14978929613876487362815699)
      ·
        refine ⟨22468394420814731044223549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14978929613876487362815699 22468394420814731044223549)
        ·
          refine ⟨8425647907805524141583831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22468394420814731044223549 8425647907805524141583831)
          ·
            refine ⟨12638471861708286212375747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8425647907805524141583831 12638471861708286212375747)
            ·
              refine ⟨18957707792562429318563621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12638471861708286212375747 18957707792562429318563621)
              ·
                refine ⟨3554570211105455497230679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18957707792562429318563621 3554570211105455497230679)
                ·
                  refine ⟨5331855316658183245846019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554570211105455497230679 5331855316658183245846019)
                  ·
                    refine ⟨7997782974987274868769029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5331855316658183245846019 7997782974987274868769029)
                    ·
                      refine ⟨1499584307810114037894193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7997782974987274868769029 1499584307810114037894193)
                      ·
                        rfl

theorem cell23_2920430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_2920430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920430 prefixEnd_2920430 := by exact prefixLift 2920430
  have htrace : WordTrace (prefixWord ++ tailWord_2920430) baseStart_2920430 baseEnd_2920430 := by
    simpa [prefixWord, tailWord_2920430, baseEnd_2920430] using wordTrace_append hprefix tailTrace_2920430
  have hstable : (prefixWord ++ tailWord_2920430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920430).length < 2 ^ (prefixWord ++ tailWord_2920430).sum := by decide
  have hdescent : baseEnd_2920430 < baseStart_2920430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920473 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 2, 7, 2]
def baseStart_2920473 : Nat := 118140960795 + 2920473 * 2 ^ 59
def prefixEnd_2920473 : Nat := 4983230072969 + 3 ^ 40 * 2920473 * 2
def baseEnd_2920473 : Nat := 1499606387478257369656495

theorem tailTrace_2920473 : CollatzResearch.WordTrace tailWord_2920473 prefixEnd_2920473 1499606387478257369656495 := by
  unfold tailWord_2920473
  simp only [CollatzResearch.WordTrace]
  refine ⟨106518401148632572923838073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71012267432421715282558715 106518401148632572923838073)
  ·
    refine ⟨79888800861474429692878555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106518401148632572923838073 79888800861474429692878555)
    ·
      refine ⟨119833201292211644539317833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79888800861474429692878555 119833201292211644539317833)
      ·
        refine ⟨89874900969158733404488375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119833201292211644539317833 89874900969158733404488375)
        ·
          refine ⟨134812351453738100106732563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89874900969158733404488375 134812351453738100106732563)
          ·
            refine ⟨202218527180607150160098845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134812351453738100106732563 202218527180607150160098845)
            ·
              refine ⟨75831947692727681310037067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202218527180607150160098845 75831947692727681310037067)
              ·
                refine ⟨113747921539091521965055601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75831947692727681310037067 113747921539091521965055601)
                ·
                  refine ⟨85310941154318641473791701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113747921539091521965055601 85310941154318641473791701)
                  ·
                    refine ⟨1999475183304343159541993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 85310941154318641473791701 1999475183304343159541993)
                    ·
                      refine ⟨1499606387478257369656495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1999475183304343159541993 1499606387478257369656495)
                      ·
                        rfl

theorem cell23_2920473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 7, 2].length) (baseStart_2920473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920473 prefixEnd_2920473 := by exact prefixLift 2920473
  have htrace : WordTrace (prefixWord ++ tailWord_2920473) baseStart_2920473 baseEnd_2920473 := by
    simpa [prefixWord, tailWord_2920473, baseEnd_2920473] using wordTrace_append hprefix tailTrace_2920473
  have hstable : (prefixWord ++ tailWord_2920473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920473).length < 2 ^ (prefixWord ++ tailWord_2920473).sum := by decide
  have hdescent : baseEnd_2920473 < baseStart_2920473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920484 : List Nat := [2, 3, 1, 4, 2, 2, 1, 2, 1, 2, 3]
def baseStart_2920484 : Nat := 118140960795 + 2920484 * 2 ^ 59
def prefixEnd_2920484 : Nat := 4983230072969 + 3 ^ 40 * 2920484 * 2
def baseEnd_2920484 : Nat := 1499612035765456826618945

theorem tailTrace_2920484 : CollatzResearch.WordTrace tailWord_2920484 prefixEnd_2920484 1499612035765456826618945 := by
  unfold tailWord_2920484
  simp only [CollatzResearch.WordTrace]
  refine ⟨53259401175796360901244253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71012534901061814534992337 53259401175796360901244253)
  ·
    refine ⟨19972275440923635337966595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53259401175796360901244253 19972275440923635337966595)
    ·
      refine ⟨29958413161385453006949893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19972275440923635337966595 29958413161385453006949893)
      ·
        refine ⟨5617202467759772438803105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29958413161385453006949893 5617202467759772438803105)
        ·
          refine ⟨4212901850819829329102329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5617202467759772438803105 4212901850819829329102329)
          ·
            refine ⟨3159676388114871996826747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4212901850819829329102329 3159676388114871996826747)
            ·
              refine ⟨4739514582172307995240121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159676388114871996826747 4739514582172307995240121)
              ·
                refine ⟨3554635936629230996430091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4739514582172307995240121 3554635936629230996430091)
                ·
                  refine ⟨5331953904943846494645137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554635936629230996430091 5331953904943846494645137)
                  ·
                    refine ⟨3998965428707884870983853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5331953904943846494645137 3998965428707884870983853)
                    ·
                      refine ⟨1499612035765456826618945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3998965428707884870983853 1499612035765456826618945)
                      ·
                        rfl

theorem cell23_2920484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_2920484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920484 prefixEnd_2920484 := by exact prefixLift 2920484
  have htrace : WordTrace (prefixWord ++ tailWord_2920484) baseStart_2920484 baseEnd_2920484 := by
    simpa [prefixWord, tailWord_2920484, baseEnd_2920484] using wordTrace_append hprefix tailTrace_2920484
  have hstable : (prefixWord ++ tailWord_2920484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920484).length < 2 ^ (prefixWord ++ tailWord_2920484).sum := by decide
  have hdescent : baseEnd_2920484 < baseStart_2920484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920530 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 2, 6]
def baseStart_2920530 : Nat := 118140960795 + 2920530 * 2 ^ 59
def prefixEnd_2920530 : Nat := 4983230072969 + 3 ^ 40 * 2920530 * 2
def baseEnd_2920530 : Nat := 499878551958521215547911

theorem tailTrace_2920530 : CollatzResearch.WordTrace tailWord_2920530 prefixEnd_2920530 499878551958521215547911 := by
  unfold tailWord_2920530
  simp only [CollatzResearch.WordTrace]
  refine ⟨26630120027356517914665761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71013653406284047772442029 26630120027356517914665761)
  ·
    refine ⟨19972590020517388435999321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26630120027356517914665761 19972590020517388435999321)
    ·
      refine ⟨14979442515388041326999491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19972590020517388435999321 14979442515388041326999491)
      ·
        refine ⟨22469163773082061990499237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14979442515388041326999491 22469163773082061990499237)
        ·
          refine ⟨4212968207452886623218607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22469163773082061990499237 4212968207452886623218607)
          ·
            refine ⟨6319452311179329934827911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4212968207452886623218607 6319452311179329934827911)
            ·
              refine ⟨9479178466768994902241867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6319452311179329934827911 9479178466768994902241867)
              ·
                refine ⟨14218767700153492353362801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9479178466768994902241867 14218767700153492353362801)
                ·
                  refine ⟨10664075775115119265022101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14218767700153492353362801 10664075775115119265022101)
                  ·
                    refine ⟨499878551958521215547911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10664075775115119265022101 499878551958521215547911)
                    ·
                      rfl

theorem cell23_2920530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_2920530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920530 prefixEnd_2920530 := by exact prefixLift 2920530
  have htrace : WordTrace (prefixWord ++ tailWord_2920530) baseStart_2920530 baseEnd_2920530 := by
    simpa [prefixWord, tailWord_2920530, baseEnd_2920530] using wordTrace_append hprefix tailTrace_2920530
  have hstable : (prefixWord ++ tailWord_2920530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920530).length < 2 ^ (prefixWord ++ tailWord_2920530).sum := by decide
  have hdescent : baseEnd_2920530 < baseStart_2920530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920533 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_2920533 : Nat := 118140960795 + 2920533 * 2 ^ 59
def prefixEnd_2920533 : Nat := 4983230072969 + 3 ^ 40 * 2920533 * 2
def baseEnd_2920533 : Nat := 1499637196317527134906219

theorem tailTrace_2920533 : CollatzResearch.WordTrace tailWord_2920533 prefixEnd_2920533 1499637196317527134906219 := by
  unfold tailWord_2920533
  simp only [CollatzResearch.WordTrace]
  refine ⟨106520589528415203171022253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71013726352276802114014835 106520589528415203171022253)
  ·
    refine ⟨39945221073155701189133345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106520589528415203171022253 39945221073155701189133345)
    ·
      refine ⟨29958915804866775891850009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39945221073155701189133345 29958915804866775891850009)
      ·
        refine ⟨22469186853650081918887507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29958915804866775891850009 22469186853650081918887507)
        ·
          refine ⟨33703780280475122878331261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22469186853650081918887507 33703780280475122878331261)
          ·
            refine ⟨12638917605178171079374223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33703780280475122878331261 12638917605178171079374223)
            ·
              refine ⟨18958376407767256619061335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12638917605178171079374223 18958376407767256619061335)
              ·
                refine ⟨28437564611650884928592003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18958376407767256619061335 28437564611650884928592003)
                ·
                  refine ⟨42656346917476327392888005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28437564611650884928592003 42656346917476327392888005)
                  ·
                    refine ⟨7998065047026811386166501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42656346917476327392888005 7998065047026811386166501)
                    ·
                      refine ⟨1499637196317527134906219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7998065047026811386166501 1499637196317527134906219)
                      ·
                        rfl

theorem cell23_2920533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_2920533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920533 prefixEnd_2920533 := by exact prefixLift 2920533
  have htrace : WordTrace (prefixWord ++ tailWord_2920533) baseStart_2920533 baseEnd_2920533 := by
    simpa [prefixWord, tailWord_2920533, baseEnd_2920533] using wordTrace_append hprefix tailTrace_2920533
  have hstable : (prefixWord ++ tailWord_2920533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920533).length < 2 ^ (prefixWord ++ tailWord_2920533).sum := by decide
  have hdescent : baseEnd_2920533 < baseStart_2920533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920537 : List Nat := [1, 2, 1, 2, 2, 1, 3, 5, 2, 2, 2]
def baseStart_2920537 : Nat := 118140960795 + 2920537 * 2 ^ 59
def prefixEnd_2920537 : Nat := 4983230072969 + 3 ^ 40 * 2920537 * 2
def baseEnd_2920537 : Nat := 1499639250240145119256201

theorem tailTrace_2920537 : CollatzResearch.WordTrace tailWord_2920537 prefixEnd_2920537 1499639250240145119256201 := by
  unfold tailWord_2920537
  simp only [CollatzResearch.WordTrace]
  refine ⟨106520735420400711854167865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71013823613600474569445243 106520735420400711854167865)
  ·
    refine ⟨79890551565300533890625899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106520735420400711854167865 79890551565300533890625899)
    ·
      refine ⟨119835827347950800835938849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79890551565300533890625899 119835827347950800835938849)
      ·
        refine ⟨89876870510963100626954137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119835827347950800835938849 89876870510963100626954137)
        ·
          refine ⟨67407652883222325470215603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89876870510963100626954137 67407652883222325470215603)
          ·
            refine ⟨101111479324833488205323405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67407652883222325470215603 101111479324833488205323405)
            ·
              refine ⟨37916804746812558076996277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101111479324833488205323405 37916804746812558076996277)
              ·
                refine ⟨3554700445013677319718401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37916804746812558076996277 3554700445013677319718401)
                ·
                  refine ⟨2666025333760257989788801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3554700445013677319718401 2666025333760257989788801)
                  ·
                    refine ⟨1999519000320193492341601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2666025333760257989788801 1999519000320193492341601)
                    ·
                      refine ⟨1499639250240145119256201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1999519000320193492341601 1499639250240145119256201)
                      ·
                        rfl

theorem cell23_2920537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 2, 2].length) (baseStart_2920537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920537 prefixEnd_2920537 := by exact prefixLift 2920537
  have htrace : WordTrace (prefixWord ++ tailWord_2920537) baseStart_2920537 baseEnd_2920537 := by
    simpa [prefixWord, tailWord_2920537, baseEnd_2920537] using wordTrace_append hprefix tailTrace_2920537
  have hstable : (prefixWord ++ tailWord_2920537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920537).length < 2 ^ (prefixWord ++ tailWord_2920537).sum := by decide
  have hdescent : baseEnd_2920537 < baseStart_2920537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920553 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 1, 5, 3]
def baseStart_2920553 : Nat := 118140960795 + 2920553 * 2 ^ 59
def prefixEnd_2920553 : Nat := 4983230072969 + 3 ^ 40 * 2920553 * 2
def baseEnd_2920553 : Nat := 1499647465930617056656127

theorem tailTrace_2920553 : CollatzResearch.WordTrace tailWord_2920553 prefixEnd_2920553 1499647465930617056656127 := by
  unfold tailWord_2920553
  simp only [CollatzResearch.WordTrace]
  refine ⟨106521318988342746586750313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71014212658895164391166875 106521318988342746586750313)
  ·
    refine ⟨79890989241257059940062735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106521318988342746586750313 79890989241257059940062735)
    ·
      refine ⟨119836483861885589910094103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79890989241257059940062735 119836483861885589910094103)
      ·
        refine ⟨179754725792828384865141155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119836483861885589910094103 179754725792828384865141155)
        ·
          refine ⟨269632088689242577297711733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179754725792828384865141155 269632088689242577297711733)
          ·
            refine ⟨25278008314616491621660475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 269632088689242577297711733 25278008314616491621660475)
            ·
              refine ⟨37917012471924737432490713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25278008314616491621660475 37917012471924737432490713)
              ·
                refine ⟨28437759353943553074368035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37917012471924737432490713 28437759353943553074368035)
                ·
                  refine ⟨42656639030915329611552053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28437759353943553074368035 42656639030915329611552053)
                  ·
                    refine ⟨3999059909148312151083005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42656639030915329611552053 3999059909148312151083005)
                    ·
                      refine ⟨1499647465930617056656127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3999059909148312151083005 1499647465930617056656127)
                      ·
                        rfl

theorem cell23_2920553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 5, 3].length) (baseStart_2920553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920553 prefixEnd_2920553 := by exact prefixLift 2920553
  have htrace : WordTrace (prefixWord ++ tailWord_2920553) baseStart_2920553 baseEnd_2920553 := by
    simpa [prefixWord, tailWord_2920553, baseEnd_2920553] using wordTrace_append hprefix tailTrace_2920553
  have hstable : (prefixWord ++ tailWord_2920553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920553).length < 2 ^ (prefixWord ++ tailWord_2920553).sum := by decide
  have hdescent : baseEnd_2920553 < baseStart_2920553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920560 : List Nat := [2, 1, 1, 1, 5, 2, 1, 5, 5]
def baseStart_2920560 : Nat := 118140960795 + 2920560 * 2 ^ 59
def prefixEnd_2920560 : Nat := 4983230072969 + 3 ^ 40 * 2920560 * 2
def baseEnd_2920560 : Nat := 166627895588355392140955

theorem tailTrace_2920560 : CollatzResearch.WordTrace tailWord_2920560 prefixEnd_2920560 166627895588355392140955 := by
  unfold tailWord_2920560
  simp only [CollatzResearch.WordTrace]
  refine ⟨53260787149658693391127567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71014382866211591188170089 53260787149658693391127567)
  ·
    refine ⟨79891180724488040086691351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53260787149658693391127567 79891180724488040086691351)
    ·
      refine ⟨119836771086732060130037027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79891180724488040086691351 119836771086732060130037027)
      ·
        refine ⟨179755156630098090195055541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119836771086732060130037027 179755156630098090195055541)
        ·
          refine ⟨16852045934071695955786457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179755156630098090195055541 16852045934071695955786457)
          ·
            refine ⟨12639034450553771966839843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16852045934071695955786457 12639034450553771966839843)
            ·
              refine ⟨18958551675830657950259765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12639034450553771966839843 18958551675830657950259765)
              ·
                refine ⟨1777364219609124182836853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18958551675830657950259765 1777364219609124182836853)
                ·
                  refine ⟨166627895588355392140955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1777364219609124182836853 166627895588355392140955)
                  ·
                    rfl

theorem cell23_2920560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 5].length) (baseStart_2920560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920560 prefixEnd_2920560 := by exact prefixLift 2920560
  have htrace : WordTrace (prefixWord ++ tailWord_2920560) baseStart_2920560 baseEnd_2920560 := by
    simpa [prefixWord, tailWord_2920560, baseEnd_2920560] using wordTrace_append hprefix tailTrace_2920560
  have hstable : (prefixWord ++ tailWord_2920560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920560).length < 2 ^ (prefixWord ++ tailWord_2920560).sum := by decide
  have hdescent : baseEnd_2920560 < baseStart_2920560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920583 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_2920583 : Nat := 118140960795 + 2920583 * 2 ^ 59
def prefixEnd_2920583 : Nat := 4983230072969 + 3 ^ 40 * 2920583 * 2
def baseEnd_2920583 : Nat := 1499662870350251939280989

theorem tailTrace_2920583 : CollatzResearch.WordTrace tailWord_2920583 prefixEnd_2920583 1499662870350251939280989 := by
  unfold tailWord_2920583
  simp only [CollatzResearch.WordTrace]
  refine ⟨106522413178234061710342403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71014942118822707806894935 106522413178234061710342403)
  ·
    refine ⟨159783619767351092565513605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106522413178234061710342403 159783619767351092565513605)
    ·
      refine ⟨29959428706378329856033801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159783619767351092565513605 29959428706378329856033801)
      ·
        refine ⟨22469571529783747392025351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29959428706378329856033801 22469571529783747392025351)
        ·
          refine ⟨33704357294675621088038027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22469571529783747392025351 33704357294675621088038027)
          ·
            refine ⟨50556535942013431632057041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33704357294675621088038027 50556535942013431632057041)
            ·
              refine ⟨37917401956510073724042781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50556535942013431632057041 37917401956510073724042781)
              ·
                refine ⟨14219025733691277646516043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37917401956510073724042781 14219025733691277646516043)
                ·
                  refine ⟨21328538600536916469774065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14219025733691277646516043 21328538600536916469774065)
                  ·
                    refine ⟨15996403950402687352330549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21328538600536916469774065 15996403950402687352330549)
                    ·
                      refine ⟨1499662870350251939280989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15996403950402687352330549 1499662870350251939280989)
                      ·
                        rfl

theorem cell23_2920583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_2920583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920583 prefixEnd_2920583 := by exact prefixLift 2920583
  have htrace : WordTrace (prefixWord ++ tailWord_2920583) baseStart_2920583 baseEnd_2920583 := by
    simpa [prefixWord, tailWord_2920583, baseEnd_2920583] using wordTrace_append hprefix tailTrace_2920583
  have hstable : (prefixWord ++ tailWord_2920583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920583).length < 2 ^ (prefixWord ++ tailWord_2920583).sum := by decide
  have hdescent : baseEnd_2920583 < baseStart_2920583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920628 : List Nat := [2, 5, 3, 1, 2, 1, 1, 1, 7]
def baseStart_2920628 : Nat := 118140960795 + 2920628 * 2 ^ 59
def prefixEnd_2920628 : Nat := 4983230072969 + 3 ^ 40 * 2920628 * 2
def baseEnd_2920628 : Nat := 166631775219967140357587

theorem tailTrace_2920628 : CollatzResearch.WordTrace tailWord_2920628 prefixEnd_2920628 166631775219967140357587 := by
  unfold tailWord_2920628
  simp only [CollatzResearch.WordTrace]
  refine ⟨53262027231535517197865269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71016036308714022930487025 53262027231535517197865269)
  ·
    refine ⟨4993315052956454737299869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53262027231535517197865269 4993315052956454737299869)
    ·
      refine ⟨1872493144858670526487451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4993315052956454737299869 1872493144858670526487451)
      ·
        refine ⟨2808739717288005789731177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1872493144858670526487451 2808739717288005789731177)
        ·
          refine ⟨2106554787966004342298383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2808739717288005789731177 2106554787966004342298383)
          ·
            refine ⟨3159832181949006513447575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2106554787966004342298383 3159832181949006513447575)
            ·
              refine ⟨4739748272923509770171363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159832181949006513447575 4739748272923509770171363)
              ·
                refine ⟨7109622409385264655257045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4739748272923509770171363 7109622409385264655257045)
                ·
                  refine ⟨166631775219967140357587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7109622409385264655257045 166631775219967140357587)
                  ·
                    rfl

theorem cell23_2920628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_2920628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920628 prefixEnd_2920628 := by exact prefixLift 2920628
  have htrace : WordTrace (prefixWord ++ tailWord_2920628) baseStart_2920628 baseEnd_2920628 := by
    simpa [prefixWord, tailWord_2920628, baseEnd_2920628] using wordTrace_append hprefix tailTrace_2920628
  have hstable : (prefixWord ++ tailWord_2920628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920628).length < 2 ^ (prefixWord ++ tailWord_2920628).sum := by decide
  have hdescent : baseEnd_2920628 < baseStart_2920628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920633 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 8]
def baseStart_2920633 : Nat := 118140960795 + 2920633 * 2 ^ 59
def prefixEnd_2920633 : Nat := 4983230072969 + 3 ^ 40 * 2920633 * 2
def baseEnd_2920633 : Nat := 166632060486997415961751

theorem tailTrace_2920633 : CollatzResearch.WordTrace tailWord_2920633 prefixEnd_2920633 166632060486997415961751 := by
  unfold tailWord_2920633
  simp only [CollatzResearch.WordTrace]
  refine ⟨106524236828052920249662553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71016157885368613499775035 106524236828052920249662553)
  ·
    refine ⟨79893177621039690187246915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106524236828052920249662553 79893177621039690187246915)
    ·
      refine ⟨119839766431559535280870373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79893177621039690187246915 119839766431559535280870373)
      ·
        refine ⟨22469956205917412865163195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119839766431559535280870373 22469956205917412865163195)
        ·
          refine ⟨33704934308876119297744793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22469956205917412865163195 33704934308876119297744793)
          ·
            refine ⟨25278700731657089473308595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33704934308876119297744793 25278700731657089473308595)
            ·
              refine ⟨37918051097485634209962893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25278700731657089473308595 37918051097485634209962893)
              ·
                refine ⟨14219269161557112828736085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37918051097485634209962893 14219269161557112828736085)
                ·
                  refine ⟨166632060486997415961751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14219269161557112828736085 166632060486997415961751)
                  ·
                    rfl

theorem cell23_2920633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 8].length) (baseStart_2920633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920633 prefixEnd_2920633 := by exact prefixLift 2920633
  have htrace : WordTrace (prefixWord ++ tailWord_2920633) baseStart_2920633 baseEnd_2920633 := by
    simpa [prefixWord, tailWord_2920633, baseEnd_2920633] using wordTrace_append hprefix tailTrace_2920633
  have hstable : (prefixWord ++ tailWord_2920633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920633).length < 2 ^ (prefixWord ++ tailWord_2920633).sum := by decide
  have hdescent : baseEnd_2920633 < baseStart_2920633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920650 : List Nat := [3, 1, 2, 1, 3, 1, 3, 3, 6]
def baseStart_2920650 : Nat := 118140960795 + 2920650 * 2 ^ 59
def prefixEnd_2920650 : Nat := 4983230072969 + 3 ^ 40 * 2920650 * 2
def baseEnd_2920650 : Nat := 166633030394900353015909

theorem tailTrace_2920650 : CollatzResearch.WordTrace tailWord_2920650 prefixEnd_2920650 166633030394900353015909 := by
  unfold tailWord_2920650
  simp only [CollatzResearch.WordTrace]
  refine ⟨26631214217247833038257851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71016571245994221435354269 26631214217247833038257851)
  ·
    refine ⟨39946821325871749557386777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26631214217247833038257851 39946821325871749557386777)
    ·
      refine ⟨29960115994403812168040083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39946821325871749557386777 29960115994403812168040083)
      ·
        refine ⟨44940173991605718252060125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29960115994403812168040083 44940173991605718252060125)
        ·
          refine ⟨16852565246852144344522547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44940173991605718252060125 16852565246852144344522547)
          ·
            refine ⟨25278847870278216516783821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16852565246852144344522547 25278847870278216516783821)
            ·
              refine ⟨9479567951354331193793933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25278847870278216516783821 9479567951354331193793933)
              ·
                refine ⟨3554837981757874197672725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9479567951354331193793933 3554837981757874197672725)
                ·
                  refine ⟨166633030394900353015909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3554837981757874197672725 166633030394900353015909)
                  ·
                    rfl

theorem cell23_2920650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 6].length) (baseStart_2920650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920650 prefixEnd_2920650 := by exact prefixLift 2920650
  have htrace : WordTrace (prefixWord ++ tailWord_2920650) baseStart_2920650 baseEnd_2920650 := by
    simpa [prefixWord, tailWord_2920650, baseEnd_2920650] using wordTrace_append hprefix tailTrace_2920650
  have hstable : (prefixWord ++ tailWord_2920650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920650).length < 2 ^ (prefixWord ++ tailWord_2920650).sum := by decide
  have hdescent : baseEnd_2920650 < baseStart_2920650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920711 : List Nat := [1, 1, 4, 5, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2920711 : Nat := 118140960795 + 2920711 * 2 ^ 59
def prefixEnd_2920711 : Nat := 4983230072969 + 3 ^ 40 * 2920711 * 2
def baseEnd_2920711 : Nat := 1499728595874027438480401

theorem tailTrace_2920711 : CollatzResearch.WordTrace tailWord_2920711 prefixEnd_2920711 1499728595874027438480401 := by
  unfold tailWord_2920711
  simp only [CollatzResearch.WordTrace]
  refine ⟨106527081721770339571001987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71018054481180226380667991 106527081721770339571001987)
  ·
    refine ⟨159790622582655509356502981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106527081721770339571001987 159790622582655509356502981)
    ·
      refine ⟨29960741734247908004344309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159790622582655509356502981 29960741734247908004344309)
      ·
        refine ⟨2808819537585741375407279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29960741734247908004344309 2808819537585741375407279)
        ·
          refine ⟨4213229306378612063110919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2808819537585741375407279 4213229306378612063110919)
          ·
            refine ⟨6319843959567918094666379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4213229306378612063110919 6319843959567918094666379)
            ·
              refine ⟨9479765939351877141999569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6319843959567918094666379 9479765939351877141999569)
              ·
                refine ⟨7109824454513907856499677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9479765939351877141999569 7109824454513907856499677)
                ·
                  refine ⟨2666184170442715446187379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7109824454513907856499677 2666184170442715446187379)
                  ·
                    refine ⟨3999276255664073169281069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2666184170442715446187379 3999276255664073169281069)
                    ·
                      refine ⟨1499728595874027438480401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3999276255664073169281069 1499728595874027438480401)
                      ·
                        rfl

theorem cell23_2920711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2920711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920711 prefixEnd_2920711 := by exact prefixLift 2920711
  have htrace : WordTrace (prefixWord ++ tailWord_2920711) baseStart_2920711 baseEnd_2920711 := by
    simpa [prefixWord, tailWord_2920711, baseEnd_2920711] using wordTrace_append hprefix tailTrace_2920711
  have hstable : (prefixWord ++ tailWord_2920711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920711).length < 2 ^ (prefixWord ++ tailWord_2920711).sum := by decide
  have hdescent : baseEnd_2920711 < baseStart_2920711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920723 : List Nat := [1, 1, 1, 2, 1, 3, 1, 13]
def baseStart_2920723 : Nat := 118140960795 + 2920723 * 2 ^ 59
def prefixEnd_2920723 : Nat := 4983230072969 + 3 ^ 40 * 2920723 * 2
def baseEnd_2920723 : Nat := 55545731764514125612235

theorem tailTrace_2920723 : CollatzResearch.WordTrace tailWord_2920723 prefixEnd_2920723 55545731764514125612235 := by
  unfold tailWord_2920723
  simp only [CollatzResearch.WordTrace]
  refine ⟨106527519397726865620438823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71018346265151243746959215 106527519397726865620438823)
  ·
    refine ⟨159791279096590298430658235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106527519397726865620438823 159791279096590298430658235)
    ·
      refine ⟨239686918644885447645987353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159791279096590298430658235 239686918644885447645987353)
      ·
        refine ⟨179765188983664085734490515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239686918644885447645987353 179765188983664085734490515)
        ·
          refine ⟨269647783475496128601735773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179765188983664085734490515 269647783475496128601735773)
          ·
            refine ⟨101117918803311048225650915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269647783475496128601735773 101117918803311048225650915)
            ·
              refine ⟨151676878204966572338476373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101117918803311048225650915 151676878204966572338476373)
              ·
                refine ⟨55545731764514125612235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 151676878204966572338476373 55545731764514125612235)
                ·
                  rfl

theorem cell23_2920723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 13].length) (baseStart_2920723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920723 prefixEnd_2920723 := by exact prefixLift 2920723
  have htrace : WordTrace (prefixWord ++ tailWord_2920723) baseStart_2920723 baseEnd_2920723 := by
    simpa [prefixWord, tailWord_2920723, baseEnd_2920723] using wordTrace_append hprefix tailTrace_2920723
  have hstable : (prefixWord ++ tailWord_2920723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920723).length < 2 ^ (prefixWord ++ tailWord_2920723).sum := by decide
  have hdescent : baseEnd_2920723 < baseStart_2920723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920740 : List Nat := [2, 3, 1, 3, 1, 3, 10]
def baseStart_2920740 : Nat := 118140960795 + 2920740 * 2 ^ 59
def prefixEnd_2920740 : Nat := 4983230072969 + 3 ^ 40 * 2920740 * 2
def baseEnd_2920740 : Nat := 18515351689049479321207

theorem tailTrace_2920740 : CollatzResearch.WordTrace tailWord_2920740 prefixEnd_2920740 18515351689049479321207 := by
  unfold tailWord_2920740
  simp only [CollatzResearch.WordTrace]
  refine ⟨53264069719332638761903837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71018759625776851682538449 53264069719332638761903837)
  ·
    refine ⟨19974026144749739535713939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53264069719332638761903837 19974026144749739535713939)
    ·
      refine ⟨29961039217124609303570909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19974026144749739535713939 29961039217124609303570909)
      ·
        refine ⟨11235389706421728488839091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29961039217124609303570909 11235389706421728488839091)
        ·
          refine ⟨16853084559632592733258637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11235389706421728488839091 16853084559632592733258637)
          ·
            refine ⟨6319906709862222274971989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16853084559632592733258637 6319906709862222274971989)
            ·
              refine ⟨18515351689049479321207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6319906709862222274971989 18515351689049479321207)
              ·
                rfl

theorem cell23_2920740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 10].length) (baseStart_2920740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920740 prefixEnd_2920740 := by exact prefixLift 2920740
  have htrace : WordTrace (prefixWord ++ tailWord_2920740) baseStart_2920740 baseEnd_2920740 := by
    simpa [prefixWord, tailWord_2920740, baseEnd_2920740] using wordTrace_append hprefix tailTrace_2920740
  have hstable : (prefixWord ++ tailWord_2920740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920740).length < 2 ^ (prefixWord ++ tailWord_2920740).sum := by decide
  have hdescent : baseEnd_2920740 < baseStart_2920740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920744 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 4, 4]
def baseStart_2920744 : Nat := 118140960795 + 2920744 * 2 ^ 59
def prefixEnd_2920744 : Nat := 4983230072969 + 3 ^ 40 * 2920744 * 2
def baseEnd_2920744 : Nat := 499915180245208603122583

theorem tailTrace_2920744 : CollatzResearch.WordTrace tailWord_2920744 prefixEnd_2920744 499915180245208603122583 := by
  unfold tailWord_2920744
  simp only [CollatzResearch.WordTrace]
  refine ⟨53264142665325393103476643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71018856887100524137968857 53264142665325393103476643)
  ·
    refine ⟨79896213997988089655214965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53264142665325393103476643 79896213997988089655214965)
    ·
      refine ⟨7490270062311383405176403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79896213997988089655214965 7490270062311383405176403)
      ·
        refine ⟨11235405093467075107764605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7490270062311383405176403 11235405093467075107764605)
        ·
          refine ⟨4213276910050153165411727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11235405093467075107764605 4213276910050153165411727)
          ·
            refine ⟨6319915365075229748117591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4213276910050153165411727 6319915365075229748117591)
            ·
              refine ⟨9479873047612844622176387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6319915365075229748117591 9479873047612844622176387)
              ·
                refine ⟨14219809571419266933264581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9479873047612844622176387 14219809571419266933264581)
                ·
                  refine ⟨2666214294641112549987109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14219809571419266933264581 2666214294641112549987109)
                  ·
                    refine ⟨499915180245208603122583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2666214294641112549987109 499915180245208603122583)
                    ·
                      rfl

theorem cell23_2920744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_2920744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920744 prefixEnd_2920744 := by exact prefixLift 2920744
  have htrace : WordTrace (prefixWord ++ tailWord_2920744) baseStart_2920744 baseEnd_2920744 := by
    simpa [prefixWord, tailWord_2920744, baseEnd_2920744] using wordTrace_append hprefix tailTrace_2920744
  have hstable : (prefixWord ++ tailWord_2920744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920744).length < 2 ^ (prefixWord ++ tailWord_2920744).sum := by decide
  have hdescent : baseEnd_2920744 < baseStart_2920744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920751 : List Nat := [1, 1, 2, 1, 2, 1, 6, 4, 1, 2, 2]
def baseStart_2920751 : Nat := 118140960795 + 2920751 * 2 ^ 59
def prefixEnd_2920751 : Nat := 4983230072969 + 3 ^ 40 * 2920751 * 2
def baseEnd_2920751 : Nat := 1499749135100207281980217

theorem tailTrace_2920751 : CollatzResearch.WordTrace tailWord_2920751 prefixEnd_2920751 1499749135100207281980217 := by
  unfold tailWord_2920751
  simp only [CollatzResearch.WordTrace]
  refine ⟨106528540641625426402458107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71019027094416950934972071 106528540641625426402458107)
  ·
    refine ⟨159792810962438139603687161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106528540641625426402458107 159792810962438139603687161)
    ·
      refine ⟨119844608221828604702765371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159792810962438139603687161 119844608221828604702765371)
      ·
        refine ⟨179766912332742907054148057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119844608221828604702765371 179766912332742907054148057)
        ·
          refine ⟨134825184249557180290611043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179766912332742907054148057 134825184249557180290611043)
          ·
            refine ⟨202237776374335770435916565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134825184249557180290611043 202237776374335770435916565)
            ·
              refine ⟨9479895767546989239183589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 202237776374335770435916565 9479895767546989239183589)
              ·
                refine ⟨1777480456415060482346923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9479895767546989239183589 1777480456415060482346923)
                ·
                  refine ⟨2666220684622590723520385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1777480456415060482346923 2666220684622590723520385)
                  ·
                    refine ⟨1999665513466943042640289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2666220684622590723520385 1999665513466943042640289)
                    ·
                      refine ⟨1499749135100207281980217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1999665513466943042640289 1499749135100207281980217)
                      ·
                        rfl

theorem cell23_2920751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 1, 2, 2].length) (baseStart_2920751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920751 prefixEnd_2920751 := by exact prefixLift 2920751
  have htrace : WordTrace (prefixWord ++ tailWord_2920751) baseStart_2920751 baseEnd_2920751 := by
    simpa [prefixWord, tailWord_2920751, baseEnd_2920751] using wordTrace_append hprefix tailTrace_2920751
  have hstable : (prefixWord ++ tailWord_2920751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920751).length < 2 ^ (prefixWord ++ tailWord_2920751).sum := by decide
  have hdescent : baseEnd_2920751 < baseStart_2920751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920761 : List Nat := [1, 2, 1, 6, 1, 2, 3, 1, 2, 4]
def baseStart_2920761 : Nat := 118140960795 + 2920761 * 2 ^ 59
def prefixEnd_2920761 : Nat := 4983230072969 + 3 ^ 40 * 2920761 * 2
def baseEnd_2920761 : Nat := 499918089968917414285057

theorem tailTrace_2920761 : CollatzResearch.WordTrace tailWord_2920761 prefixEnd_2920761 499918089968917414285057 := by
  unfold tailWord_2920761
  simp only [CollatzResearch.WordTrace]
  refine ⟨106528905371589198110322137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71019270247726132073548091 106528905371589198110322137)
  ·
    refine ⟨79896679028691898582741603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106528905371589198110322137 79896679028691898582741603)
    ·
      refine ⟨119845018543037847874112405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79896679028691898582741603 119845018543037847874112405)
      ·
        refine ⟨5617735244204899119099019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 119845018543037847874112405 5617735244204899119099019)
        ·
          refine ⟨8426602866307348678648529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5617735244204899119099019 8426602866307348678648529)
          ·
            refine ⟨6319952149730511508986397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8426602866307348678648529 6319952149730511508986397)
            ·
              refine ⟨2369982056148941815869899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6319952149730511508986397 2369982056148941815869899)
              ·
                refine ⟨3554973084223412723804849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2369982056148941815869899 3554973084223412723804849)
                ·
                  refine ⟨2666229813167559542853637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3554973084223412723804849 2666229813167559542853637)
                  ·
                    refine ⟨499918089968917414285057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2666229813167559542853637 499918089968917414285057)
                    ·
                      rfl

theorem cell23_2920761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 2, 4].length) (baseStart_2920761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920761 prefixEnd_2920761 := by exact prefixLift 2920761
  have htrace : WordTrace (prefixWord ++ tailWord_2920761) baseStart_2920761 baseEnd_2920761 := by
    simpa [prefixWord, tailWord_2920761, baseEnd_2920761] using wordTrace_append hprefix tailTrace_2920761
  have hstable : (prefixWord ++ tailWord_2920761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920761).length < 2 ^ (prefixWord ++ tailWord_2920761).sum := by decide
  have hdescent : baseEnd_2920761 < baseStart_2920761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920780 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 1, 4, 5]
def baseStart_2920780 : Nat := 118140960795 + 2920780 * 2 ^ 59
def prefixEnd_2920780 : Nat := 4983230072969 + 3 ^ 40 * 2920780 * 2
def baseEnd_2920780 : Nat := 1499764026039187668517583

theorem tailTrace_2920780 : CollatzResearch.WordTrace tailWord_2920780 prefixEnd_2920780 1499764026039187668517583 := by
  unfold tailWord_2920780
  simp only [CollatzResearch.WordTrace]
  refine ⟨53264799179260182177631897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71019732239013576236842529 53264799179260182177631897)
  ·
    refine ⟨39948599384445136633223923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53264799179260182177631897 39948599384445136633223923)
    ·
      refine ⟨59922899076667704949835885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39948599384445136633223923 59922899076667704949835885)
      ·
        refine ⟨22471087153750389356188457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59922899076667704949835885 22471087153750389356188457)
        ·
          refine ⟨16853315365312792017141343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22471087153750389356188457 16853315365312792017141343)
          ·
            refine ⟨25279973047969188025712015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16853315365312792017141343 25279973047969188025712015)
            ·
              refine ⟨37919959571953782038568023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25279973047969188025712015 37919959571953782038568023)
              ·
                refine ⟨56879939357930673057852035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37919959571953782038568023 56879939357930673057852035)
                ·
                  refine ⟨85319909036896009586778053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56879939357930673057852035 85319909036896009586778053)
                  ·
                    refine ⟨15997482944418001797520885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85319909036896009586778053 15997482944418001797520885)
                    ·
                      refine ⟨1499764026039187668517583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15997482944418001797520885 1499764026039187668517583)
                      ·
                        rfl

theorem cell23_2920780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_2920780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920780 prefixEnd_2920780 := by exact prefixLift 2920780
  have htrace : WordTrace (prefixWord ++ tailWord_2920780) baseStart_2920780 baseEnd_2920780 := by
    simpa [prefixWord, tailWord_2920780, baseEnd_2920780] using wordTrace_append hprefix tailTrace_2920780
  have hstable : (prefixWord ++ tailWord_2920780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920780).length < 2 ^ (prefixWord ++ tailWord_2920780).sum := by decide
  have hdescent : baseEnd_2920780 < baseStart_2920780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920818 : List Nat := [3, 2, 1, 2, 1, 5, 2, 1, 2, 1, 3]
def baseStart_2920818 : Nat := 118140960795 + 2920818 * 2 ^ 59
def prefixEnd_2920818 : Nat := 4983230072969 + 3 ^ 40 * 2920818 * 2
def baseEnd_2920818 : Nat := 1499783538304058519842409

theorem tailTrace_2920818 : CollatzResearch.WordTrace tailWord_2920818 prefixEnd_2920818 1499783538304058519842409 := by
  unfold tailWord_2920818
  simp only [CollatzResearch.WordTrace]
  refine ⟨26632746083095674211286777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71020656221588464563431405 26632746083095674211286777)
  ·
    refine ⟨19974559562321755658465083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26632746083095674211286777 19974559562321755658465083)
    ·
      refine ⟨29961839343482633487697625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19974559562321755658465083 29961839343482633487697625)
      ·
        refine ⟨22471379507611975115773219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29961839343482633487697625 22471379507611975115773219)
        ·
          refine ⟨33707069261417962673659829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22471379507611975115773219 33707069261417962673659829)
          ·
            refine ⟨3160037743257934000655609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33707069261417962673659829 3160037743257934000655609)
            ·
              refine ⟨2370028307443450500491707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3160037743257934000655609 2370028307443450500491707)
              ·
                refine ⟨3555042461165175750737561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2370028307443450500491707 3555042461165175750737561)
                ·
                  refine ⟨2666281845873881813053171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3555042461165175750737561 2666281845873881813053171)
                  ·
                    refine ⟨3999422768810822719579757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2666281845873881813053171 3999422768810822719579757)
                    ·
                      refine ⟨1499783538304058519842409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3999422768810822719579757 1499783538304058519842409)
                      ·
                        rfl

theorem cell23_2920818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_2920818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920818 prefixEnd_2920818 := by exact prefixLift 2920818
  have htrace : WordTrace (prefixWord ++ tailWord_2920818) baseStart_2920818 baseEnd_2920818 := by
    simpa [prefixWord, tailWord_2920818, baseEnd_2920818] using wordTrace_append hprefix tailTrace_2920818
  have hstable : (prefixWord ++ tailWord_2920818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920818).length < 2 ^ (prefixWord ++ tailWord_2920818).sum := by decide
  have hdescent : baseEnd_2920818 < baseStart_2920818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920857 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 2, 3, 3]
def baseStart_2920857 : Nat := 118140960795 + 2920857 * 2 ^ 59
def prefixEnd_2920857 : Nat := 4983230072969 + 3 ^ 40 * 2920857 * 2
def baseEnd_2920857 : Nat := 1499803564049583867254729

theorem tailTrace_2920857 : CollatzResearch.WordTrace tailWord_2920857 prefixEnd_2920857 1499803564049583867254729 := by
  unfold tailWord_2920857
  simp only [CollatzResearch.WordTrace]
  refine ⟨106532406779241406505816825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71021604519494271003877883 106532406779241406505816825)
  ·
    refine ⟨79899305084431054879362619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106532406779241406505816825 79899305084431054879362619)
    ·
      refine ⟨119848957626646582319043929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79899305084431054879362619 119848957626646582319043929)
      ·
        refine ⟨89886718219984936739282947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119848957626646582319043929 89886718219984936739282947)
        ·
          refine ⟨134830077329977405108924421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89886718219984936739282947 134830077329977405108924421)
          ·
            refine ⟨25280639499370763457923329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134830077329977405108924421 25280639499370763457923329)
            ·
              refine ⟨18960479624528072593442497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25280639499370763457923329 18960479624528072593442497)
              ·
                refine ⟨14220359718396054445081873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18960479624528072593442497 14220359718396054445081873)
                ·
                  refine ⟨10665269788797040833811405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14220359718396054445081873 10665269788797040833811405)
                  ·
                    refine ⟨3999476170798890312679277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10665269788797040833811405 3999476170798890312679277)
                    ·
                      refine ⟨1499803564049583867254729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3999476170798890312679277 1499803564049583867254729)
                      ·
                        rfl

theorem cell23_2920857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_2920857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920857 prefixEnd_2920857 := by exact prefixLift 2920857
  have htrace : WordTrace (prefixWord ++ tailWord_2920857) baseStart_2920857 baseEnd_2920857 := by
    simpa [prefixWord, tailWord_2920857, baseEnd_2920857] using wordTrace_append hprefix tailTrace_2920857
  have hstable : (prefixWord ++ tailWord_2920857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920857).length < 2 ^ (prefixWord ++ tailWord_2920857).sum := by decide
  have hdescent : baseEnd_2920857 < baseStart_2920857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920858 : List Nat := [3, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2]
def baseStart_2920858 : Nat := 118140960795 + 2920858 * 2 ^ 59
def prefixEnd_2920858 : Nat := 4983230072969 + 3 ^ 40 * 2920858 * 2
def baseEnd_2920858 : Nat := 1499804077530238363342225

theorem tailTrace_2920858 : CollatzResearch.WordTrace tailWord_2920858 prefixEnd_2920858 1499804077530238363342225 := by
  unfold tailWord_2920858
  simp only [CollatzResearch.WordTrace]
  refine ⟨26633110813059445919150807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71021628834825189117735485 26633110813059445919150807)
  ·
    refine ⟨39949666219589168878726211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26633110813059445919150807 39949666219589168878726211)
    ·
      refine ⟨59924499329383753318089317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39949666219589168878726211 59924499329383753318089317)
      ·
        refine ⟨11235843624259453747141747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59924499329383753318089317 11235843624259453747141747)
        ·
          refine ⟨16853765436389180620712621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11235843624259453747141747 16853765436389180620712621)
          ·
            refine ⟨6320162038645942732767233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16853765436389180620712621 6320162038645942732767233)
            ·
              refine ⟨4740121528984457049575425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6320162038645942732767233 4740121528984457049575425)
              ·
                refine ⟨3555091146738342787181569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4740121528984457049575425 3555091146738342787181569)
                ·
                  refine ⟨2666318360053757090386177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3555091146738342787181569 2666318360053757090386177)
                  ·
                    refine ⟨1999738770040317817789633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2666318360053757090386177 1999738770040317817789633)
                    ·
                      refine ⟨1499804077530238363342225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1999738770040317817789633 1499804077530238363342225)
                      ·
                        rfl

theorem cell23_2920858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_2920858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920858 prefixEnd_2920858 := by exact prefixLift 2920858
  have htrace : WordTrace (prefixWord ++ tailWord_2920858) baseStart_2920858 baseEnd_2920858 := by
    simpa [prefixWord, tailWord_2920858, baseEnd_2920858] using wordTrace_append hprefix tailTrace_2920858
  have hstable : (prefixWord ++ tailWord_2920858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920858).length < 2 ^ (prefixWord ++ tailWord_2920858).sum := by decide
  have hdescent : baseEnd_2920858 < baseStart_2920858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920864 : List Nat := [2, 1, 1, 4, 1, 4, 1, 4, 5]
def baseStart_2920864 : Nat := 118140960795 + 2920864 * 2 ^ 59
def prefixEnd_2920864 : Nat := 4983230072969 + 3 ^ 40 * 2920864 * 2
def baseEnd_2920864 : Nat := 166645239823796148874133

theorem tailTrace_2920864 : CollatzResearch.WordTrace tailWord_2920864 prefixEnd_2920864 166645239823796148874133 := by
  unfold tailWord_2920864
  simp only [CollatzResearch.WordTrace]
  refine ⟨53266331045108023350660823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71021774726810697800881097 53266331045108023350660823)
  ·
    refine ⟨79899496567662035025991235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53266331045108023350660823 79899496567662035025991235)
    ·
      refine ⟨119849244851493052538986853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79899496567662035025991235 119849244851493052538986853)
      ·
        refine ⟨22471733409654947351060035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119849244851493052538986853 22471733409654947351060035)
        ·
          refine ⟨33707600114482421026590053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22471733409654947351060035 33707600114482421026590053)
          ·
            refine ⟨6320175021465453942485635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33707600114482421026590053 6320175021465453942485635)
            ·
              refine ⟨9480262532198180913728453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6320175021465453942485635 9480262532198180913728453)
              ·
                refine ⟨1777549224787158921324085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9480262532198180913728453 1777549224787158921324085)
                ·
                  refine ⟨166645239823796148874133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1777549224787158921324085 166645239823796148874133)
                  ·
                    rfl

theorem cell23_2920864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 5].length) (baseStart_2920864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920864 prefixEnd_2920864 := by exact prefixLift 2920864
  have htrace : WordTrace (prefixWord ++ tailWord_2920864) baseStart_2920864 baseEnd_2920864 := by
    simpa [prefixWord, tailWord_2920864, baseEnd_2920864] using wordTrace_append hprefix tailTrace_2920864
  have hstable : (prefixWord ++ tailWord_2920864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920864).length < 2 ^ (prefixWord ++ tailWord_2920864).sum := by decide
  have hdescent : baseEnd_2920864 < baseStart_2920864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920894 : List Nat := [4, 2, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_2920894 : Nat := 118140960795 + 2920894 * 2 ^ 59
def prefixEnd_2920894 : Nat := 4983230072969 + 3 ^ 40 * 2920894 * 2
def baseEnd_2920894 : Nat := 499940854277933407497353

theorem tailTrace_2920894 : CollatzResearch.WordTrace tailWord_2920894 prefixEnd_2920894 499940854277933407497353 := by
  unfold tailWord_2920894
  simp only [CollatzResearch.WordTrace]
  refine ⟨13316719535013420228114217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71022504186738241216609157 13316719535013420228114217)
  ·
    refine ⟨9987539651260065171085663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13316719535013420228114217 9987539651260065171085663)
    ·
      refine ⟨14981309476890097756628495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9987539651260065171085663 14981309476890097756628495)
      ·
        refine ⟨22471964215335146634942743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14981309476890097756628495 22471964215335146634942743)
        ·
          refine ⟨33707946323002719952414115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22471964215335146634942743 33707946323002719952414115)
          ·
            refine ⟨50561919484504079928621173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33707946323002719952414115 50561919484504079928621173)
            ·
              refine ⟨4740179951672257493308235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50561919484504079928621173 4740179951672257493308235)
              ·
                refine ⟨7110269927508386239962353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4740179951672257493308235 7110269927508386239962353)
                ·
                  refine ⟨5332702445631289679971765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7110269927508386239962353 5332702445631289679971765)
                  ·
                    refine ⟨499940854277933407497353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5332702445631289679971765 499940854277933407497353)
                    ·
                      rfl

theorem cell23_2920894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_2920894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920894 prefixEnd_2920894 := by exact prefixLift 2920894
  have htrace : WordTrace (prefixWord ++ tailWord_2920894) baseStart_2920894 baseEnd_2920894 := by
    simpa [prefixWord, tailWord_2920894, baseEnd_2920894] using wordTrace_append hprefix tailTrace_2920894
  have hstable : (prefixWord ++ tailWord_2920894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920894).length < 2 ^ (prefixWord ++ tailWord_2920894).sum := by decide
  have hdescent : baseEnd_2920894 < baseStart_2920894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920907 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 7, 4]
def baseStart_2920907 : Nat := 118140960795 + 2920907 * 2 ^ 59
def prefixEnd_2920907 : Nat := 4983230072969 + 3 ^ 40 * 2920907 * 2
def baseEnd_2920907 : Nat := 499943079360769557209833

theorem tailTrace_2920907 : CollatzResearch.WordTrace tailWord_2920907 prefixEnd_2920907 499943079360769557209833 := by
  unfold tailWord_2920907
  simp only [CollatzResearch.WordTrace]
  refine ⟨106534230429060265045136975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71022820286040176696757983 106534230429060265045136975)
  ·
    refine ⟨159801345643590397567705463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106534230429060265045136975 159801345643590397567705463)
    ·
      refine ⟨239702018465385596351558195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159801345643590397567705463 239702018465385596351558195)
      ·
        refine ⟨359553027698078394527337293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239702018465385596351558195 359553027698078394527337293)
        ·
          refine ⟨134832385386779397947751485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359553027698078394527337293 134832385386779397947751485)
          ·
            refine ⟨50562144520042274230406807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134832385386779397947751485 50562144520042274230406807)
            ·
              refine ⟨75843216780063411345610211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50562144520042274230406807 75843216780063411345610211)
              ·
                refine ⟨113764825170095117018415317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75843216780063411345610211 113764825170095117018415317)
                ·
                  refine ⟨2666363089924104305119109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 113764825170095117018415317 2666363089924104305119109)
                  ·
                    refine ⟨499943079360769557209833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2666363089924104305119109 499943079360769557209833)
                    ·
                      rfl

theorem cell23_2920907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 4].length) (baseStart_2920907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920907 prefixEnd_2920907 := by exact prefixLift 2920907
  have htrace : WordTrace (prefixWord ++ tailWord_2920907) baseStart_2920907 baseEnd_2920907 := by
    simpa [prefixWord, tailWord_2920907, baseEnd_2920907] using wordTrace_append hprefix tailTrace_2920907
  have hstable : (prefixWord ++ tailWord_2920907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920907).length < 2 ^ (prefixWord ++ tailWord_2920907).sum := by decide
  have hdescent : baseEnd_2920907 < baseStart_2920907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920941 : List Nat := [1, 5, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_2920941 : Nat := 118140960795 + 2920941 * 2 ^ 59
def prefixEnd_2920941 : Nat := 4983230072969 + 3 ^ 40 * 2920941 * 2
def baseEnd_2920941 : Nat := 499948898808187179534781

theorem tailTrace_2920941 : CollatzResearch.WordTrace tailWord_2920941 prefixEnd_2920941 499948898808187179534781 := by
  unfold tailWord_2920941
  simp only [CollatzResearch.WordTrace]
  refine ⟨106535470510937088851874677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71023647007291392567916451 106535470510937088851874677)
  ·
    refine ⟨9987700360400352079863251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106535470510937088851874677 9987700360400352079863251)
    ·
      refine ⟨14981550540600528119794877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9987700360400352079863251 14981550540600528119794877)
      ·
        refine ⟨5618081452725198044923079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14981550540600528119794877 5618081452725198044923079)
        ·
          refine ⟨8427122179087797067384619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5618081452725198044923079 8427122179087797067384619)
          ·
            refine ⟨12640683268631695601076929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8427122179087797067384619 12640683268631695601076929)
            ·
              refine ⟨9480512451473771700807697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12640683268631695601076929 9480512451473771700807697)
              ·
                refine ⟨7110384338605328775605773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9480512451473771700807697 7110384338605328775605773)
                ·
                  refine ⟨2666394126976998290852165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7110384338605328775605773 2666394126976998290852165)
                  ·
                    refine ⟨499948898808187179534781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2666394126976998290852165 499948898808187179534781)
                    ·
                      rfl

theorem cell23_2920941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_2920941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920941 prefixEnd_2920941 := by exact prefixLift 2920941
  have htrace : WordTrace (prefixWord ++ tailWord_2920941) baseStart_2920941 baseEnd_2920941 := by
    simpa [prefixWord, tailWord_2920941, baseEnd_2920941] using wordTrace_append hprefix tailTrace_2920941
  have hstable : (prefixWord ++ tailWord_2920941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920941).length < 2 ^ (prefixWord ++ tailWord_2920941).sum := by decide
  have hdescent : baseEnd_2920941 < baseStart_2920941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2920947 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 3]
def baseStart_2920947 : Nat := 118140960795 + 2920947 * 2 ^ 59
def prefixEnd_2920947 : Nat := 4983230072969 + 3 ^ 40 * 2920947 * 2
def baseEnd_2920947 : Nat := 1499849777308488515129315

theorem tailTrace_2920947 : CollatzResearch.WordTrace tailWord_2920947 prefixEnd_2920947 1499849777308488515129315 := by
  unfold tailWord_2920947
  simp only [CollatzResearch.WordTrace]
  refine ⟨106535689348915351876593095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71023792899276901251062063 106535689348915351876593095)
  ·
    refine ⟨159803534023373027814889643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106535689348915351876593095 159803534023373027814889643)
    ·
      refine ⟨239705301035059541722334465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159803534023373027814889643 239705301035059541722334465)
      ·
        refine ⟨179778975776294656291750849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239705301035059541722334465 179778975776294656291750849)
        ·
          refine ⟨134834231832220992218813137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179778975776294656291750849 134834231832220992218813137)
          ·
            refine ⟨101125673874165744164109853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134834231832220992218813137 101125673874165744164109853)
            ·
              refine ⟨37922127702812154061541195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101125673874165744164109853 37922127702812154061541195)
              ·
                refine ⟨56883191554218231092311793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37922127702812154061541195 56883191554218231092311793)
                ·
                  refine ⟨42662393665663673319233845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56883191554218231092311793 42662393665663673319233845)
                  ·
                    refine ⟨3999599406155969373678173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42662393665663673319233845 3999599406155969373678173)
                    ·
                      refine ⟨1499849777308488515129315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3999599406155969373678173 1499849777308488515129315)
                      ·
                        rfl

theorem cell23_2920947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 3].length) (baseStart_2920947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2920947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2920947 prefixEnd_2920947 := by exact prefixLift 2920947
  have htrace : WordTrace (prefixWord ++ tailWord_2920947) baseStart_2920947 baseEnd_2920947 := by
    simpa [prefixWord, tailWord_2920947, baseEnd_2920947] using wordTrace_append hprefix tailTrace_2920947
  have hstable : (prefixWord ++ tailWord_2920947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2920947).length < 2 ^ (prefixWord ++ tailWord_2920947).sum := by decide
  have hdescent : baseEnd_2920947 < baseStart_2920947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2920947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921004 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 2, 6, 2]
def baseStart_2921004 : Nat := 118140960795 + 2921004 * 2 ^ 59
def prefixEnd_2921004 : Nat := 4983230072969 + 3 ^ 40 * 2921004 * 2
def baseEnd_2921004 : Nat := 1499879045705794792116553

theorem tailTrace_2921004 : CollatzResearch.WordTrace tailWord_2921004 prefixEnd_2921004 1499879045705794792116553 := by
  unfold tailWord_2921004
  simp only [CollatzResearch.WordTrace]
  refine ⟨53268884154854425305709033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71025178873139233740945377 53268884154854425305709033)
  ·
    refine ⟨39951663116140818979281775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53268884154854425305709033 39951663116140818979281775)
    ·
      refine ⟨59927494674211228468922663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39951663116140818979281775 59927494674211228468922663)
      ·
        refine ⟨89891242011316842703383995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59927494674211228468922663 89891242011316842703383995)
        ·
          refine ⟨134836863016975264055075993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89891242011316842703383995 134836863016975264055075993)
          ·
            refine ⟨101127647262731448041306995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134836863016975264055075993 101127647262731448041306995)
            ·
              refine ⟨151691470894097172061960493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101127647262731448041306995 151691470894097172061960493)
              ·
                refine ⟨56884301585286439523235185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151691470894097172061960493 56884301585286439523235185)
                ·
                  refine ⟨42663226188964829642426389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56884301585286439523235185 42663226188964829642426389)
                  ·
                    refine ⟨1999838727607726389488737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42663226188964829642426389 1999838727607726389488737)
                    ·
                      refine ⟨1499879045705794792116553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1999838727607726389488737 1499879045705794792116553)
                      ·
                        rfl

theorem cell23_2921004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 6, 2].length) (baseStart_2921004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921004 prefixEnd_2921004 := by exact prefixLift 2921004
  have htrace : WordTrace (prefixWord ++ tailWord_2921004) baseStart_2921004 baseEnd_2921004 := by
    simpa [prefixWord, tailWord_2921004, baseEnd_2921004] using wordTrace_append hprefix tailTrace_2921004
  have hstable : (prefixWord ++ tailWord_2921004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921004).length < 2 ^ (prefixWord ++ tailWord_2921004).sum := by decide
  have hdescent : baseEnd_2921004 < baseStart_2921004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921024 : List Nat := [2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 5]
def baseStart_2921024 : Nat := 118140960795 + 2921024 * 2 ^ 59
def prefixEnd_2921024 : Nat := 4983230072969 + 3 ^ 40 * 2921024 * 2
def baseEnd_2921024 : Nat := 1499889315318884713866461

theorem tailTrace_2921024 : CollatzResearch.WordTrace tailWord_2921024 prefixEnd_2921024 1499889315318884713866461 := by
  unfold tailWord_2921024
  simp only [CollatzResearch.WordTrace]
  refine ⟨53269248884818197013573063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71025665179757596018097417 53269248884818197013573063)
  ·
    refine ⟨79903873327227295520359595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53269248884818197013573063 79903873327227295520359595)
    ·
      refine ⟨119855809990840943280539393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79903873327227295520359595 119855809990840943280539393)
      ·
        refine ⟨89891857493130707460404545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119855809990840943280539393 89891857493130707460404545)
        ·
          refine ⟨67418893119848030595303409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89891857493130707460404545 67418893119848030595303409)
          ·
            refine ⟨50564169839886022946477557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67418893119848030595303409 50564169839886022946477557)
            ·
              refine ⟨4740390922489314651232271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50564169839886022946477557 4740390922489314651232271)
              ·
                refine ⟨7110586383733971976848407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4740390922489314651232271 7110586383733971976848407)
                ·
                  refine ⟨10665879575600957965272611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7110586383733971976848407 10665879575600957965272611)
                  ·
                    refine ⟨15998819363401436947908917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10665879575600957965272611 15998819363401436947908917)
                    ·
                      refine ⟨1499889315318884713866461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15998819363401436947908917 1499889315318884713866461)
                      ·
                        rfl

theorem cell23_2921024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_2921024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921024 prefixEnd_2921024 := by exact prefixLift 2921024
  have htrace : WordTrace (prefixWord ++ tailWord_2921024) baseStart_2921024 baseEnd_2921024 := by
    simpa [prefixWord, tailWord_2921024, baseEnd_2921024] using wordTrace_append hprefix tailTrace_2921024
  have hstable : (prefixWord ++ tailWord_2921024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921024).length < 2 ^ (prefixWord ++ tailWord_2921024).sum := by decide
  have hdescent : baseEnd_2921024 < baseStart_2921024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921031 : List Nat := [1, 1, 4, 1, 4, 1, 1, 4, 2, 4]
def baseStart_2921031 : Nat := 118140960795 + 2921031 * 2 ^ 59
def prefixEnd_2921031 : Nat := 4983230072969 + 3 ^ 40 * 2921031 * 2
def baseEnd_2921031 : Nat := 499964303227822062159643

theorem tailTrace_2921031 : CollatzResearch.WordTrace tailWord_2921031 prefixEnd_2921031 499964303227822062159643 := by
  unfold tailWord_2921031
  simp only [CollatzResearch.WordTrace]
  refine ⟨106538753080611034222650947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71025835387074022815100631 106538753080611034222650947)
  ·
    refine ⟨159808129620916551333976421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106538753080611034222650947 159808129620916551333976421)
    ·
      refine ⟨29964024303921853375120579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159808129620916551333976421 29964024303921853375120579)
      ·
        refine ⟨44946036455882780062680869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29964024303921853375120579 44946036455882780062680869)
        ·
          refine ⟨8427381835478021261752663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44946036455882780062680869 8427381835478021261752663)
          ·
            refine ⟨12641072753217031892628995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8427381835478021261752663 12641072753217031892628995)
            ·
              refine ⟨18961609129825547838943493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12641072753217031892628995 18961609129825547838943493)
              ·
                refine ⟨3555301711842290219801905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18961609129825547838943493 3555301711842290219801905)
                ·
                  refine ⟨2666476283881717664851429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3555301711842290219801905 2666476283881717664851429)
                  ·
                    refine ⟨499964303227822062159643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2666476283881717664851429 499964303227822062159643)
                    ·
                      rfl

theorem cell23_2921031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_2921031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921031 prefixEnd_2921031 := by exact prefixLift 2921031
  have htrace : WordTrace (prefixWord ++ tailWord_2921031) baseStart_2921031 baseEnd_2921031 := by
    simpa [prefixWord, tailWord_2921031, baseEnd_2921031] using wordTrace_append hprefix tailTrace_2921031
  have hstable : (prefixWord ++ tailWord_2921031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921031).length < 2 ^ (prefixWord ++ tailWord_2921031).sum := by decide
  have hdescent : baseEnd_2921031 < baseStart_2921031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921044 : List Nat := [2, 4, 1, 1, 1, 3, 3, 8]
def baseStart_2921044 : Nat := 118140960795 + 2921044 * 2 ^ 59
def prefixEnd_2921044 : Nat := 4983230072969 + 3 ^ 40 * 2921044 * 2
def baseEnd_2921044 : Nat := 55551836478962023541347

theorem tailTrace_2921044 : CollatzResearch.WordTrace tailWord_2921044 prefixEnd_2921044 55551836478962023541347 := by
  unfold tailWord_2921044
  simp only [CollatzResearch.WordTrace]
  refine ⟨53269613614781968721437093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71026151486375958295249457 53269613614781968721437093)
  ·
    refine ⟨9988052552771619135269455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53269613614781968721437093 9988052552771619135269455)
    ·
      refine ⟨14982078829157428702904183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9988052552771619135269455 14982078829157428702904183)
      ·
        refine ⟨22473118243736143054356275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14982078829157428702904183 22473118243736143054356275)
        ·
          refine ⟨33709677365604214581534413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22473118243736143054356275 33709677365604214581534413)
          ·
            refine ⟨12641129012101580468075405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33709677365604214581534413 12641129012101580468075405)
            ·
              refine ⟨4740423379538092675528277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12641129012101580468075405 4740423379538092675528277)
              ·
                refine ⟨55551836478962023541347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4740423379538092675528277 55551836478962023541347)
                ·
                  rfl

theorem cell23_2921044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 8].length) (baseStart_2921044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921044 prefixEnd_2921044 := by exact prefixLift 2921044
  have htrace : WordTrace (prefixWord ++ tailWord_2921044) baseStart_2921044 baseEnd_2921044 := by
    simpa [prefixWord, tailWord_2921044, baseEnd_2921044] using wordTrace_append hprefix tailTrace_2921044
  have hstable : (prefixWord ++ tailWord_2921044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921044).length < 2 ^ (prefixWord ++ tailWord_2921044).sum := by decide
  have hdescent : baseEnd_2921044 < baseStart_2921044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921061 : List Nat := [1, 3, 1, 3, 4, 1, 3, 7]
def baseStart_2921061 : Nat := 118140960795 + 2921061 * 2 ^ 59
def prefixEnd_2921061 : Nat := 4983230072969 + 3 ^ 40 * 2921061 * 2
def baseEnd_2921061 : Nat := 55552159781596335892733

theorem tailTrace_2921061 : CollatzResearch.WordTrace tailWord_2921061 prefixEnd_2921061 55552159781596335892733 := by
  unfold tailWord_2921061
  simp only [CollatzResearch.WordTrace]
  refine ⟨106539847270502349346243037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71026564847001566230828691 106539847270502349346243037)
  ·
    refine ⟨39952442726438381004841139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106539847270502349346243037 39952442726438381004841139)
    ·
      refine ⟨59928664089657571507261709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39952442726438381004841139 59928664089657571507261709)
      ·
        refine ⟨22473249033621589315223141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59928664089657571507261709 22473249033621589315223141)
        ·
          refine ⟨4213734193804047996604339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22473249033621589315223141 4213734193804047996604339)
          ·
            refine ⟨6320601290706071994906509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4213734193804047996604339 6320601290706071994906509)
            ·
              refine ⟨2370225484014776998089941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6320601290706071994906509 2370225484014776998089941)
              ·
                refine ⟨55552159781596335892733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2370225484014776998089941 55552159781596335892733)
                ·
                  rfl

theorem cell23_2921061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 7].length) (baseStart_2921061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921061 prefixEnd_2921061 := by exact prefixLift 2921061
  have htrace : WordTrace (prefixWord ++ tailWord_2921061) baseStart_2921061 baseEnd_2921061 := by
    simpa [prefixWord, tailWord_2921061, baseEnd_2921061] using wordTrace_append hprefix tailTrace_2921061
  have hstable : (prefixWord ++ tailWord_2921061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921061).length < 2 ^ (prefixWord ++ tailWord_2921061).sum := by decide
  have hdescent : baseEnd_2921061 < baseStart_2921061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921072 : List Nat := [2, 1, 1, 1, 7, 1, 2, 3, 1, 2, 2]
def baseStart_2921072 : Nat := 118140960795 + 2921072 * 2 ^ 59
def prefixEnd_2921072 : Nat := 4983230072969 + 3 ^ 40 * 2921072 * 2
def baseEnd_2921072 : Nat := 1499913962390300526066241

theorem tailTrace_2921072 : CollatzResearch.WordTrace tailWord_2921072 prefixEnd_2921072 1499913962390300526066241 := by
  unfold tailWord_2921072
  simp only [CollatzResearch.WordTrace]
  refine ⟨53270124236731249112446735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71026832315641665483262313 53270124236731249112446735)
  ·
    refine ⟨79905186355096873668670103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53270124236731249112446735 79905186355096873668670103)
    ·
      refine ⟨119857779532645310503005155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79905186355096873668670103 119857779532645310503005155)
      ·
        refine ⟨179786669298967965754507733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119857779532645310503005155 179786669298967965754507733)
        ·
          refine ⟨4213750061694561697371275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 179786669298967965754507733 4213750061694561697371275)
          ·
            refine ⟨6320625092541842546056913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4213750061694561697371275 6320625092541842546056913)
            ·
              refine ⟨4740468819406381909542685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6320625092541842546056913 4740468819406381909542685)
              ·
                refine ⟨1777675807277393216078507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4740468819406381909542685 1777675807277393216078507)
                ·
                  refine ⟨2666513710916089824117761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1777675807277393216078507 2666513710916089824117761)
                  ·
                    refine ⟨1999885283187067368088321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2666513710916089824117761 1999885283187067368088321)
                    ·
                      refine ⟨1499913962390300526066241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1999885283187067368088321 1499913962390300526066241)
                      ·
                        rfl

theorem cell23_2921072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 1, 2, 2].length) (baseStart_2921072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921072 prefixEnd_2921072 := by exact prefixLift 2921072
  have htrace : WordTrace (prefixWord ++ tailWord_2921072) baseStart_2921072 baseEnd_2921072 := by
    simpa [prefixWord, tailWord_2921072, baseEnd_2921072] using wordTrace_append hprefix tailTrace_2921072
  have hstable : (prefixWord ++ tailWord_2921072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921072).length < 2 ^ (prefixWord ++ tailWord_2921072).sum := by decide
  have hdescent : baseEnd_2921072 < baseStart_2921072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921088 : List Nat := [2, 1, 1, 2, 1, 5, 3, 2, 2, 1, 3]
def baseStart_2921088 : Nat := 118140960795 + 2921088 * 2 ^ 59
def prefixEnd_2921088 : Nat := 4983230072969 + 3 ^ 40 * 2921088 * 2
def baseEnd_2921088 : Nat := 1499922178080772463466167

theorem tailTrace_2921088 : CollatzResearch.WordTrace tailWord_2921088 prefixEnd_2921088 1499922178080772463466167 := by
  unfold tailWord_2921088
  simp only [CollatzResearch.WordTrace]
  refine ⟨53270416020702266478737959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71027221360936355304983945 53270416020702266478737959)
  ·
    refine ⟨79905624031053399718106939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53270416020702266478737959 79905624031053399718106939)
    ·
      refine ⟨119858436046580099577160409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79905624031053399718106939 119858436046580099577160409)
      ·
        refine ⟨89893827034935074682870307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119858436046580099577160409 89893827034935074682870307)
        ·
          refine ⟨134840740552402612024305461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89893827034935074682870307 134840740552402612024305461)
          ·
            refine ⟨12641319426787744877278637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134840740552402612024305461 12641319426787744877278637)
            ·
              refine ⟨4740494785045404328979489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12641319426787744877278637 4740494785045404328979489)
              ·
                refine ⟨3555371088784053246734617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4740494785045404328979489 3555371088784053246734617)
                ·
                  refine ⟨2666528316588039935050963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3555371088784053246734617 2666528316588039935050963)
                  ·
                    refine ⟨3999792474882059902576445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2666528316588039935050963 3999792474882059902576445)
                    ·
                      refine ⟨1499922178080772463466167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3999792474882059902576445 1499922178080772463466167)
                      ·
                        rfl

theorem cell23_2921088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 2, 1, 3].length) (baseStart_2921088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921088 prefixEnd_2921088 := by exact prefixLift 2921088
  have htrace : WordTrace (prefixWord ++ tailWord_2921088) baseStart_2921088 baseEnd_2921088 := by
    simpa [prefixWord, tailWord_2921088, baseEnd_2921088] using wordTrace_append hprefix tailTrace_2921088
  have hstable : (prefixWord ++ tailWord_2921088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921088).length < 2 ^ (prefixWord ++ tailWord_2921088).sum := by decide
  have hdescent : baseEnd_2921088 < baseStart_2921088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921151 : List Nat := [1, 1, 2, 2, 2, 6, 1, 1, 7]
def baseStart_2921151 : Nat := 118140960795 + 2921151 * 2 ^ 59
def prefixEnd_2921151 : Nat := 4983230072969 + 3 ^ 40 * 2921151 * 2
def baseEnd_2921151 : Nat := 166661614151333968553153

theorem tailTrace_2921151 : CollatzResearch.WordTrace tailWord_2921151 prefixEnd_2921151 166661614151333968553153 := by
  unfold tailWord_2921151
  simp only [CollatzResearch.WordTrace]
  refine ⟨106543129840176294717019307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71028753226784196478012871 106543129840176294717019307)
  ·
    refine ⟨159814694760264442075528961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106543129840176294717019307 159814694760264442075528961)
    ·
      refine ⟨119861021070198331556646721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159814694760264442075528961 119861021070198331556646721)
      ·
        refine ⟨89895765802648748667485041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119861021070198331556646721 89895765802648748667485041)
        ·
          refine ⟨67421824351986561500613781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89895765802648748667485041 67421824351986561500613781)
          ·
            refine ⟨3160398016499370070341271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67421824351986561500613781 3160398016499370070341271)
            ·
              refine ⟨4740597024749055105511907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3160398016499370070341271 4740597024749055105511907)
              ·
                refine ⟨7110895537123582658267861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4740597024749055105511907 7110895537123582658267861)
                ·
                  refine ⟨166661614151333968553153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7110895537123582658267861 166661614151333968553153)
                  ·
                    rfl

theorem cell23_2921151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 7].length) (baseStart_2921151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921151 prefixEnd_2921151 := by exact prefixLift 2921151
  have htrace : WordTrace (prefixWord ++ tailWord_2921151) baseStart_2921151 baseEnd_2921151 := by
    simpa [prefixWord, tailWord_2921151, baseEnd_2921151] using wordTrace_append hprefix tailTrace_2921151
  have hstable : (prefixWord ++ tailWord_2921151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921151).length < 2 ^ (prefixWord ++ tailWord_2921151).sum := by decide
  have hdescent : baseEnd_2921151 < baseStart_2921151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921162 : List Nat := [3, 1, 2, 1, 4, 1, 4, 1, 2, 2, 2]
def baseStart_2921162 : Nat := 118140960795 + 2921162 * 2 ^ 59
def prefixEnd_2921162 : Nat := 4983230072969 + 3 ^ 40 * 2921162 * 2
def baseEnd_2921162 : Nat := 1499960175649205173940827

theorem tailTrace_2921162 : CollatzResearch.WordTrace tailWord_2921162 prefixEnd_2921162 1499960175649205173940827 := by
  unfold tailWord_2921162
  simp only [CollatzResearch.WordTrace]
  refine ⟨26635882760784110898917435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71029020695424295730446493 26635882760784110898917435)
  ·
    refine ⟨39953824141176166348376153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26635882760784110898917435 39953824141176166348376153)
    ·
      refine ⟨29965368105882124761282115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39953824141176166348376153 29965368105882124761282115)
      ·
        refine ⟨44948052158823187141923173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29965368105882124761282115 44948052158823187141923173)
        ·
          refine ⟨8427759779779347589110595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44948052158823187141923173 8427759779779347589110595)
          ·
            refine ⟨12641639669669021383665893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8427759779779347589110595 12641639669669021383665893)
            ·
              refine ⟨2370307438062941509437355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12641639669669021383665893 2370307438062941509437355)
              ·
                refine ⟨3555461157094412264156033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2370307438062941509437355 3555461157094412264156033)
                ·
                  refine ⟨2666595867820809198117025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3555461157094412264156033 2666595867820809198117025)
                  ·
                    refine ⟨1999946900865606898587769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2666595867820809198117025 1999946900865606898587769)
                    ·
                      refine ⟨1499960175649205173940827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1999946900865606898587769 1499960175649205173940827)
                      ·
                        rfl

theorem cell23_2921162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_2921162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921162 prefixEnd_2921162 := by exact prefixLift 2921162
  have htrace : WordTrace (prefixWord ++ tailWord_2921162) baseStart_2921162 baseEnd_2921162 := by
    simpa [prefixWord, tailWord_2921162, baseEnd_2921162] using wordTrace_append hprefix tailTrace_2921162
  have hstable : (prefixWord ++ tailWord_2921162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921162).length < 2 ^ (prefixWord ++ tailWord_2921162).sum := by decide
  have hdescent : baseEnd_2921162 < baseStart_2921162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921201 : List Nat := [1, 2, 2, 2, 2, 2, 1, 4, 2, 1, 4]
def baseStart_2921201 : Nat := 118140960795 + 2921201 * 2 ^ 59
def prefixEnd_2921201 : Nat := 4983230072969 + 3 ^ 40 * 2921201 * 2
def baseEnd_2921201 : Nat := 1499980201394730521353147

theorem tailTrace_2921201 : CollatzResearch.WordTrace tailWord_2921201 prefixEnd_2921201 1499980201394730521353147 := by
  unfold tailWord_2921201
  simp only [CollatzResearch.WordTrace]
  refine ⟨106544953489995153256339457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71029968993330102170892971 106544953489995153256339457)
  ·
    refine ⟨79908715117496364942254593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106544953489995153256339457 79908715117496364942254593)
    ·
      refine ⟨59931536338122273706690945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79908715117496364942254593 59931536338122273706690945)
      ·
        refine ⟨44948652253591705280018209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59931536338122273706690945 44948652253591705280018209)
        ·
          refine ⟨33711489190193778960013657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44948652253591705280018209 33711489190193778960013657)
          ·
            refine ⟨25283616892645334220010243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33711489190193778960013657 25283616892645334220010243)
            ·
              refine ⟨37925425338968001330015365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25283616892645334220010243 37925425338968001330015365)
              ·
                refine ⟨7111017251056500249377881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37925425338968001330015365 7111017251056500249377881)
                ·
                  refine ⟨5333262938292375187033411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7111017251056500249377881 5333262938292375187033411)
                  ·
                    refine ⟨7999894407438562780550117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5333262938292375187033411 7999894407438562780550117)
                    ·
                      refine ⟨1499980201394730521353147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7999894407438562780550117 1499980201394730521353147)
                      ·
                        rfl

theorem cell23_2921201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_2921201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921201 prefixEnd_2921201 := by exact prefixLift 2921201
  have htrace : WordTrace (prefixWord ++ tailWord_2921201) baseStart_2921201 baseEnd_2921201 := by
    simpa [prefixWord, tailWord_2921201, baseEnd_2921201] using wordTrace_append hprefix tailTrace_2921201
  have hstable : (prefixWord ++ tailWord_2921201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921201).length < 2 ^ (prefixWord ++ tailWord_2921201).sum := by decide
  have hdescent : baseEnd_2921201 < baseStart_2921201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921221 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 4, 2, 3]
def baseStart_2921221 : Nat := 118140960795 + 2921221 * 2 ^ 59
def prefixEnd_2921221 : Nat := 4983230072969 + 3 ^ 40 * 2921221 * 2
def baseEnd_2921221 : Nat := 1499990471007820443103055

theorem tailTrace_2921221 : CollatzResearch.WordTrace tailWord_2921221 prefixEnd_2921221 1499990471007820443103055 := by
  unfold tailWord_2921221
  simp only [CollatzResearch.WordTrace]
  refine ⟨106545682949922696672067517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71030455299948464448045011 106545682949922696672067517)
  ·
    refine ⟨39954631106221011252025319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106545682949922696672067517 39954631106221011252025319)
    ·
      refine ⟨59931946659331516878037979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39954631106221011252025319 59931946659331516878037979)
      ·
        refine ⟨89897919988997275317056969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59931946659331516878037979 89897919988997275317056969)
        ·
          refine ⟨67423439991747956487792727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89897919988997275317056969 67423439991747956487792727)
          ·
            refine ⟨101135159987621934731689091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67423439991747956487792727 101135159987621934731689091)
            ·
              refine ⟨151702739981432902097533637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101135159987621934731689091 151702739981432902097533637)
              ·
                refine ⟨28444263746518669143287557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151702739981432902097533637 28444263746518669143287557)
                ·
                  refine ⟨5333299452472250464366417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28444263746518669143287557 5333299452472250464366417)
                  ·
                    refine ⟨3999974589354187848274813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5333299452472250464366417 3999974589354187848274813)
                    ·
                      refine ⟨1499990471007820443103055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3999974589354187848274813 1499990471007820443103055)
                      ·
                        rfl

theorem cell23_2921221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_2921221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921221 prefixEnd_2921221 := by exact prefixLift 2921221
  have htrace : WordTrace (prefixWord ++ tailWord_2921221) baseStart_2921221 baseEnd_2921221 := by
    simpa [prefixWord, tailWord_2921221, baseEnd_2921221] using wordTrace_append hprefix tailTrace_2921221
  have hstable : (prefixWord ++ tailWord_2921221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921221).length < 2 ^ (prefixWord ++ tailWord_2921221).sum := by decide
  have hdescent : baseEnd_2921221 < baseStart_2921221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921262 : List Nat := [4, 1, 3, 2, 1, 1, 2, 4, 1, 4]
def baseStart_2921262 : Nat := 118140960795 + 2921262 * 2 ^ 59
def prefixEnd_2921262 : Nat := 4983230072969 + 3 ^ 40 * 2921262 * 2
def baseEnd_2921262 : Nat := 500003841238218260896789

theorem tailTrace_2921262 : CollatzResearch.WordTrace tailWord_2921262 prefixEnd_2921262 500003841238218260896789 := by
  unfold tailWord_2921262
  simp only [CollatzResearch.WordTrace]
  refine ⟨13318397292846770084288755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71031452228516107116206693 13318397292846770084288755)
  ·
    refine ⟨19977595939270155126433133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13318397292846770084288755 19977595939270155126433133)
    ·
      refine ⟨7491598477226308172412425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19977595939270155126433133 7491598477226308172412425)
      ·
        refine ⟨5618698857919731129309319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7491598477226308172412425 5618698857919731129309319)
        ·
          refine ⟨8428048286879596693963979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5618698857919731129309319 8428048286879596693963979)
          ·
            refine ⟨12642072430319395040945969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8428048286879596693963979 12642072430319395040945969)
            ·
              refine ⟨9481554322739546280709477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12642072430319395040945969 9481554322739546280709477)
              ·
                refine ⟨1777791435513664927633027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9481554322739546280709477 1777791435513664927633027)
                ·
                  refine ⟨2666687153270497391449541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1777791435513664927633027 2666687153270497391449541)
                  ·
                    refine ⟨500003841238218260896789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2666687153270497391449541 500003841238218260896789)
                    ·
                      rfl

theorem cell23_2921262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_2921262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921262 prefixEnd_2921262 := by exact prefixLift 2921262
  have htrace : WordTrace (prefixWord ++ tailWord_2921262) baseStart_2921262 baseEnd_2921262 := by
    simpa [prefixWord, tailWord_2921262, baseEnd_2921262] using wordTrace_append hprefix tailTrace_2921262
  have hstable : (prefixWord ++ tailWord_2921262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921262).length < 2 ^ (prefixWord ++ tailWord_2921262).sum := by decide
  have hdescent : baseEnd_2921262 < baseStart_2921262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921288 : List Nat := [2, 1, 3, 1, 1, 3, 4, 2, 1, 5]
def baseStart_2921288 : Nat := 118140960795 + 2921288 * 2 ^ 59
def prefixEnd_2921288 : Nat := 4983230072969 + 3 ^ 40 * 2921288 * 2
def baseEnd_2921288 : Nat := 500008291403890560321749

theorem tailTrace_2921288 : CollatzResearch.WordTrace tailWord_2921288 prefixEnd_2921288 500008291403890560321749 := by
  unfold tailWord_2921288
  simp only [CollatzResearch.WordTrace]
  refine ⟨53274063320339983557378259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71032084427119978076504345 53274063320339983557378259)
  ·
    refine ⟨79911094980509975336067389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53274063320339983557378259 79911094980509975336067389)
    ·
      refine ⟨29966660617691240751025271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79911094980509975336067389 29966660617691240751025271)
      ·
        refine ⟨44949990926536861126537907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29966660617691240751025271 44949990926536861126537907)
        ·
          refine ⟨67424986389805291689806861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44949990926536861126537907 67424986389805291689806861)
          ·
            refine ⟨25284369896176984383677573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67424986389805291689806861 25284369896176984383677573)
            ·
              refine ⟨4740819355533184571939545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25284369896176984383677573 4740819355533184571939545)
              ·
                refine ⟨3555614516649888428954659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4740819355533184571939545 3555614516649888428954659)
                ·
                  refine ⟨5333421774974832643431989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3555614516649888428954659 5333421774974832643431989)
                  ·
                    refine ⟨500008291403890560321749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5333421774974832643431989 500008291403890560321749)
                    ·
                      rfl

theorem cell23_2921288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_2921288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921288 prefixEnd_2921288 := by exact prefixLift 2921288
  have htrace : WordTrace (prefixWord ++ tailWord_2921288) baseStart_2921288 baseEnd_2921288 := by
    simpa [prefixWord, tailWord_2921288, baseEnd_2921288] using wordTrace_append hprefix tailTrace_2921288
  have hstable : (prefixWord ++ tailWord_2921288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921288).length < 2 ^ (prefixWord ++ tailWord_2921288).sum := by decide
  have hdescent : baseEnd_2921288 < baseStart_2921288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921301 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 3, 6]
def baseStart_2921301 : Nat := 118140960795 + 2921301 * 2 ^ 59
def prefixEnd_2921301 : Nat := 4983230072969 + 3 ^ 40 * 2921301 * 2
def baseEnd_2921301 : Nat := 500010516486726710034229

theorem tailTrace_2921301 : CollatzResearch.WordTrace tailWord_2921301 prefixEnd_2921301 500010516486726710034229 := by
  unfold tailWord_2921301
  simp only [CollatzResearch.WordTrace]
  refine ⟨106548600789632870334979757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71032400526421913556653171 106548600789632870334979757)
  ·
    refine ⟨39955725296112326375617409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106548600789632870334979757 39955725296112326375617409)
    ·
      refine ⟨29966793972084244781713057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39955725296112326375617409 29966793972084244781713057)
      ·
        refine ⟨22475095479063183586284793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29966793972084244781713057 22475095479063183586284793)
        ·
          refine ⟨16856321609297387689713595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22475095479063183586284793 16856321609297387689713595)
          ·
            refine ⟨25284482413946081534570393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16856321609297387689713595 25284482413946081534570393)
            ·
              refine ⟨18963361810459561150927795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25284482413946081534570393 18963361810459561150927795)
              ·
                refine ⟨28445042715689341726391693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18963361810459561150927795 28445042715689341726391693)
                ·
                  refine ⟨10666891018383503147396885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28445042715689341726391693 10666891018383503147396885)
                  ·
                    refine ⟨500010516486726710034229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10666891018383503147396885 500010516486726710034229)
                    ·
                      rfl

theorem cell23_2921301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_2921301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921301 prefixEnd_2921301 := by exact prefixLift 2921301
  have htrace : WordTrace (prefixWord ++ tailWord_2921301) baseStart_2921301 baseEnd_2921301 := by
    simpa [prefixWord, tailWord_2921301, baseEnd_2921301] using wordTrace_append hprefix tailTrace_2921301
  have hstable : (prefixWord ++ tailWord_2921301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921301).length < 2 ^ (prefixWord ++ tailWord_2921301).sum := by decide
  have hdescent : baseEnd_2921301 < baseStart_2921301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921319 : List Nat := [1, 1, 5, 1, 2, 3, 3, 2, 1, 1, 3]
def baseStart_2921319 : Nat := 118140960795 + 2921319 * 2 ^ 59
def prefixEnd_2921319 : Nat := 4983230072969 + 3 ^ 40 * 2921319 * 2
def baseEnd_2921319 : Nat := 1500040792111961059677605

theorem tailTrace_2921319 : CollatzResearch.WordTrace tailWord_2921319 prefixEnd_2921319 1500040792111961059677605 := by
  unfold tailWord_2921319
  simp only [CollatzResearch.WordTrace]
  refine ⟨106549257303567659409135011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71032838202378439606090007 106549257303567659409135011)
  ·
    refine ⟨159823885955351489113702517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106549257303567659409135011 159823885955351489113702517)
    ·
      refine ⟨14983489308314202104409611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159823885955351489113702517 14983489308314202104409611)
      ·
        refine ⟨22475233962471303156614417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14983489308314202104409611 22475233962471303156614417)
        ·
          refine ⟨16856425471853477367460813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22475233962471303156614417 16856425471853477367460813)
          ·
            refine ⟨6321159551945054012797805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16856425471853477367460813 6321159551945054012797805)
            ·
              refine ⟨2370434831979395254799177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6321159551945054012797805 2370434831979395254799177)
              ·
                refine ⟨1777826123984546441099383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2370434831979395254799177 1777826123984546441099383)
                ·
                  refine ⟨2666739185976819661649075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1777826123984546441099383 2666739185976819661649075)
                  ·
                    refine ⟨4000108778965229492473613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2666739185976819661649075 4000108778965229492473613)
                    ·
                      refine ⟨1500040792111961059677605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4000108778965229492473613 1500040792111961059677605)
                      ·
                        rfl

theorem cell23_2921319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_2921319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921319 prefixEnd_2921319 := by exact prefixLift 2921319
  have htrace : WordTrace (prefixWord ++ tailWord_2921319) baseStart_2921319 baseEnd_2921319 := by
    simpa [prefixWord, tailWord_2921319, baseEnd_2921319] using wordTrace_append hprefix tailTrace_2921319
  have hstable : (prefixWord ++ tailWord_2921319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921319).length < 2 ^ (prefixWord ++ tailWord_2921319).sum := by decide
  have hdescent : baseEnd_2921319 < baseStart_2921319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921342 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2921342 : Nat := 118140960795 + 2921342 * 2 ^ 59
def prefixEnd_2921342 : Nat := 4983230072969 + 3 ^ 40 * 2921342 * 2
def baseEnd_2921342 : Nat := 1500052602167014469689999

theorem tailTrace_2921342 : CollatzResearch.WordTrace tailWord_2921342 prefixEnd_2921342 1500052602167014469689999 := by
  unfold tailWord_2921342
  simp only [CollatzResearch.WordTrace]
  refine ⟨13318762022810541792152785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71033397454989556224814853 13318762022810541792152785)
  ·
    refine ⟨9989071517107906344114589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13318762022810541792152785 9989071517107906344114589)
    ·
      refine ⟨3745901818915464879042971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9989071517107906344114589 3745901818915464879042971)
      ·
        refine ⟨5618852728373197318564457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3745901818915464879042971 5618852728373197318564457)
        ·
          refine ⟨4214139546279897988923343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5618852728373197318564457 4214139546279897988923343)
          ·
            refine ⟨6321209319419846983385015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4214139546279897988923343 6321209319419846983385015)
            ·
              refine ⟨9481813979129770475077523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6321209319419846983385015 9481813979129770475077523)
              ·
                refine ⟨14222720968694655712616285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9481813979129770475077523 14222720968694655712616285)
                ·
                  refine ⟨5333520363260495892231107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14222720968694655712616285 5333520363260495892231107)
                  ·
                    refine ⟨8000280544890743838346661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5333520363260495892231107 8000280544890743838346661)
                    ·
                      refine ⟨1500052602167014469689999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8000280544890743838346661 1500052602167014469689999)
                      ·
                        rfl

theorem cell23_2921342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2921342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921342 prefixEnd_2921342 := by exact prefixLift 2921342
  have htrace : WordTrace (prefixWord ++ tailWord_2921342) baseStart_2921342 baseEnd_2921342 := by
    simpa [prefixWord, tailWord_2921342, baseEnd_2921342] using wordTrace_append hprefix tailTrace_2921342
  have hstable : (prefixWord ++ tailWord_2921342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921342).length < 2 ^ (prefixWord ++ tailWord_2921342).sum := by decide
  have hdescent : baseEnd_2921342 < baseStart_2921342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921346 : List Nat := [3, 4, 2, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_2921346 : Nat := 118140960795 + 2921346 * 2 ^ 59
def prefixEnd_2921346 : Nat := 4983230072969 + 3 ^ 40 * 2921346 * 2
def baseEnd_2921346 : Nat := 1500054656089632454039981

theorem tailTrace_2921346 : CollatzResearch.WordTrace tailWord_2921346 prefixEnd_2921346 1500054656089632454039981 := by
  unfold tailWord_2921346
  simp only [CollatzResearch.WordTrace]
  refine ⟨26637560518617460755091973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71033494716313228680245261 26637560518617460755091973)
  ·
    refine ⟨4994542597240773891579745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26637560518617460755091973 4994542597240773891579745)
    ·
      refine ⟨3745906947930580418684809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4994542597240773891579745 3745906947930580418684809)
      ·
        refine ⟨2809430210947935314013607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3745906947930580418684809 2809430210947935314013607)
        ·
          refine ⟨4214145316421902971020411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2809430210947935314013607 4214145316421902971020411)
          ·
            refine ⟨6321217974632854456530617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4214145316421902971020411 6321217974632854456530617)
            ·
              refine ⟨4740913480974640842397963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6321217974632854456530617 4740913480974640842397963)
              ·
                refine ⟨7111370221461961263596945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4740913480974640842397963 7111370221461961263596945)
                ·
                  refine ⟨5333527666096470947697709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7111370221461961263596945 5333527666096470947697709)
                  ·
                    refine ⟨2000072874786176605386641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5333527666096470947697709 2000072874786176605386641)
                    ·
                      refine ⟨1500054656089632454039981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2000072874786176605386641 1500054656089632454039981)
                      ·
                        rfl

theorem cell23_2921346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_2921346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921346 prefixEnd_2921346 := by exact prefixLift 2921346
  have htrace : WordTrace (prefixWord ++ tailWord_2921346) baseStart_2921346 baseEnd_2921346 := by
    simpa [prefixWord, tailWord_2921346, baseEnd_2921346] using wordTrace_append hprefix tailTrace_2921346
  have hstable : (prefixWord ++ tailWord_2921346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921346).length < 2 ^ (prefixWord ++ tailWord_2921346).sum := by decide
  have hdescent : baseEnd_2921346 < baseStart_2921346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921362 : List Nat := [3, 2, 3, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_2921362 : Nat := 118140960795 + 2921362 * 2 ^ 59
def prefixEnd_2921362 : Nat := 4983230072969 + 3 ^ 40 * 2921362 * 2
def baseEnd_2921362 : Nat := 1500062871780104391439907

theorem tailTrace_2921362 : CollatzResearch.WordTrace tailWord_2921362 prefixEnd_2921362 1500062871780104391439907 := by
  unfold tailWord_2921362
  simp only [CollatzResearch.WordTrace]
  refine ⟨26637706410602969438237585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71033883761607918501966893 26637706410602969438237585)
  ·
    refine ⟨19978279807952227078678189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26637706410602969438237585 19978279807952227078678189)
    ·
      refine ⟨7491854927982085154504321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19978279807952227078678189 7491854927982085154504321)
      ·
        refine ⟨5618891195986563865878241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7491854927982085154504321 5618891195986563865878241)
        ·
          refine ⟨4214168396989922899408681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5618891195986563865878241 4214168396989922899408681)
          ·
            refine ⟨3160626297742442174556511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4214168396989922899408681 3160626297742442174556511)
            ·
              refine ⟨4740939446613663261834767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3160626297742442174556511 4740939446613663261834767)
              ·
                refine ⟨7111409169920494892752151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4740939446613663261834767 7111409169920494892752151)
                ·
                  refine ⟨10667113754880742339128227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7111409169920494892752151 10667113754880742339128227)
                  ·
                    refine ⟨16000670632321113508692341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10667113754880742339128227 16000670632321113508692341)
                    ·
                      refine ⟨1500062871780104391439907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16000670632321113508692341 1500062871780104391439907)
                      ·
                        rfl

theorem cell23_2921362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_2921362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921362 prefixEnd_2921362 := by exact prefixLift 2921362
  have htrace : WordTrace (prefixWord ++ tailWord_2921362) baseStart_2921362 baseEnd_2921362 := by
    simpa [prefixWord, tailWord_2921362, baseEnd_2921362] using wordTrace_append hprefix tailTrace_2921362
  have hstable : (prefixWord ++ tailWord_2921362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921362).length < 2 ^ (prefixWord ++ tailWord_2921362).sum := by decide
  have hdescent : baseEnd_2921362 < baseStart_2921362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921378 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_2921378 : Nat := 118140960795 + 2921378 * 2 ^ 59
def prefixEnd_2921378 : Nat := 4983230072969 + 3 ^ 40 * 2921378 * 2
def baseEnd_2921378 : Nat := 500023695823525442946611

theorem tailTrace_2921378 : CollatzResearch.WordTrace tailWord_2921378 prefixEnd_2921378 500023695823525442946611 := by
  unfold tailWord_2921378
  simp only [CollatzResearch.WordTrace]
  refine ⟨26637852302588478121383197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71034272806902608323688525 26637852302588478121383197)
  ·
    refine ⟨9989194613470679295518699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26637852302588478121383197 9989194613470679295518699)
    ·
      refine ⟨14983791920206018943278049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9989194613470679295518699 14983791920206018943278049)
      ·
        refine ⟨11237843940154514207458537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14983791920206018943278049 11237843940154514207458537)
        ·
          refine ⟨8428382955115885655593903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11237843940154514207458537 8428382955115885655593903)
          ·
            refine ⟨12642574432673828483390855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8428382955115885655593903 12642574432673828483390855)
            ·
              refine ⟨18963861649010742725086283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12642574432673828483390855 18963861649010742725086283)
              ·
                refine ⟨28445792473516114087629425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18963861649010742725086283 28445792473516114087629425)
                ·
                  refine ⟨21334344355137085565722069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28445792473516114087629425 21334344355137085565722069)
                  ·
                    refine ⟨500023695823525442946611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21334344355137085565722069 500023695823525442946611)
                    ·
                      rfl

theorem cell23_2921378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_2921378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921378 prefixEnd_2921378 := by exact prefixLift 2921378
  have htrace : WordTrace (prefixWord ++ tailWord_2921378) baseStart_2921378 baseEnd_2921378 := by
    simpa [prefixWord, tailWord_2921378, baseEnd_2921378] using wordTrace_append hprefix tailTrace_2921378
  have hstable : (prefixWord ++ tailWord_2921378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921378).length < 2 ^ (prefixWord ++ tailWord_2921378).sum := by decide
  have hdescent : baseEnd_2921378 < baseStart_2921378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921415 : List Nat := [1, 1, 4, 1, 1, 2, 4, 2, 1, 4, 2]
def baseStart_2921415 : Nat := 118140960795 + 2921415 * 2 ^ 59
def prefixEnd_2921415 : Nat := 4983230072969 + 3 ^ 40 * 2921415 * 2
def baseEnd_2921415 : Nat := 1500090086254792684077163

theorem tailTrace_2921415 : CollatzResearch.WordTrace tailWord_2921415 prefixEnd_2921415 1500090086254792684077163 := by
  unfold tailWord_2921415
  simp only [CollatzResearch.WordTrace]
  refine ⟨106552758711219867804629699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71035172474146578536419799 106552758711219867804629699)
  ·
    refine ⟨159829138066829801706944549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106552758711219867804629699 159829138066829801706944549)
    ·
      refine ⟨29967963387530587820052103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159829138066829801706944549 29967963387530587820052103)
      ·
        refine ⟨44951945081295881730078155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29967963387530587820052103 44951945081295881730078155)
        ·
          refine ⟨67427917621943822595117233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44951945081295881730078155 67427917621943822595117233)
          ·
            refine ⟨50570938216457866946337925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67427917621943822595117233 50570938216457866946337925)
            ·
              refine ⟨9482050915585850052438361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50570938216457866946337925 9482050915585850052438361)
              ·
                refine ⟨7111538186689387539328771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9482050915585850052438361 7111538186689387539328771)
                ·
                  refine ⟨10667307280034081308993157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7111538186689387539328771 10667307280034081308993157)
                  ·
                    refine ⟨2000120115006390245436217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10667307280034081308993157 2000120115006390245436217)
                    ·
                      refine ⟨1500090086254792684077163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2000120115006390245436217 1500090086254792684077163)
                      ·
                        rfl

theorem cell23_2921415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_2921415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921415 prefixEnd_2921415 := by exact prefixLift 2921415
  have htrace : WordTrace (prefixWord ++ tailWord_2921415) baseStart_2921415 baseEnd_2921415 := by
    simpa [prefixWord, tailWord_2921415, baseEnd_2921415] using wordTrace_append hprefix tailTrace_2921415
  have hstable : (prefixWord ++ tailWord_2921415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921415).length < 2 ^ (prefixWord ++ tailWord_2921415).sum := by decide
  have hdescent : baseEnd_2921415 < baseStart_2921415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921419 : List Nat := [1, 1, 1, 1, 3, 7, 2, 1, 1, 3, 2]
def baseStart_2921419 : Nat := 118140960795 + 2921419 * 2 ^ 59
def prefixEnd_2921419 : Nat := 4983230072969 + 3 ^ 40 * 2921419 * 2
def baseEnd_2921419 : Nat := 1500092140177410668427145

theorem tailTrace_2921419 : CollatzResearch.WordTrace tailWord_2921419 prefixEnd_2921419 1500092140177410668427145 := by
  unfold tailWord_2921419
  simp only [CollatzResearch.WordTrace]
  refine ⟨106552904603205376487775311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71035269735470250991850207 106552904603205376487775311)
  ·
    refine ⟨159829356904808064731662967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106552904603205376487775311 159829356904808064731662967)
    ·
      refine ⟨239744035357212097097494451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159829356904808064731662967 239744035357212097097494451)
      ·
        refine ⟨359616053035818145646241677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239744035357212097097494451 359616053035818145646241677)
        ·
          refine ⟨134856019888431804617340629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359616053035818145646241677 134856019888431804617340629)
          ·
            refine ⟨3160687966135120420718921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 134856019888431804617340629 3160687966135120420718921)
            ·
              refine ⟨2370515974601340315539191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3160687966135120420718921 2370515974601340315539191)
              ·
                refine ⟨3555773961902010473308787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2370515974601340315539191 3555773961902010473308787)
                ·
                  refine ⟨5333660942853015709963181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3555773961902010473308787 5333660942853015709963181)
                  ·
                    refine ⟨2000122853569880891236193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5333660942853015709963181 2000122853569880891236193)
                    ·
                      refine ⟨1500092140177410668427145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2000122853569880891236193 1500092140177410668427145)
                      ·
                        rfl

theorem cell23_2921419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 1, 3, 2].length) (baseStart_2921419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921419 prefixEnd_2921419 := by exact prefixLift 2921419
  have htrace : WordTrace (prefixWord ++ tailWord_2921419) baseStart_2921419 baseEnd_2921419 := by
    simpa [prefixWord, tailWord_2921419, baseEnd_2921419] using wordTrace_append hprefix tailTrace_2921419
  have hstable : (prefixWord ++ tailWord_2921419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921419).length < 2 ^ (prefixWord ++ tailWord_2921419).sum := by decide
  have hdescent : baseEnd_2921419 < baseStart_2921419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921431 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 9]
def baseStart_2921431 : Nat := 118140960795 + 2921431 * 2 ^ 59
def prefixEnd_2921431 : Nat := 4983230072969 + 3 ^ 40 * 2921431 * 2
def baseEnd_2921431 : Nat := 1500098301945264621477089

theorem tailTrace_2921431 : CollatzResearch.WordTrace tailWord_2921431 prefixEnd_2921431 1500098301945264621477089 := by
  unfold tailWord_2921431
  simp only [CollatzResearch.WordTrace]
  refine ⟨106553342279161902537212147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71035561519441268358141431 106553342279161902537212147)
  ·
    refine ⟨159830013418742853805818221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106553342279161902537212147 159830013418742853805818221)
    ·
      refine ⟨59936255032028570177181833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159830013418742853805818221 59936255032028570177181833)
      ·
        refine ⟨44952191274021427632886375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59936255032028570177181833 44952191274021427632886375)
        ·
          refine ⟨67428286911032141449329563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44952191274021427632886375 67428286911032141449329563)
          ·
            refine ⟨101142430366548212173994345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67428286911032141449329563 101142430366548212173994345)
            ·
              refine ⟨75856822774911159130495759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101142430366548212173994345 75856822774911159130495759)
              ·
                refine ⟨113785234162366738695743639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75856822774911159130495759 113785234162366738695743639)
                ·
                  refine ⟨170677851243550108043615459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113785234162366738695743639 170677851243550108043615459)
                  ·
                    refine ⟨256016776865325162065423189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 170677851243550108043615459 256016776865325162065423189)
                    ·
                      refine ⟨1500098301945264621477089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 256016776865325162065423189 1500098301945264621477089)
                      ·
                        rfl

theorem cell23_2921431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_2921431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921431 prefixEnd_2921431 := by exact prefixLift 2921431
  have htrace : WordTrace (prefixWord ++ tailWord_2921431) baseStart_2921431 baseEnd_2921431 := by
    simpa [prefixWord, tailWord_2921431, baseEnd_2921431] using wordTrace_append hprefix tailTrace_2921431
  have hstable : (prefixWord ++ tailWord_2921431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921431).length < 2 ^ (prefixWord ++ tailWord_2921431).sum := by decide
  have hdescent : baseEnd_2921431 < baseStart_2921431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921432 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 4, 2, 2]
def baseStart_2921432 : Nat := 118140960795 + 2921432 * 2 ^ 59
def prefixEnd_2921432 : Nat := 4983230072969 + 3 ^ 40 * 2921432 * 2
def baseEnd_2921432 : Nat := 1500098815425919117564585

theorem tailTrace_2921432 : CollatzResearch.WordTrace tailWord_2921432 prefixEnd_2921432 1500098815425919117564585 := by
  unfold tailWord_2921432
  simp only [CollatzResearch.WordTrace]
  refine ⟨53276689376079139853999275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71035585834772186471999033 53276689376079139853999275)
  ·
    refine ⟨79915034064118709780998913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53276689376079139853999275 79915034064118709780998913)
    ·
      refine ⟨59936275548089032335749185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79915034064118709780998913 59936275548089032335749185)
      ·
        refine ⟨44952206661066774251811889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59936275548089032335749185 44952206661066774251811889)
        ·
          refine ⟨33714154995800080688858917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44952206661066774251811889 33714154995800080688858917)
          ·
            refine ⟨6321404061712515129161047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33714154995800080688858917 6321404061712515129161047)
            ·
              refine ⟨9482106092568772693741571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6321404061712515129161047 9482106092568772693741571)
              ·
                refine ⟨14223159138853159040612357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9482106092568772693741571 14223159138853159040612357)
                ·
                  refine ⟨2666842338534967320114817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14223159138853159040612357 2666842338534967320114817)
                  ·
                    refine ⟨2000131753901225490086113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2666842338534967320114817 2000131753901225490086113)
                    ·
                      refine ⟨1500098815425919117564585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2000131753901225490086113 1500098815425919117564585)
                      ·
                        rfl

theorem cell23_2921432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_2921432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921432 prefixEnd_2921432 := by exact prefixLift 2921432
  have htrace : WordTrace (prefixWord ++ tailWord_2921432) baseStart_2921432 baseEnd_2921432 := by
    simpa [prefixWord, tailWord_2921432, baseEnd_2921432] using wordTrace_append hprefix tailTrace_2921432
  have hstable : (prefixWord ++ tailWord_2921432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921432).length < 2 ^ (prefixWord ++ tailWord_2921432).sum := by decide
  have hdescent : baseEnd_2921432 < baseStart_2921432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921468 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 1, 7]
def baseStart_2921468 : Nat := 118140960795 + 2921468 * 2 ^ 59
def prefixEnd_2921468 : Nat := 4983230072969 + 3 ^ 40 * 2921468 * 2
def baseEnd_2921468 : Nat := 500039100243160325571473

theorem tailTrace_2921468 : CollatzResearch.WordTrace tailWord_2921468 prefixEnd_2921468 500039100243160325571473 := by
  unfold tailWord_2921468
  simp only [CollatzResearch.WordTrace]
  refine ⟨53277345890013928928154529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71036461186685238570872705 53277345890013928928154529)
  ·
    refine ⟨39958009417510446696115897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53277345890013928928154529 39958009417510446696115897)
    ·
      refine ⟨29968507063132835022086923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39958009417510446696115897 29968507063132835022086923)
      ·
        refine ⟨44952760594699252533130385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29968507063132835022086923 44952760594699252533130385)
        ·
          refine ⟨33714570446024439399847789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44952760594699252533130385 33714570446024439399847789)
          ·
            refine ⟨12642963917259164774942921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33714570446024439399847789 12642963917259164774942921)
            ·
              refine ⟨9482222937944373581207191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12642963917259164774942921 9482222937944373581207191)
              ·
                refine ⟨14223334406916560371810787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9482222937944373581207191 14223334406916560371810787)
                ·
                  refine ⟨21335001610374840557716181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14223334406916560371810787 21335001610374840557716181)
                  ·
                    refine ⟨500039100243160325571473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21335001610374840557716181 500039100243160325571473)
                    ·
                      rfl

theorem cell23_2921468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_2921468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921468 prefixEnd_2921468 := by exact prefixLift 2921468
  have htrace : WordTrace (prefixWord ++ tailWord_2921468) baseStart_2921468 baseEnd_2921468 := by
    simpa [prefixWord, tailWord_2921468, baseEnd_2921468] using wordTrace_append hprefix tailTrace_2921468
  have hstable : (prefixWord ++ tailWord_2921468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921468).length < 2 ^ (prefixWord ++ tailWord_2921468).sum := by decide
  have hdescent : baseEnd_2921468 < baseStart_2921468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921495 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 5]
def baseStart_2921495 : Nat := 118140960795 + 2921495 * 2 ^ 59
def prefixEnd_2921495 : Nat := 4983230072969 + 3 ^ 40 * 2921495 * 2
def baseEnd_2921495 : Nat := 1500131164707152371076795

theorem tailTrace_2921495 : CollatzResearch.WordTrace tailWord_2921495 prefixEnd_2921495 1500131164707152371076795 := by
  unfold tailWord_2921495
  simp only [CollatzResearch.WordTrace]
  refine ⟨106555676550930041467541939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71037117700620027645027959 106555676550930041467541939)
  ·
    refine ⟨159833514826395062201312909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106555676550930041467541939 159833514826395062201312909)
    ·
      refine ⟨59937568059898148325492341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159833514826395062201312909 59937568059898148325492341)
      ·
        refine ⟨5619147005615451405514907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59937568059898148325492341 5619147005615451405514907)
        ·
          refine ⟨8428720508423177108272361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5619147005615451405514907 8428720508423177108272361)
          ·
            refine ⟨6321540381317382831204271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8428720508423177108272361 6321540381317382831204271)
            ·
              refine ⟨9482310571976074246806407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6321540381317382831204271 9482310571976074246806407)
              ·
                refine ⟨14223465857964111370209611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9482310571976074246806407 14223465857964111370209611)
                ·
                  refine ⟨21335198786946167055314417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14223465857964111370209611 21335198786946167055314417)
                  ·
                    refine ⟨16001399090209625291485813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21335198786946167055314417 16001399090209625291485813)
                    ·
                      refine ⟨1500131164707152371076795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16001399090209625291485813 1500131164707152371076795)
                      ·
                        rfl

theorem cell23_2921495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_2921495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921495 prefixEnd_2921495 := by exact prefixLift 2921495
  have htrace : WordTrace (prefixWord ++ tailWord_2921495) baseStart_2921495 baseEnd_2921495 := by
    simpa [prefixWord, tailWord_2921495, baseEnd_2921495] using wordTrace_append hprefix tailTrace_2921495
  have hstable : (prefixWord ++ tailWord_2921495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921495).length < 2 ^ (prefixWord ++ tailWord_2921495).sum := by decide
  have hdescent : baseEnd_2921495 < baseStart_2921495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921548 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 1, 2, 6]
def baseStart_2921548 : Nat := 118140960795 + 2921548 * 2 ^ 59
def prefixEnd_2921548 : Nat := 4983230072969 + 3 ^ 40 * 2921548 * 2
def baseEnd_2921548 : Nat := 1500158379181840663714051

theorem tailTrace_2921548 : CollatzResearch.WordTrace tailWord_2921548 prefixEnd_2921548 1500158379181840663714051 := by
  unfold tailWord_2921548
  simp only [CollatzResearch.WordTrace]
  refine ⟨53278804809869015759610649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71038406413158687679480865 53278804809869015759610649)
  ·
    refine ⟨39959103607401761819707987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53278804809869015759610649 39959103607401761819707987)
    ·
      refine ⟨59938655411102642729561981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39959103607401761819707987 59938655411102642729561981)
      ·
        refine ⟨22476995779163491023585743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59938655411102642729561981 22476995779163491023585743)
        ·
          refine ⟨33715493668745236535378615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22476995779163491023585743 33715493668745236535378615)
          ·
            refine ⟨50573240503117854803067923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33715493668745236535378615 50573240503117854803067923)
            ·
              refine ⟨75859860754676782204601885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50573240503117854803067923 75859860754676782204601885)
              ·
                refine ⟨28447447783003793326725707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75859860754676782204601885 28447447783003793326725707)
                ·
                  refine ⟨42671171674505689990088561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28447447783003793326725707 42671171674505689990088561)
                  ·
                    refine ⟨32003378755879267492566421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42671171674505689990088561 32003378755879267492566421)
                    ·
                      refine ⟨1500158379181840663714051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32003378755879267492566421 1500158379181840663714051)
                      ·
                        rfl

theorem cell23_2921548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_2921548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921548 prefixEnd_2921548 := by exact prefixLift 2921548
  have htrace : WordTrace (prefixWord ++ tailWord_2921548) baseStart_2921548 baseEnd_2921548 := by
    simpa [prefixWord, tailWord_2921548, baseEnd_2921548] using wordTrace_append hprefix tailTrace_2921548
  have hstable : (prefixWord ++ tailWord_2921548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921548).length < 2 ^ (prefixWord ++ tailWord_2921548).sum := by decide
  have hdescent : baseEnd_2921548 < baseStart_2921548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921566 : List Nat := [4, 4, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_2921566 : Nat := 118140960795 + 2921566 * 2 ^ 59
def prefixEnd_2921566 : Nat := 4983230072969 + 3 ^ 40 * 2921566 * 2
def baseEnd_2921566 : Nat := 500055873944540531096323

theorem tailTrace_2921566 : CollatzResearch.WordTrace tailWord_2921566 prefixEnd_2921566 500055873944540531096323 := by
  unfold tailWord_2921566
  simp only [CollatzResearch.WordTrace]
  refine ⟨13319783266709102574172069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71038844089115213728917701 13319783266709102574172069)
  ·
    refine ⟨2497459362507956732657263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13319783266709102574172069 2497459362507956732657263)
    ·
      refine ⟨3746189043761935098985895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2497459362507956732657263 3746189043761935098985895)
      ·
        refine ⟨5619283565642902648478843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3746189043761935098985895 5619283565642902648478843)
        ·
          refine ⟨8428925348464353972718265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5619283565642902648478843 8428925348464353972718265)
          ·
            refine ⟨6321694011348265479538699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8428925348464353972718265 6321694011348265479538699)
            ·
              refine ⟨9482541017022398219308049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6321694011348265479538699 9482541017022398219308049)
              ·
                refine ⟨7111905762766798664481037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9482541017022398219308049 7111905762766798664481037)
                ·
                  refine ⟨2666964661037549499180389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7111905762766798664481037 2666964661037549499180389)
                  ·
                    refine ⟨500055873944540531096323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2666964661037549499180389 500055873944540531096323)
                    ·
                      rfl

theorem cell23_2921566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_2921566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921566 prefixEnd_2921566 := by exact prefixLift 2921566
  have htrace : WordTrace (prefixWord ++ tailWord_2921566) baseStart_2921566 baseEnd_2921566 := by
    simpa [prefixWord, tailWord_2921566, baseEnd_2921566] using wordTrace_append hprefix tailTrace_2921566
  have hstable : (prefixWord ++ tailWord_2921566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921566).length < 2 ^ (prefixWord ++ tailWord_2921566).sum := by decide
  have hdescent : baseEnd_2921566 < baseStart_2921566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921568 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 7]
def baseStart_2921568 : Nat := 118140960795 + 2921568 * 2 ^ 59
def prefixEnd_2921568 : Nat := 4983230072969 + 3 ^ 40 * 2921568 * 2
def baseEnd_2921568 : Nat := 1500168648794930585463959

theorem tailTrace_2921568 : CollatzResearch.WordTrace tailWord_2921568 prefixEnd_2921568 1500168648794930585463959 := by
  unfold tailWord_2921568
  simp only [CollatzResearch.WordTrace]
  refine ⟨53279169539832787467474679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71038892719777049956632905 53279169539832787467474679)
  ·
    refine ⟨79918754309749181201212019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53279169539832787467474679 79918754309749181201212019)
    ·
      refine ⟨119878131464623771801818029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79918754309749181201212019 119878131464623771801818029)
      ·
        refine ⟨44954299299233914425681761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119878131464623771801818029 44954299299233914425681761)
        ·
          refine ⟨33715724474425435819261321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44954299299233914425681761 33715724474425435819261321)
          ·
            refine ⟨25286793355819076864445991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33715724474425435819261321 25286793355819076864445991)
            ·
              refine ⟨37930190033728615296668987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25286793355819076864445991 37930190033728615296668987)
              ·
                refine ⟨56895285050592922945003481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37930190033728615296668987 56895285050592922945003481)
                ·
                  refine ⟨42671463787944692208752611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56895285050592922945003481 42671463787944692208752611)
                  ·
                    refine ⟨64007195681917038313128917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42671463787944692208752611 64007195681917038313128917)
                    ·
                      refine ⟨1500168648794930585463959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64007195681917038313128917 1500168648794930585463959)
                      ·
                        rfl

theorem cell23_2921568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_2921568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921568 prefixEnd_2921568 := by exact prefixLift 2921568
  have htrace : WordTrace (prefixWord ++ tailWord_2921568) baseStart_2921568 baseEnd_2921568 := by
    simpa [prefixWord, tailWord_2921568, baseEnd_2921568] using wordTrace_append hprefix tailTrace_2921568
  have hstable : (prefixWord ++ tailWord_2921568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921568).length < 2 ^ (prefixWord ++ tailWord_2921568).sum := by decide
  have hdescent : baseEnd_2921568 < baseStart_2921568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921575 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 3, 5]
def baseStart_2921575 : Nat := 118140960795 + 2921575 * 2 ^ 59
def prefixEnd_2921575 : Nat := 4983230072969 + 3 ^ 40 * 2921575 * 2
def baseEnd_2921575 : Nat := 500057414386504019358809

theorem tailTrace_2921575 : CollatzResearch.WordTrace tailWord_2921575 prefixEnd_2921575 500057414386504019358809 := by
  unfold tailWord_2921575
  simp only [CollatzResearch.WordTrace]
  refine ⟨106558594390640215130454179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71039062927093476753636119 106558594390640215130454179)
  ·
    refine ⟨159837891585960322695681269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106558594390640215130454179 159837891585960322695681269)
    ·
      refine ⟨14984802336183780252720119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159837891585960322695681269 14984802336183780252720119)
      ·
        refine ⟨22477203504275670379080179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14984802336183780252720119 22477203504275670379080179)
        ·
          refine ⟨33715805256413505568620269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22477203504275670379080179 33715805256413505568620269)
          ·
            refine ⟨12643426971155064588232601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33715805256413505568620269 12643426971155064588232601)
            ·
              refine ⟨9482570228366298441174451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12643426971155064588232601 9482570228366298441174451)
              ·
                refine ⟨14223855342549447661761677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9482570228366298441174451 14223855342549447661761677)
                ·
                  refine ⟨5333945753456042873160629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14223855342549447661761677 5333945753456042873160629)
                  ·
                    refine ⟨500057414386504019358809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5333945753456042873160629 500057414386504019358809)
                    ·
                      rfl

theorem cell23_2921575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_2921575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921575 prefixEnd_2921575 := by exact prefixLift 2921575
  have htrace : WordTrace (prefixWord ++ tailWord_2921575) baseStart_2921575 baseEnd_2921575 := by
    simpa [prefixWord, tailWord_2921575, baseEnd_2921575] using wordTrace_append hprefix tailTrace_2921575
  have hstable : (prefixWord ++ tailWord_2921575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921575).length < 2 ^ (prefixWord ++ tailWord_2921575).sum := by decide
  have hdescent : baseEnd_2921575 < baseStart_2921575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921576 : List Nat := [2, 1, 4, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2921576 : Nat := 118140960795 + 2921576 * 2 ^ 59
def prefixEnd_2921576 : Nat := 4983230072969 + 3 ^ 40 * 2921576 * 2
def baseEnd_2921576 : Nat := 1500172756640166554163923

theorem tailTrace_2921576 : CollatzResearch.WordTrace tailWord_2921576 prefixEnd_2921576 1500172756640166554163923 := by
  unfold tailWord_2921576
  simp only [CollatzResearch.WordTrace]
  refine ⟨53279315431818296150620291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71039087242424394867493721 53279315431818296150620291)
  ·
    refine ⟨79918973147727444225930437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53279315431818296150620291 79918973147727444225930437)
    ·
      refine ⟨14984807465198895792361957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79918973147727444225930437 14984807465198895792361957)
      ·
        refine ⟨2809651399724792961067867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14984807465198895792361957 2809651399724792961067867)
        ·
          refine ⟨4214477099587189441601801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2809651399724792961067867 4214477099587189441601801)
          ·
            refine ⟨3160857824690392081201351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4214477099587189441601801 3160857824690392081201351)
            ·
              refine ⟨4741286737035588121802027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3160857824690392081201351 4741286737035588121802027)
              ·
                refine ⟨7111930105553382182703041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4741286737035588121802027 7111930105553382182703041)
                ·
                  refine ⟨5333947579165036637027281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7111930105553382182703041 5333947579165036637027281)
                  ·
                    refine ⟨4000460684373777477770461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5333947579165036637027281 4000460684373777477770461)
                    ·
                      refine ⟨1500172756640166554163923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4000460684373777477770461 1500172756640166554163923)
                      ·
                        rfl

theorem cell23_2921576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2921576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921576 prefixEnd_2921576 := by exact prefixLift 2921576
  have htrace : WordTrace (prefixWord ++ tailWord_2921576) baseStart_2921576 baseEnd_2921576 := by
    simpa [prefixWord, tailWord_2921576, baseEnd_2921576] using wordTrace_append hprefix tailTrace_2921576
  have hstable : (prefixWord ++ tailWord_2921576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921576).length < 2 ^ (prefixWord ++ tailWord_2921576).sum := by decide
  have hdescent : baseEnd_2921576 < baseStart_2921576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921592 : List Nat := [2, 1, 2, 1, 1, 1, 8, 1, 1, 5]
def baseStart_2921592 : Nat := 118140960795 + 2921592 * 2 ^ 59
def prefixEnd_2921592 : Nat := 4983230072969 + 3 ^ 40 * 2921592 * 2
def baseEnd_2921592 : Nat := 500060324110212830521283

theorem tailTrace_2921592 : CollatzResearch.WordTrace tailWord_2921592 prefixEnd_2921592 500060324110212830521283 := by
  unfold tailWord_2921592
  simp only [CollatzResearch.WordTrace]
  refine ⟨53279607215789313516911515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71039476287719084689215353 53279607215789313516911515)
  ·
    refine ⟨79919410823683970275367273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53279607215789313516911515 79919410823683970275367273)
    ·
      refine ⟨59939558117762977706525455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79919410823683970275367273 59939558117762977706525455)
      ·
        refine ⟨89909337176644466559788183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59939558117762977706525455 89909337176644466559788183)
        ·
          refine ⟨134864005764966699839682275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89909337176644466559788183 134864005764966699839682275)
          ·
            refine ⟨202296008647450049759523413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134864005764966699839682275 202296008647450049759523413)
            ·
              refine ⟨2370656351337305270619415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 202296008647450049759523413 2370656351337305270619415)
              ·
                refine ⟨3555984527005957905929123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2370656351337305270619415 3555984527005957905929123)
                ·
                  refine ⟨5333976790508936858893685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3555984527005957905929123 5333976790508936858893685)
                  ·
                    refine ⟨500060324110212830521283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5333976790508936858893685 500060324110212830521283)
                    ·
                      rfl

theorem cell23_2921592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 1, 5].length) (baseStart_2921592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921592 prefixEnd_2921592 := by exact prefixLift 2921592
  have htrace : WordTrace (prefixWord ++ tailWord_2921592) baseStart_2921592 baseEnd_2921592 := by
    simpa [prefixWord, tailWord_2921592, baseEnd_2921592] using wordTrace_append hprefix tailTrace_2921592
  have hstable : (prefixWord ++ tailWord_2921592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921592).length < 2 ^ (prefixWord ++ tailWord_2921592).sum := by decide
  have hdescent : baseEnd_2921592 < baseStart_2921592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921595 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 1, 8, 2]
def baseStart_2921595 : Nat := 118140960795 + 2921595 * 2 ^ 59
def prefixEnd_2921595 : Nat := 4983230072969 + 3 ^ 40 * 2921595 * 2
def baseEnd_2921595 : Nat := 1500182512772601979826335

theorem tailTrace_2921595 : CollatzResearch.WordTrace tailWord_2921595 prefixEnd_2921595 1500182512772601979826335 := by
  unfold tailWord_2921595
  simp only [CollatzResearch.WordTrace]
  refine ⟨106559323850567758546182239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71039549233711839030788159 106559323850567758546182239)
  ·
    refine ⟨159838985775851637819273359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106559323850567758546182239 159838985775851637819273359)
    ·
      refine ⟨239758478663777456728910039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159838985775851637819273359 239758478663777456728910039)
      ·
        refine ⟨359637717995666185093365059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239758478663777456728910039 359637717995666185093365059)
        ·
          refine ⟨539456576993499277640047589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359637717995666185093365059 539456576993499277640047589)
          ·
            refine ⟨101148108186281114557508923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 539456576993499277640047589 101148108186281114557508923)
            ·
              refine ⟨151722162279421671836263385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101148108186281114557508923 151722162279421671836263385)
              ·
                refine ⟨113791621709566253877197539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151722162279421671836263385 113791621709566253877197539)
                ·
                  refine ⟨170687432564349380815796309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113791621709566253877197539 170687432564349380815796309)
                  ·
                    refine ⟨2000243350363469306435113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 170687432564349380815796309 2000243350363469306435113)
                    ·
                      refine ⟨1500182512772601979826335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2000243350363469306435113 1500182512772601979826335)
                      ·
                        rfl

theorem cell23_2921595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 8, 2].length) (baseStart_2921595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921595 prefixEnd_2921595 := by exact prefixLift 2921595
  have htrace : WordTrace (prefixWord ++ tailWord_2921595) baseStart_2921595 baseEnd_2921595 := by
    simpa [prefixWord, tailWord_2921595, baseEnd_2921595] using wordTrace_append hprefix tailTrace_2921595
  have hstable : (prefixWord ++ tailWord_2921595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921595).length < 2 ^ (prefixWord ++ tailWord_2921595).sum := by decide
  have hdescent : baseEnd_2921595 < baseStart_2921595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921629 : List Nat := [1, 4, 2, 1, 1, 2, 1, 4, 3, 2, 2]
def baseStart_2921629 : Nat := 118140960795 + 2921629 * 2 ^ 59
def prefixEnd_2921629 : Nat := 4983230072969 + 3 ^ 40 * 2921629 * 2
def baseEnd_2921629 : Nat := 1500199971114854846801179

theorem tailTrace_2921629 : CollatzResearch.WordTrace tailWord_2921629 prefixEnd_2921629 1500199971114854846801179 := by
  unfold tailWord_2921629
  simp only [CollatzResearch.WordTrace]
  refine ⟨106560563932444582352919941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71040375954963054901946627 106560563932444582352919941)
  ·
    refine ⟨19980105737333359191172489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106560563932444582352919941 19980105737333359191172489)
    ·
      refine ⟨14985079303000019393379367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19980105737333359191172489 14985079303000019393379367)
      ·
        refine ⟨22477618954500029090069051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14985079303000019393379367 22477618954500029090069051)
        ·
          refine ⟨33716428431750043635103577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22477618954500029090069051 33716428431750043635103577)
          ·
            refine ⟨25287321323812532726327683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33716428431750043635103577 25287321323812532726327683)
            ·
              refine ⟨37930981985718799089491525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25287321323812532726327683 37930981985718799089491525)
              ·
                refine ⟨7112059122322274829279661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37930981985718799089491525 7112059122322274829279661)
                ·
                  refine ⟨2667022170870853060979873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7112059122322274829279661 2667022170870853060979873)
                  ·
                    refine ⟨2000266628153139795734905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2667022170870853060979873 2000266628153139795734905)
                    ·
                      refine ⟨1500199971114854846801179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2000266628153139795734905 1500199971114854846801179)
                      ·
                        rfl

theorem cell23_2921629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_2921629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921629 prefixEnd_2921629 := by exact prefixLift 2921629
  have htrace : WordTrace (prefixWord ++ tailWord_2921629) baseStart_2921629 baseEnd_2921629 := by
    simpa [prefixWord, tailWord_2921629, baseEnd_2921629] using wordTrace_append hprefix tailTrace_2921629
  have hstable : (prefixWord ++ tailWord_2921629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921629).length < 2 ^ (prefixWord ++ tailWord_2921629).sum := by decide
  have hdescent : baseEnd_2921629 < baseStart_2921629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921649 : List Nat := [1, 2, 2, 5, 1, 1, 2, 3, 1, 2, 3]
def baseStart_2921649 : Nat := 118140960795 + 2921649 * 2 ^ 59
def prefixEnd_2921649 : Nat := 4983230072969 + 3 ^ 40 * 2921649 * 2
def baseEnd_2921649 : Nat := 1500210240727944768551087

theorem tailTrace_2921649 : CollatzResearch.WordTrace tailWord_2921649 prefixEnd_2921649 1500210240727944768551087 := by
  unfold tailWord_2921649
  simp only [CollatzResearch.WordTrace]
  refine ⟨106561293392372125768648001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71040862261581417179098667 106561293392372125768648001)
  ·
    refine ⟨79920970044279094326486001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106561293392372125768648001 79920970044279094326486001)
    ·
      refine ⟨59940727533209320744864501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79920970044279094326486001 59940727533209320744864501)
      ·
        refine ⟨5619443206238373819831047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59940727533209320744864501 5619443206238373819831047)
        ·
          refine ⟨8429164809357560729746571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5619443206238373819831047 8429164809357560729746571)
          ·
            refine ⟨12643747214036341094619857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8429164809357560729746571 12643747214036341094619857)
            ·
              refine ⟨9482810410527255820964893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12643747214036341094619857 9482810410527255820964893)
              ·
                refine ⟨3556053903947720932861835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9482810410527255820964893 3556053903947720932861835)
                ·
                  refine ⟨5334080855921581399292753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3556053903947720932861835 5334080855921581399292753)
                  ·
                    refine ⟨4000560641941186049469565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5334080855921581399292753 4000560641941186049469565)
                    ·
                      refine ⟨1500210240727944768551087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4000560641941186049469565 1500210240727944768551087)
                      ·
                        rfl

theorem cell23_2921649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_2921649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921649 prefixEnd_2921649 := by exact prefixLift 2921649
  have htrace : WordTrace (prefixWord ++ tailWord_2921649) baseStart_2921649 baseEnd_2921649 := by
    simpa [prefixWord, tailWord_2921649, baseEnd_2921649] using wordTrace_append hprefix tailTrace_2921649
  have hstable : (prefixWord ++ tailWord_2921649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921649).length < 2 ^ (prefixWord ++ tailWord_2921649).sum := by decide
  have hdescent : baseEnd_2921649 < baseStart_2921649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921705 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 3, 6, 3]
def baseStart_2921705 : Nat := 118140960795 + 2921705 * 2 ^ 59
def prefixEnd_2921705 : Nat := 4983230072969 + 3 ^ 40 * 2921705 * 2
def baseEnd_2921705 : Nat := 1500238995644596549450829

theorem tailTrace_2921705 : CollatzResearch.WordTrace tailWord_2921705 prefixEnd_2921705 1500238995644596549450829 := by
  unfold tailWord_2921705
  simp only [CollatzResearch.WordTrace]
  refine ⟨106563335880169247332686569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71042223920112831555124379 106563335880169247332686569)
  ·
    refine ⟨79922501910126935499514927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106563335880169247332686569 79922501910126935499514927)
    ·
      refine ⟨119883752865190403249272391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79922501910126935499514927 119883752865190403249272391)
      ·
        refine ⟨179825629297785604873908587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119883752865190403249272391 179825629297785604873908587)
        ·
          refine ⟨269738443946678407310862881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179825629297785604873908587 269738443946678407310862881)
          ·
            refine ⟨202303832960008805483147161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269738443946678407310862881 202303832960008805483147161)
            ·
              refine ⟨151727874720006604112360371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202303832960008805483147161 151727874720006604112360371)
              ·
                refine ⟨227591812080009906168540557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151727874720006604112360371 227591812080009906168540557)
                ·
                  refine ⟨85346929530003714813202709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227591812080009906168540557 85346929530003714813202709)
                  ·
                    refine ⟨4000637321718924131868877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85346929530003714813202709 4000637321718924131868877)
                    ·
                      refine ⟨1500238995644596549450829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4000637321718924131868877 1500238995644596549450829)
                      ·
                        rfl

theorem cell23_2921705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 6, 3].length) (baseStart_2921705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921705 prefixEnd_2921705 := by exact prefixLift 2921705
  have htrace : WordTrace (prefixWord ++ tailWord_2921705) baseStart_2921705 baseEnd_2921705 := by
    simpa [prefixWord, tailWord_2921705, baseEnd_2921705] using wordTrace_append hprefix tailTrace_2921705
  have hstable : (prefixWord ++ tailWord_2921705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921705).length < 2 ^ (prefixWord ++ tailWord_2921705).sum := by decide
  have hdescent : baseEnd_2921705 < baseStart_2921705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921732 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_2921732 : Nat := 118140960795 + 2921732 * 2 ^ 59
def prefixEnd_2921732 : Nat := 4983230072969 + 3 ^ 40 * 2921732 * 2
def baseEnd_2921732 : Nat := 1500252859622267943813205

theorem tailTrace_2921732 : CollatzResearch.WordTrace tailWord_2921732 prefixEnd_2921732 1500252859622267943813205 := by
  unfold tailWord_2921732
  simp only [CollatzResearch.WordTrace]
  refine ⟨53282160325535715471959725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71042880434047620629279633 53282160325535715471959725)
  ·
    refine ⟨19980810122075893301984897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53282160325535715471959725 19980810122075893301984897)
    ·
      refine ⟨14985607591556919976488673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19980810122075893301984897 14985607591556919976488673)
      ·
        refine ⟨11239205693667689982366505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14985607591556919976488673 11239205693667689982366505)
        ·
          refine ⟨8429404270250767486774879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11239205693667689982366505 8429404270250767486774879)
          ·
            refine ⟨12644106405376151230162319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8429404270250767486774879 12644106405376151230162319)
            ·
              refine ⟨18966159608064226845243479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12644106405376151230162319 18966159608064226845243479)
              ·
                refine ⟨28449239412096340267865219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18966159608064226845243479 28449239412096340267865219)
                ·
                  refine ⟨42673859118144510401797829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28449239412096340267865219 42673859118144510401797829)
                  ·
                    refine ⟨8001348584652095700337093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42673859118144510401797829 8001348584652095700337093)
                    ·
                      refine ⟨1500252859622267943813205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8001348584652095700337093 1500252859622267943813205)
                      ·
                        rfl

theorem cell23_2921732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_2921732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921732 prefixEnd_2921732 := by exact prefixLift 2921732
  have htrace : WordTrace (prefixWord ++ tailWord_2921732) baseStart_2921732 baseEnd_2921732 := by
    simpa [prefixWord, tailWord_2921732, baseEnd_2921732] using wordTrace_append hprefix tailTrace_2921732
  have hstable : (prefixWord ++ tailWord_2921732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921732).length < 2 ^ (prefixWord ++ tailWord_2921732).sum := by decide
  have hdescent : baseEnd_2921732 < baseStart_2921732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921736 : List Nat := [2, 1, 3, 2, 4, 1, 2, 1, 1, 4, 2]
def baseStart_2921736 : Nat := 118140960795 + 2921736 * 2 ^ 59
def prefixEnd_2921736 : Nat := 4983230072969 + 3 ^ 40 * 2921736 * 2
def baseEnd_2921736 : Nat := 1500254913544885928163187

theorem tailTrace_2921736 : CollatzResearch.WordTrace tailWord_2921736 prefixEnd_2921736 1500254913544885928163187 := by
  unfold tailWord_2921736
  simp only [CollatzResearch.WordTrace]
  refine ⟨53282233271528469813532531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71042977695371293084710041 53282233271528469813532531)
  ·
    refine ⟨79923349907292704720298797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53282233271528469813532531 79923349907292704720298797)
    ·
      refine ⟨29971256215234764270112049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79923349907292704720298797 29971256215234764270112049)
      ·
        refine ⟨22478442161426073202584037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29971256215234764270112049 22478442161426073202584037)
        ·
          refine ⟨4214707905267388725484507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22478442161426073202584037 4214707905267388725484507)
          ·
            refine ⟨6322061857901083088226761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4214707905267388725484507 6322061857901083088226761)
            ·
              refine ⟨4741546393425812316170071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6322061857901083088226761 4741546393425812316170071)
              ·
                refine ⟨7112319590138718474255107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4741546393425812316170071 7112319590138718474255107)
                ·
                  refine ⟨10668479385208077711382661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7112319590138718474255107 10668479385208077711382661)
                  ·
                    refine ⟨2000339884726514570884249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10668479385208077711382661 2000339884726514570884249)
                    ·
                      refine ⟨1500254913544885928163187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2000339884726514570884249 1500254913544885928163187)
                      ·
                        rfl

theorem cell23_2921736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_2921736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921736 prefixEnd_2921736 := by exact prefixLift 2921736
  have htrace : WordTrace (prefixWord ++ tailWord_2921736) baseStart_2921736 baseEnd_2921736 := by
    simpa [prefixWord, tailWord_2921736, baseEnd_2921736] using wordTrace_append hprefix tailTrace_2921736
  have hstable : (prefixWord ++ tailWord_2921736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921736).length < 2 ^ (prefixWord ++ tailWord_2921736).sum := by decide
  have hdescent : baseEnd_2921736 < baseStart_2921736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921742 : List Nat := [4, 1, 1, 2, 1, 4, 1, 2, 7]
def baseStart_2921742 : Nat := 118140960795 + 2921742 * 2 ^ 59
def prefixEnd_2921742 : Nat := 4983230072969 + 3 ^ 40 * 2921742 * 2
def baseEnd_2921742 : Nat := 166695332714312544965351

theorem tailTrace_2921742 : CollatzResearch.WordTrace tailWord_2921742 prefixEnd_2921742 166695332714312544965351 := by
  unfold tailWord_2921742
  simp only [CollatzResearch.WordTrace]
  refine ⟨13320585672629400331472935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71043123587356801767855653 13320585672629400331472935)
  ·
    refine ⟨19980878508944100497209403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13320585672629400331472935 19980878508944100497209403)
    ·
      refine ⟨29971317763416150745814105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19980878508944100497209403 29971317763416150745814105)
      ·
        refine ⟨22478488322562113059360579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29971317763416150745814105 22478488322562113059360579)
        ·
          refine ⟨33717732483843169589040869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22478488322562113059360579 33717732483843169589040869)
          ·
            refine ⟨6322074840720594297945163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33717732483843169589040869 6322074840720594297945163)
            ·
              refine ⟨9483112261080891446917745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6322074840720594297945163 9483112261080891446917745)
              ·
                refine ⟨7112334195810668585188309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9483112261080891446917745 7112334195810668585188309)
                ·
                  refine ⟨166695332714312544965351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7112334195810668585188309 166695332714312544965351)
                  ·
                    rfl

theorem cell23_2921742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_2921742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921742 prefixEnd_2921742 := by exact prefixLift 2921742
  have htrace : WordTrace (prefixWord ++ tailWord_2921742) baseStart_2921742 baseEnd_2921742 := by
    simpa [prefixWord, tailWord_2921742, baseEnd_2921742] using wordTrace_append hprefix tailTrace_2921742
  have hstable : (prefixWord ++ tailWord_2921742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921742).length < 2 ^ (prefixWord ++ tailWord_2921742).sum := by decide
  have hdescent : baseEnd_2921742 < baseStart_2921742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921770 : List Nat := [3, 1, 4, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_2921770 : Nat := 118140960795 + 2921770 * 2 ^ 59
def prefixEnd_2921770 : Nat := 4983230072969 + 3 ^ 40 * 2921770 * 2
def baseEnd_2921770 : Nat := 1500272371887138795138031

theorem tailTrace_2921770 : CollatzResearch.WordTrace tailWord_2921770 prefixEnd_2921770 1500272371887138795138031 := by
  unfold tailWord_2921770
  simp only [CollatzResearch.WordTrace]
  refine ⟨26641426656233440858450691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71043804416622508955868509 26641426656233440858450691)
  ·
    refine ⟨39962139984350161287676037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26641426656233440858450691 39962139984350161287676037)
    ·
      refine ⟨7492901247065655241439257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39962139984350161287676037 7492901247065655241439257)
      ·
        refine ⟨5619675935299241431079443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7492901247065655241439257 5619675935299241431079443)
        ·
          refine ⟨8429513902948862146619165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5619675935299241431079443 8429513902948862146619165)
          ·
            refine ⟨3161067713605823304982187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8429513902948862146619165 3161067713605823304982187)
            ·
              refine ⟨4741601570408734957473281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3161067713605823304982187 4741601570408734957473281)
              ·
                refine ⟨3556201177806551218104961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4741601570408734957473281 3556201177806551218104961)
                ·
                  refine ⟨2667150883354913413578721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3556201177806551218104961 2667150883354913413578721)
                  ·
                    refine ⟨2000363162516185060184041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2667150883354913413578721 2000363162516185060184041)
                    ·
                      refine ⟨1500272371887138795138031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2000363162516185060184041 1500272371887138795138031)
                      ·
                        rfl

theorem cell23_2921770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_2921770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921770 prefixEnd_2921770 := by exact prefixLift 2921770
  have htrace : WordTrace (prefixWord ++ tailWord_2921770) baseStart_2921770 baseEnd_2921770 := by
    simpa [prefixWord, tailWord_2921770, baseEnd_2921770] using wordTrace_append hprefix tailTrace_2921770
  have hstable : (prefixWord ++ tailWord_2921770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921770).length < 2 ^ (prefixWord ++ tailWord_2921770).sum := by decide
  have hdescent : baseEnd_2921770 < baseStart_2921770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921829 : List Nat := [1, 3, 1, 3, 1, 2, 3, 2, 2, 2, 3]
def baseStart_2921829 : Nat := 118140960795 + 2921829 * 2 ^ 59
def prefixEnd_2921829 : Nat := 4983230072969 + 3 ^ 40 * 2921829 * 2
def baseEnd_2921829 : Nat := 1500302667245754064300259

theorem tailTrace_2921829 : CollatzResearch.WordTrace tailWord_2921829 prefixEnd_2921829 1500302667245754064300259 := by
  unfold tailWord_2921829
  simp only [CollatzResearch.WordTrace]
  refine ⟨106567858531720016510200541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71045239021146677673467027 106567858531720016510200541)
  ·
    refine ⟨39962946949395006191325203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106567858531720016510200541 39962946949395006191325203)
    ·
      refine ⟨59944420424092509286987805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39962946949395006191325203 59944420424092509286987805)
      ·
        refine ⟨22479157659034690982620427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59944420424092509286987805 22479157659034690982620427)
        ·
          refine ⟨33718736488552036473930641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22479157659034690982620427 33718736488552036473930641)
          ·
            refine ⟨25289052366414027355447981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33718736488552036473930641 25289052366414027355447981)
            ·
              refine ⟨9483394637405260258292993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25289052366414027355447981 9483394637405260258292993)
              ·
                refine ⟨7112545978053945193719745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9483394637405260258292993 7112545978053945193719745)
                ·
                  refine ⟨5334409483540458895289809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7112545978053945193719745 5334409483540458895289809)
                  ·
                    refine ⟨4000807112655344171467357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5334409483540458895289809 4000807112655344171467357)
                    ·
                      refine ⟨1500302667245754064300259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4000807112655344171467357 1500302667245754064300259)
                      ·
                        rfl

theorem cell23_2921829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_2921829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921829 prefixEnd_2921829 := by exact prefixLift 2921829
  have htrace : WordTrace (prefixWord ++ tailWord_2921829) baseStart_2921829 baseEnd_2921829 := by
    simpa [prefixWord, tailWord_2921829, baseEnd_2921829] using wordTrace_append hprefix tailTrace_2921829
  have hstable : (prefixWord ++ tailWord_2921829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921829).length < 2 ^ (prefixWord ++ tailWord_2921829).sum := by decide
  have hdescent : baseEnd_2921829 < baseStart_2921829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921836 : List Nat := [2, 2, 1, 1, 5, 3, 1, 1, 3, 4]
def baseStart_2921836 : Nat := 118140960795 + 2921836 * 2 ^ 59
def prefixEnd_2921836 : Nat := 4983230072969 + 3 ^ 40 * 2921836 * 2
def baseEnd_2921836 : Nat := 500102087203445178970909

theorem tailTrace_2921836 : CollatzResearch.WordTrace tailWord_2921836 prefixEnd_2921836 500102087203445178970909 := by
  unfold tailWord_2921836
  simp only [CollatzResearch.WordTrace]
  refine ⟨53284056921347328352852681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71045409228463104470470241 53284056921347328352852681)
  ·
    refine ⟨39963042691010496264639511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53284056921347328352852681 39963042691010496264639511)
    ·
      refine ⟨59944564036515744396959267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39963042691010496264639511 59944564036515744396959267)
      ·
        refine ⟨89916846054773616595438901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59944564036515744396959267 89916846054773616595438901)
        ·
          refine ⟨8429704317635026555822397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89916846054773616595438901 8429704317635026555822397)
          ·
            refine ⟨3161139119113134958433399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8429704317635026555822397 3161139119113134958433399)
            ·
              refine ⟨4741708678669702437650099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3161139119113134958433399 4741708678669702437650099)
              ·
                refine ⟨7112563018004553656475149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4741708678669702437650099 7112563018004553656475149)
                ·
                  refine ⟨2667211131751707621178181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7112563018004553656475149 2667211131751707621178181)
                  ·
                    refine ⟨500102087203445178970909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2667211131751707621178181 500102087203445178970909)
                    ·
                      rfl

theorem cell23_2921836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_2921836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921836 prefixEnd_2921836 := by exact prefixLift 2921836
  have htrace : WordTrace (prefixWord ++ tailWord_2921836) baseStart_2921836 baseEnd_2921836 := by
    simpa [prefixWord, tailWord_2921836, baseEnd_2921836] using wordTrace_append hprefix tailTrace_2921836
  have hstable : (prefixWord ++ tailWord_2921836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921836).length < 2 ^ (prefixWord ++ tailWord_2921836).sum := by decide
  have hdescent : baseEnd_2921836 < baseStart_2921836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921849 : List Nat := [1, 2, 1, 3, 2, 1, 6, 1, 6]
def baseStart_2921849 : Nat := 118140960795 + 2921849 * 2 ^ 59
def prefixEnd_2921849 : Nat := 4983230072969 + 3 ^ 40 * 2921849 * 2
def baseEnd_2921849 : Nat := 166701437428760442894463

theorem tailTrace_2921849 : CollatzResearch.WordTrace tailWord_2921849 prefixEnd_2921849 166701437428760442894463 := by
  unfold tailWord_2921849
  simp only [CollatzResearch.WordTrace]
  refine ⟨106568587991647559925928601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71045725327765039950619067 106568587991647559925928601)
  ·
    refine ⟨79926440993735669944446451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106568587991647559925928601 79926440993735669944446451)
    ·
      refine ⟨119889661490603504916669677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79926440993735669944446451 119889661490603504916669677)
      ·
        refine ⟨44958623058976314343751129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119889661490603504916669677 44958623058976314343751129)
        ·
          refine ⟨33718967294232235757813347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44958623058976314343751129 33718967294232235757813347)
          ·
            refine ⟨50578450941348353636720021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33718967294232235757813347 50578450941348353636720021)
            ·
              refine ⟨2370864887875704076721251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50578450941348353636720021 2370864887875704076721251)
              ·
                refine ⟨3556297331813556115081877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2370864887875704076721251 3556297331813556115081877)
                ·
                  refine ⟨166701437428760442894463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3556297331813556115081877 166701437428760442894463)
                  ·
                    rfl

theorem cell23_2921849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 6].length) (baseStart_2921849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921849 prefixEnd_2921849 := by exact prefixLift 2921849
  have htrace : WordTrace (prefixWord ++ tailWord_2921849) baseStart_2921849 baseEnd_2921849 := by
    simpa [prefixWord, tailWord_2921849, baseEnd_2921849] using wordTrace_append hprefix tailTrace_2921849
  have hstable : (prefixWord ++ tailWord_2921849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921849).length < 2 ^ (prefixWord ++ tailWord_2921849).sum := by decide
  have hdescent : baseEnd_2921849 < baseStart_2921849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921892 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 5, 6]
def baseStart_2921892 : Nat := 118140960795 + 2921892 * 2 ^ 59
def prefixEnd_2921892 : Nat := 4983230072969 + 3 ^ 40 * 2921892 * 2
def baseEnd_2921892 : Nat := 500111672175662439270823

theorem tailTrace_2921892 : CollatzResearch.WordTrace tailWord_2921892 prefixEnd_2921892 500111672175662439270823 := by
  unfold tailWord_2921892
  simp only [CollatzResearch.WordTrace]
  refine ⟨53285078165245889134871965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71046770886994518846495953 53285078165245889134871965)
  ·
    refine ⟨19981904311967208425576987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53285078165245889134871965 19981904311967208425576987)
    ·
      refine ⟨29972856467950812638365481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19981904311967208425576987 29972856467950812638365481)
      ·
        refine ⟨22479642350963109478774111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29972856467950812638365481 22479642350963109478774111)
        ·
          refine ⟨33719463526444664218161167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22479642350963109478774111 33719463526444664218161167)
          ·
            refine ⟨50579195289666996327241751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33719463526444664218161167 50579195289666996327241751)
            ·
              refine ⟨75868792934500494490862627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50579195289666996327241751 75868792934500494490862627)
              ·
                refine ⟨113803189401750741736293941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75868792934500494490862627 113803189401750741736293941)
                ·
                  refine ⟨10669049006414132037777557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113803189401750741736293941 10669049006414132037777557)
                  ·
                    refine ⟨500111672175662439270823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10669049006414132037777557 500111672175662439270823)
                    ·
                      rfl

theorem cell23_2921892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_2921892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921892 prefixEnd_2921892 := by exact prefixLift 2921892
  have htrace : WordTrace (prefixWord ++ tailWord_2921892) baseStart_2921892 baseEnd_2921892 := by
    simpa [prefixWord, tailWord_2921892, baseEnd_2921892] using wordTrace_append hprefix tailTrace_2921892
  have hstable : (prefixWord ++ tailWord_2921892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921892).length < 2 ^ (prefixWord ++ tailWord_2921892).sum := by decide
  have hdescent : baseEnd_2921892 < baseStart_2921892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921909 : List Nat := [1, 3, 3, 2, 2, 1, 1, 3, 1, 6]
def baseStart_2921909 : Nat := 118140960795 + 2921909 * 2 ^ 59
def prefixEnd_2921909 : Nat := 4983230072969 + 3 ^ 40 * 2921909 * 2
def baseEnd_2921909 : Nat := 500114581899371250433297

theorem tailTrace_2921909 : CollatzResearch.WordTrace tailWord_2921909 prefixEnd_2921909 500114581899371250433297 := by
  unfold tailWord_2921909
  simp only [CollatzResearch.WordTrace]
  refine ⟨106570776371430190173112781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71047184247620126782075187 106570776371430190173112781)
  ·
    refine ⟨39964041139286321314917293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106570776371430190173112781 39964041139286321314917293)
    ·
      refine ⟨14986515427232370493093985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39964041139286321314917293 14986515427232370493093985)
      ·
        refine ⟨11239886570424277869820489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14986515427232370493093985 11239886570424277869820489)
        ·
          refine ⟨8429914927818208402365367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11239886570424277869820489 8429914927818208402365367)
          ·
            refine ⟨12644872391727312603548051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8429914927818208402365367 12644872391727312603548051)
            ·
              refine ⟨18967308587590968905322077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12644872391727312603548051 18967308587590968905322077)
              ·
                refine ⟨7112740720346613339495779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18967308587590968905322077 7112740720346613339495779)
                ·
                  refine ⟨10669111080519920009243669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7112740720346613339495779 10669111080519920009243669)
                  ·
                    refine ⟨500114581899371250433297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10669111080519920009243669 500114581899371250433297)
                    ·
                      rfl

theorem cell23_2921909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_2921909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921909 prefixEnd_2921909 := by exact prefixLift 2921909
  have htrace : WordTrace (prefixWord ++ tailWord_2921909) baseStart_2921909 baseEnd_2921909 := by
    simpa [prefixWord, tailWord_2921909, baseEnd_2921909] using wordTrace_append hprefix tailTrace_2921909
  have hstable : (prefixWord ++ tailWord_2921909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921909).length < 2 ^ (prefixWord ++ tailWord_2921909).sum := by decide
  have hdescent : baseEnd_2921909 < baseStart_2921909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921912 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 1, 1, 6]
def baseStart_2921912 : Nat := 118140960795 + 2921912 * 2 ^ 59
def prefixEnd_2921912 : Nat := 4983230072969 + 3 ^ 40 * 2921912 * 2
def baseEnd_2921912 : Nat := 1500345286140077239562377

theorem tailTrace_2921912 : CollatzResearch.WordTrace tailWord_2921912 prefixEnd_2921912 1500345286140077239562377 := by
  unfold tailWord_2921912
  simp only [CollatzResearch.WordTrace]
  refine ⟨53285442895209660842735995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71047257193612881123647993 53285442895209660842735995)
  ·
    refine ⟨79928164342814491264103993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53285442895209660842735995 79928164342814491264103993)
    ·
      refine ⟨59946123257110868448077995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79928164342814491264103993 59946123257110868448077995)
      ·
        refine ⟨89919184885666302672116993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59946123257110868448077995 89919184885666302672116993)
        ·
          refine ⟨67439388664249727004087745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89919184885666302672116993 67439388664249727004087745)
          ·
            refine ⟨50579541498187295253065809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67439388664249727004087745 50579541498187295253065809)
            ·
              refine ⟨37934656123640471439799357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50579541498187295253065809 37934656123640471439799357)
              ·
                refine ⟨14225496046365176789924759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37934656123640471439799357 14225496046365176789924759)
                ·
                  refine ⟨21338244069547765184887139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14225496046365176789924759 21338244069547765184887139)
                  ·
                    refine ⟨32007366104321647777330709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21338244069547765184887139 32007366104321647777330709)
                    ·
                      refine ⟨1500345286140077239562377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32007366104321647777330709 1500345286140077239562377)
                      ·
                        rfl

theorem cell23_2921912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_2921912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921912 prefixEnd_2921912 := by exact prefixLift 2921912
  have htrace : WordTrace (prefixWord ++ tailWord_2921912) baseStart_2921912 baseEnd_2921912 := by
    simpa [prefixWord, tailWord_2921912, baseEnd_2921912] using wordTrace_append hprefix tailTrace_2921912
  have hstable : (prefixWord ++ tailWord_2921912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921912).length < 2 ^ (prefixWord ++ tailWord_2921912).sum := by decide
  have hdescent : baseEnd_2921912 < baseStart_2921912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921952 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 2, 7]
def baseStart_2921952 : Nat := 118140960795 + 2921952 * 2 ^ 59
def prefixEnd_2921952 : Nat := 4983230072969 + 3 ^ 40 * 2921952 * 2
def baseEnd_2921952 : Nat := 500121941788752361020731

theorem tailTrace_2921952 : CollatzResearch.WordTrace tailWord_2921952 prefixEnd_2921952 500121941788752361020731 := by
  unfold tailWord_2921952
  simp only [CollatzResearch.WordTrace]
  refine ⟨53286172355137204258464055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71048229806849605677952073 53286172355137204258464055)
  ·
    refine ⟨79929258532705806387696083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53286172355137204258464055 79929258532705806387696083)
    ·
      refine ⟨119893887799058709581544125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79929258532705806387696083 119893887799058709581544125)
      ·
        refine ⟨44960207924647016093079047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119893887799058709581544125 44960207924647016093079047)
        ·
          refine ⟨67440311886970524139618571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44960207924647016093079047 67440311886970524139618571)
          ·
            refine ⟨101160467830455786209427857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67440311886970524139618571 101160467830455786209427857)
            ·
              refine ⟨75870350872841839657070893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101160467830455786209427857 75870350872841839657070893)
              ·
                refine ⟨28451381577315689871401585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75870350872841839657070893 28451381577315689871401585)
                ·
                  refine ⟨21338536182986767403551189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28451381577315689871401585 21338536182986767403551189)
                  ·
                    refine ⟨500121941788752361020731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21338536182986767403551189 500121941788752361020731)
                    ·
                      rfl

theorem cell23_2921952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2, 7].length) (baseStart_2921952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921952 prefixEnd_2921952 := by exact prefixLift 2921952
  have htrace : WordTrace (prefixWord ++ tailWord_2921952) baseStart_2921952 baseEnd_2921952 := by
    simpa [prefixWord, tailWord_2921952, baseEnd_2921952] using wordTrace_append hprefix tailTrace_2921952
  have hstable : (prefixWord ++ tailWord_2921952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921952).length < 2 ^ (prefixWord ++ tailWord_2921952).sum := by decide
  have hdescent : baseEnd_2921952 < baseStart_2921952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921973 : List Nat := [1, 3, 5, 1, 1, 3, 2, 7]
def baseStart_2921973 : Nat := 118140960795 + 2921973 * 2 ^ 59
def prefixEnd_2921973 : Nat := 4983230072969 + 3 ^ 40 * 2921973 * 2
def baseEnd_2921973 : Nat := 55569504017037092625911

theorem tailTrace_2921973 : CollatzResearch.WordTrace tailWord_2921973 prefixEnd_2921973 55569504017037092625911 := by
  unfold tailWord_2921973
  simp only [CollatzResearch.WordTrace]
  refine ⟨106573110643198329103442573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71048740428798886068961715 106573110643198329103442573)
  ·
    refine ⟨39964916491199373413790965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106573110643198329103442573 39964916491199373413790965)
    ·
      refine ⟨3746710921049941257542903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39964916491199373413790965 3746710921049941257542903)
      ·
        refine ⟨5620066381574911886314355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3746710921049941257542903 5620066381574911886314355)
        ·
          refine ⟨8430099572362367829471533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5620066381574911886314355 8430099572362367829471533)
          ·
            refine ⟨3161287339635887936051825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8430099572362367829471533 3161287339635887936051825)
            ·
              refine ⟨2370965504726915952038869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3161287339635887936051825 2370965504726915952038869)
              ·
                refine ⟨55569504017037092625911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2370965504726915952038869 55569504017037092625911)
                ·
                  rfl

theorem cell23_2921973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 7].length) (baseStart_2921973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921973 prefixEnd_2921973 := by exact prefixLift 2921973
  have htrace : WordTrace (prefixWord ++ tailWord_2921973) baseStart_2921973 baseEnd_2921973 := by
    simpa [prefixWord, tailWord_2921973, baseEnd_2921973] using wordTrace_append hprefix tailTrace_2921973
  have hstable : (prefixWord ++ tailWord_2921973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921973).length < 2 ^ (prefixWord ++ tailWord_2921973).sum := by decide
  have hdescent : baseEnd_2921973 < baseStart_2921973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2921990 : List Nat := [6, 2, 1, 1, 2, 2, 9]
def baseStart_2921990 : Nat := 118140960795 + 2921990 * 2 ^ 59
def prefixEnd_2921990 : Nat := 4983230072969 + 3 ^ 40 * 2921990 * 2
def baseEnd_2921990 : Nat := 18523275773223801659099

theorem tailTrace_2921990 : CollatzResearch.WordTrace tailWord_2921990 prefixEnd_2921990 18523275773223801659099 := by
  unfold tailWord_2921990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3330429083879273156462857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71049153789424494004540949 3330429083879273156462857)
  ·
    refine ⟨2497821812909454867347143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3330429083879273156462857 2497821812909454867347143)
    ·
      refine ⟨3746732719364182301020715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2497821812909454867347143 3746732719364182301020715)
      ·
        refine ⟨5620099079046273451531073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3746732719364182301020715 5620099079046273451531073)
        ·
          refine ⟨4215074309284705088648305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5620099079046273451531073 4215074309284705088648305)
          ·
            refine ⟨3161305731963528816486229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4215074309284705088648305 3161305731963528816486229)
            ·
              refine ⟨18523275773223801659099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3161305731963528816486229 18523275773223801659099)
              ·
                rfl

theorem cell23_2921990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 9].length) (baseStart_2921990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2921990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2921990 prefixEnd_2921990 := by exact prefixLift 2921990
  have htrace : WordTrace (prefixWord ++ tailWord_2921990) baseStart_2921990 baseEnd_2921990 := by
    simpa [prefixWord, tailWord_2921990, baseEnd_2921990] using wordTrace_append hprefix tailTrace_2921990
  have hstable : (prefixWord ++ tailWord_2921990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2921990).length < 2 ^ (prefixWord ++ tailWord_2921990).sum := by decide
  have hdescent : baseEnd_2921990 < baseStart_2921990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2921990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922096 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 4]
def baseStart_2922096 : Nat := 118140960795 + 2922096 * 2 ^ 59
def prefixEnd_2922096 : Nat := 4983230072969 + 3 ^ 40 * 2922096 * 2
def baseEnd_2922096 : Nat := 1500439766580504519661531

theorem tailTrace_2922096 : CollatzResearch.WordTrace tailWord_2922096 prefixEnd_2922096 1500439766580504519661531 := by
  unfold tailWord_2922096
  simp only [CollatzResearch.WordTrace]
  refine ⟨53288798410876360555085071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71051731214501814073446761 53288798410876360555085071)
  ·
    refine ⟨79933197616314540832627607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53288798410876360555085071 79933197616314540832627607)
    ·
      refine ⟨119899796424471811248941411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79933197616314540832627607 119899796424471811248941411)
      ·
        refine ⟨179849694636707716873412117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119899796424471811248941411 179849694636707716873412117)
        ·
          refine ⟨8430454436095674228441193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 179849694636707716873412117 8430454436095674228441193)
          ·
            refine ⟨6322840827071755671330895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8430454436095674228441193 6322840827071755671330895)
            ·
              refine ⟨9484261240607633506996343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6322840827071755671330895 9484261240607633506996343)
              ·
                refine ⟨14226391860911450260494515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9484261240607633506996343 14226391860911450260494515)
                ·
                  refine ⟨21339587791367175390741773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14226391860911450260494515 21339587791367175390741773)
                  ·
                    refine ⟨8002345421762690771528165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21339587791367175390741773 8002345421762690771528165)
                    ·
                      refine ⟨1500439766580504519661531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8002345421762690771528165 1500439766580504519661531)
                      ·
                        rfl

theorem cell23_2922096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 4].length) (baseStart_2922096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922096 prefixEnd_2922096 := by exact prefixLift 2922096
  have htrace : WordTrace (prefixWord ++ tailWord_2922096) baseStart_2922096 baseEnd_2922096 := by
    simpa [prefixWord, tailWord_2922096, baseEnd_2922096] using wordTrace_append hprefix tailTrace_2922096
  have hstable : (prefixWord ++ tailWord_2922096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922096).length < 2 ^ (prefixWord ++ tailWord_2922096).sum := by decide
  have hdescent : baseEnd_2922096 < baseStart_2922096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922113 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 2, 4, 2]
def baseStart_2922113 : Nat := 118140960795 + 2922113 * 2 ^ 59
def prefixEnd_2922113 : Nat := 4983230072969 + 3 ^ 40 * 2922113 * 2
def baseEnd_2922113 : Nat := 1500448495751630953148953

theorem tailTrace_2922113 : CollatzResearch.WordTrace tailWord_2922113 prefixEnd_2922113 1500448495751630953148953 := by
  unfold tailWord_2922113
  simp only [CollatzResearch.WordTrace]
  refine ⟨106578216862691133013538993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71052144575127422009025995 106578216862691133013538993)
  ·
    refine ⟨79933662647018349760154245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106578216862691133013538993 79933662647018349760154245)
    ·
      refine ⟨14987561746315940580028921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79933662647018349760154245 14987561746315940580028921)
      ·
        refine ⟨11240671309736955435021691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14987561746315940580028921 11240671309736955435021691)
        ·
          refine ⟨16861006964605433152532537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11240671309736955435021691 16861006964605433152532537)
          ·
            refine ⟨12645755223454074864399403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16861006964605433152532537 12645755223454074864399403)
            ·
              refine ⟨18968632835181112296599105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12645755223454074864399403 18968632835181112296599105)
              ·
                refine ⟨14226474626385834222449329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18968632835181112296599105 14226474626385834222449329)
                ·
                  refine ⟨10669855969789375666836997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14226474626385834222449329 10669855969789375666836997)
                  ·
                    refine ⟨2000597994335507937531937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10669855969789375666836997 2000597994335507937531937)
                    ·
                      refine ⟨1500448495751630953148953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2000597994335507937531937 1500448495751630953148953)
                      ·
                        rfl

theorem cell23_2922113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_2922113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922113 prefixEnd_2922113 := by exact prefixLift 2922113
  have htrace : WordTrace (prefixWord ++ tailWord_2922113) baseStart_2922113 baseEnd_2922113 := by
    simpa [prefixWord, tailWord_2922113, baseEnd_2922113] using wordTrace_append hprefix tailTrace_2922113
  have hstable : (prefixWord ++ tailWord_2922113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922113).length < 2 ^ (prefixWord ++ tailWord_2922113).sum := by decide
  have hdescent : baseEnd_2922113 < baseStart_2922113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922123 : List Nat := [1, 1, 1, 1, 4, 1, 3, 6, 1, 4]
def baseStart_2922123 : Nat := 118140960795 + 2922123 * 2 ^ 59
def prefixEnd_2922123 : Nat := 4983230072969 + 3 ^ 40 * 2922123 * 2
def baseEnd_2922123 : Nat := 500151210186058638007969

theorem tailTrace_2922123 : CollatzResearch.WordTrace tailWord_2922123 prefixEnd_2922123 500151210186058638007969 := by
  unfold tailWord_2922123
  simp only [CollatzResearch.WordTrace]
  refine ⟨106578581592654904721403023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71052387728436603147602015 106578581592654904721403023)
  ·
    refine ⟨159867872388982357082104535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106578581592654904721403023 159867872388982357082104535)
    ·
      refine ⟨239801808583473535623156803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159867872388982357082104535 239801808583473535623156803)
      ·
        refine ⟨359702712875210303434735205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239801808583473535623156803 359702712875210303434735205)
        ·
          refine ⟨67444258664101931894012851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 359702712875210303434735205 67444258664101931894012851)
          ·
            refine ⟨101166387996152897841019277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67444258664101931894012851 101166387996152897841019277)
            ·
              refine ⟨37937395498557336690382229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101166387996152897841019277 37937395498557336690382229)
              ·
                refine ⟨1778315413994875157361667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37937395498557336690382229 1778315413994875157361667)
                ·
                  refine ⟨2667473120992312736042501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1778315413994875157361667 2667473120992312736042501)
                  ·
                    refine ⟨500151210186058638007969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2667473120992312736042501 500151210186058638007969)
                    ·
                      rfl

theorem cell23_2922123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 1, 4].length) (baseStart_2922123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922123 prefixEnd_2922123 := by exact prefixLift 2922123
  have htrace : WordTrace (prefixWord ++ tailWord_2922123) baseStart_2922123 baseEnd_2922123 := by
    simpa [prefixWord, tailWord_2922123, baseEnd_2922123] using wordTrace_append hprefix tailTrace_2922123
  have hstable : (prefixWord ++ tailWord_2922123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922123).length < 2 ^ (prefixWord ++ tailWord_2922123).sum := by decide
  have hdescent : baseEnd_2922123 < baseStart_2922123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922230 : List Nat := [5, 1, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_2922230 : Nat := 118140960795 + 2922230 * 2 ^ 59
def prefixEnd_2922230 : Nat := 4983230072969 + 3 ^ 40 * 2922230 * 2
def baseEnd_2922230 : Nat := 500169524329402331795305

theorem tailTrace_2922230 : CollatzResearch.WordTrace tailWord_2922230 prefixEnd_2922230 500169524329402331795305 := by
  unfold tailWord_2922230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6661405262704203874721759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71054989468844841330365429 6661405262704203874721759)
  ·
    refine ⟨9992107894056305812082639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6661405262704203874721759 9992107894056305812082639)
    ·
      refine ⟨14988161841084458718123959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9992107894056305812082639 14988161841084458718123959)
      ·
        refine ⟨22482242761626688077185939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14988161841084458718123959 22482242761626688077185939)
        ·
          refine ⟨33723364142440032115778909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22482242761626688077185939 33723364142440032115778909)
          ·
            refine ⟨12646261553415012043417091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33723364142440032115778909 12646261553415012043417091)
            ·
              refine ⟨18969392330122518065125637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12646261553415012043417091 18969392330122518065125637)
              ·
                refine ⟨3556761061897972137211057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18969392330122518065125637 3556761061897972137211057)
                ·
                  refine ⟨2667570796423479102908293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3556761061897972137211057 2667570796423479102908293)
                  ·
                    refine ⟨500169524329402331795305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2667570796423479102908293 500169524329402331795305)
                    ·
                      rfl

theorem cell23_2922230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_2922230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922230 prefixEnd_2922230 := by exact prefixLift 2922230
  have htrace : WordTrace (prefixWord ++ tailWord_2922230) baseStart_2922230 baseEnd_2922230 := by
    simpa [prefixWord, tailWord_2922230, baseEnd_2922230] using wordTrace_append hprefix tailTrace_2922230
  have hstable : (prefixWord ++ tailWord_2922230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922230).length < 2 ^ (prefixWord ++ tailWord_2922230).sum := by decide
  have hdescent : baseEnd_2922230 < baseStart_2922230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922350 : List Nat := [4, 1, 2, 3, 1, 1, 3, 1, 7]
def baseStart_2922350 : Nat := 118140960795 + 2922350 * 2 ^ 59
def prefixEnd_2922350 : Nat := 4983230072969 + 3 ^ 40 * 2922350 * 2
def baseEnd_2922350 : Nat := 166730021185194058431707

theorem tailTrace_2922350 : CollatzResearch.WordTrace tailWord_2922350 prefixEnd_2922350 166730021185194058431707 := by
  unfold tailWord_2922350
  simp only [CollatzResearch.WordTrace]
  refine ⟨13323357620354065311239563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71057907308555014993277669 13323357620354065311239563)
  ·
    refine ⟨19985036430531097966859345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13323357620354065311239563 19985036430531097966859345)
    ·
      refine ⟨14988777322898323475144509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19985036430531097966859345 14988777322898323475144509)
      ·
        refine ⟨5620791496086871303179191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14988777322898323475144509 5620791496086871303179191)
        ·
          refine ⟨8431187244130306954768787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5620791496086871303179191 8431187244130306954768787)
          ·
            refine ⟨12646780866195460432153181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8431187244130306954768787 12646780866195460432153181)
            ·
              refine ⟨4742542824823297662057443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12646780866195460432153181 4742542824823297662057443)
              ·
                refine ⟨7113814237234946493086165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4742542824823297662057443 7113814237234946493086165)
                ·
                  refine ⟨166730021185194058431707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7113814237234946493086165 166730021185194058431707)
                  ·
                    rfl

theorem cell23_2922350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_2922350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922350 prefixEnd_2922350 := by exact prefixLift 2922350
  have htrace : WordTrace (prefixWord ++ tailWord_2922350) baseStart_2922350 baseEnd_2922350 := by
    simpa [prefixWord, tailWord_2922350, baseEnd_2922350] using wordTrace_append hprefix tailTrace_2922350
  have hstable : (prefixWord ++ tailWord_2922350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922350).length < 2 ^ (prefixWord ++ tailWord_2922350).sum := by decide
  have hdescent : baseEnd_2922350 < baseStart_2922350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922400 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 2, 4, 2]
def baseStart_2922400 : Nat := 118140960795 + 2922400 * 2 ^ 59
def prefixEnd_2922400 : Nat := 4983230072969 + 3 ^ 40 * 2922400 * 2
def baseEnd_2922400 : Nat := 1500595864699471330260133

theorem tailTrace_2922400 : CollatzResearch.WordTrace tailWord_2922400 prefixEnd_2922400 1500595864699471330260133 := by
  unfold tailWord_2922400
  simp only [CollatzResearch.WordTrace]
  refine ⟨53294342306325690514618327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71059123075100920686157769 53294342306325690514618327)
  ·
    refine ⟨79941513459488535771927491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53294342306325690514618327 79941513459488535771927491)
    ·
      refine ⟨119912270189232803657891237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79941513459488535771927491 119912270189232803657891237)
      ·
        refine ⟨22483550660481150685854607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119912270189232803657891237 22483550660481150685854607)
        ·
          refine ⟨33725325990721726028781911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22483550660481150685854607 33725325990721726028781911)
          ·
            refine ⟨50587988986082589043172867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33725325990721726028781911 50587988986082589043172867)
            ·
              refine ⟨75881983479123883564759301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50587988986082589043172867 75881983479123883564759301)
              ·
                refine ⟨14227871902335728168392369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75881983479123883564759301 14227871902335728168392369)
                ·
                  refine ⟨10670903926751796126294277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14227871902335728168392369 10670903926751796126294277)
                  ·
                    refine ⟨2000794486265961773680177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10670903926751796126294277 2000794486265961773680177)
                    ·
                      refine ⟨1500595864699471330260133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2000794486265961773680177 1500595864699471330260133)
                      ·
                        rfl

theorem cell23_2922400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_2922400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922400 prefixEnd_2922400 := by exact prefixLift 2922400
  have htrace : WordTrace (prefixWord ++ tailWord_2922400) baseStart_2922400 baseEnd_2922400 := by
    simpa [prefixWord, tailWord_2922400, baseEnd_2922400] using wordTrace_append hprefix tailTrace_2922400
  have hstable : (prefixWord ++ tailWord_2922400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922400).length < 2 ^ (prefixWord ++ tailWord_2922400).sum := by decide
  have hdescent : baseEnd_2922400 < baseStart_2922400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922401 : List Nat := [1, 2, 3, 4, 3, 1, 2, 2, 5]
def baseStart_2922401 : Nat := 118140960795 + 2922401 * 2 ^ 59
def prefixEnd_2922401 : Nat := 4983230072969 + 3 ^ 40 * 2922401 * 2
def baseEnd_2922401 : Nat := 166732930908902869594181

theorem tailTrace_2922401 : CollatzResearch.WordTrace tailWord_2922401 prefixEnd_2922401 166732930908902869594181 := by
  unfold tailWord_2922401
  simp only [CollatzResearch.WordTrace]
  refine ⟨106588721085647758200023057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71059147390431838800015371 106588721085647758200023057)
  ·
    refine ⟨79941540814235818650017293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106588721085647758200023057 79941540814235818650017293)
    ·
      refine ⟨29978077805338431993756485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79941540814235818650017293 29978077805338431993756485)
      ·
        refine ⟨5620889588500955998829341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29978077805338431993756485 5620889588500955998829341)
        ·
          refine ⟨2107833595687858499561003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5620889588500955998829341 2107833595687858499561003)
          ·
            refine ⟨3161750393531787749341505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2107833595687858499561003 3161750393531787749341505)
            ·
              refine ⟨2371312795148840812006129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3161750393531787749341505 2371312795148840812006129)
              ·
                refine ⟨1778484596361630609004597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2371312795148840812006129 1778484596361630609004597)
                ·
                  refine ⟨166732930908902869594181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1778484596361630609004597 166732930908902869594181)
                  ·
                    rfl

theorem cell23_2922401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 5].length) (baseStart_2922401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922401 prefixEnd_2922401 := by exact prefixLift 2922401
  have htrace : WordTrace (prefixWord ++ tailWord_2922401) baseStart_2922401 baseEnd_2922401 := by
    simpa [prefixWord, tailWord_2922401, baseEnd_2922401] using wordTrace_append hprefix tailTrace_2922401
  have hstable : (prefixWord ++ tailWord_2922401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922401).length < 2 ^ (prefixWord ++ tailWord_2922401).sum := by decide
  have hdescent : baseEnd_2922401 < baseStart_2922401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922403 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 3]
def baseStart_2922403 : Nat := 118140960795 + 2922403 * 2 ^ 59
def prefixEnd_2922403 : Nat := 4983230072969 + 3 ^ 40 * 2922403 * 2
def baseEnd_2922403 : Nat := 1500597405141434818522619

theorem tailTrace_2922403 : CollatzResearch.WordTrace tailWord_2922403 prefixEnd_2922403 1500597405141434818522619 := by
  unfold tailWord_2922403
  simp only [CollatzResearch.WordTrace]
  refine ⟨106588794031640512541595863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71059196021093675027730575 106588794031640512541595863)
  ·
    refine ⟨159883191047460768812393795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106588794031640512541595863 159883191047460768812393795)
    ·
      refine ⟨239824786571191153218590693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159883191047460768812393795 239824786571191153218590693)
      ·
        refine ⟨44967147482098341228485755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239824786571191153218590693 44967147482098341228485755)
        ·
          refine ⟨67450721223147511842728633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44967147482098341228485755 67450721223147511842728633)
          ·
            refine ⟨50588040917360633882046475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67450721223147511842728633 50588040917360633882046475)
            ·
              refine ⟨75882061376040950823069713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50588040917360633882046475 75882061376040950823069713)
              ·
                refine ⟨56911546032030713117302285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75882061376040950823069713 56911546032030713117302285)
                ·
                  refine ⟨21341829762011517418988357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56911546032030713117302285 21341829762011517418988357)
                  ·
                    refine ⟨4001593080377159516060317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21341829762011517418988357 4001593080377159516060317)
                    ·
                      refine ⟨1500597405141434818522619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4001593080377159516060317 1500597405141434818522619)
                      ·
                        rfl

theorem cell23_2922403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_2922403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922403 prefixEnd_2922403 := by exact prefixLift 2922403
  have htrace : WordTrace (prefixWord ++ tailWord_2922403) baseStart_2922403 baseEnd_2922403 := by
    simpa [prefixWord, tailWord_2922403, baseEnd_2922403] using wordTrace_append hprefix tailTrace_2922403
  have hstable : (prefixWord ++ tailWord_2922403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922403).length < 2 ^ (prefixWord ++ tailWord_2922403).sum := by decide
  have hdescent : baseEnd_2922403 < baseStart_2922403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922417 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 2, 4, 2]
def baseStart_2922417 : Nat := 118140960795 + 2922417 * 2 ^ 59
def prefixEnd_2922417 : Nat := 4983230072969 + 3 ^ 40 * 2922417 * 2
def baseEnd_2922417 : Nat := 1500604593870597763747555

theorem tailTrace_2922417 : CollatzResearch.WordTrace tailWord_2922417 prefixEnd_2922417 1500604593870597763747555 := by
  unfold tailWord_2922417
  simp only [CollatzResearch.WordTrace]
  refine ⟨106589304653589792932605505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71059536435726528621737003 106589304653589792932605505)
  ·
    refine ⟨79941978490192344699454129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106589304653589792932605505 79941978490192344699454129)
    ·
      refine ⟨59956483867644258524590597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79941978490192344699454129 59956483867644258524590597)
      ·
        refine ⟨11241840725183298473360737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59956483867644258524590597 11241840725183298473360737)
        ·
          refine ⟨8431380543887473855020553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11241840725183298473360737 8431380543887473855020553)
          ·
            refine ⟨6323535407915605391265415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8431380543887473855020553 6323535407915605391265415)
            ·
              refine ⟨9485303111873408086898123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6323535407915605391265415 9485303111873408086898123)
              ·
                refine ⟨14227954667810112130347185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9485303111873408086898123 14227954667810112130347185)
                ·
                  refine ⟨10670966000857584097760389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14227954667810112130347185 10670966000857584097760389)
                  ·
                    refine ⟨2000806125160797018330073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10670966000857584097760389 2000806125160797018330073)
                    ·
                      refine ⟨1500604593870597763747555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2000806125160797018330073 1500604593870597763747555)
                      ·
                        rfl

theorem cell23_2922417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_2922417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922417 prefixEnd_2922417 := by exact prefixLift 2922417
  have htrace : WordTrace (prefixWord ++ tailWord_2922417) baseStart_2922417 baseEnd_2922417 := by
    simpa [prefixWord, tailWord_2922417, baseEnd_2922417] using wordTrace_append hprefix tailTrace_2922417
  have hstable : (prefixWord ++ tailWord_2922417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922417).length < 2 ^ (prefixWord ++ tailWord_2922417).sum := by decide
  have hdescent : baseEnd_2922417 < baseStart_2922417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922444 : List Nat := [2, 2, 1, 4, 1, 3, 2, 3, 1, 4]
def baseStart_2922444 : Nat := 118140960795 + 2922444 * 2 ^ 59
def prefixEnd_2922444 : Nat := 4983230072969 + 3 ^ 40 * 2922444 * 2
def baseEnd_2922444 : Nat := 500206152616089719369977

theorem tailTrace_2922444 : CollatzResearch.WordTrace tailWord_2922444 prefixEnd_2922444 500206152616089719369977 := by
  unfold tailWord_2922444
  simp only [CollatzResearch.WordTrace]
  refine ⟨53295144712245988271919193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71060192949661317695892257 53295144712245988271919193)
  ·
    refine ⟨39971358534184491203939395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53295144712245988271919193 39971358534184491203939395)
    ·
      refine ⟨59957037801276736805909093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39971358534184491203939395 59957037801276736805909093)
      ·
        refine ⟨11241944587739388151107955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59957037801276736805909093 11241944587739388151107955)
        ·
          refine ⟨16862916881609082226661933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11241944587739388151107955 16862916881609082226661933)
          ·
            refine ⟨6323593830603405834998225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16862916881609082226661933 6323593830603405834998225)
            ·
              refine ⟨4742695372952554376248669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6323593830603405834998225 4742695372952554376248669)
              ·
                refine ⟨1778510764857207891093251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4742695372952554376248669 1778510764857207891093251)
                ·
                  refine ⟨2667766147285811836639877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1778510764857207891093251 2667766147285811836639877)
                  ·
                    refine ⟨500206152616089719369977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2667766147285811836639877 500206152616089719369977)
                    ·
                      rfl

theorem cell23_2922444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 1, 4].length) (baseStart_2922444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922444 prefixEnd_2922444 := by exact prefixLift 2922444
  have htrace : WordTrace (prefixWord ++ tailWord_2922444) baseStart_2922444 baseEnd_2922444 := by
    simpa [prefixWord, tailWord_2922444, baseEnd_2922444] using wordTrace_append hprefix tailTrace_2922444
  have hstable : (prefixWord ++ tailWord_2922444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922444).length < 2 ^ (prefixWord ++ tailWord_2922444).sum := by decide
  have hdescent : baseEnd_2922444 < baseStart_2922444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922457 : List Nat := [1, 2, 1, 2, 6, 2, 1, 2, 6]
def baseStart_2922457 : Nat := 118140960795 + 2922457 * 2 ^ 59
def prefixEnd_2922457 : Nat := 4983230072969 + 3 ^ 40 * 2922457 * 2
def baseEnd_2922457 : Nat := 166736125899641956360819

theorem tailTrace_2922457 : CollatzResearch.WordTrace tailWord_2922457 prefixEnd_2922457 166736125899641956360819 := by
  unfold tailWord_2922457
  simp only [CollatzResearch.WordTrace]
  refine ⟨106590763573444879764061625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71060509048963253176041083 106590763573444879764061625)
  ·
    refine ⟨79943072680083659823046219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106590763573444879764061625 79943072680083659823046219)
    ·
      refine ⟨119914609020125489734569329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79943072680083659823046219 119914609020125489734569329)
      ·
        refine ⟨89935956765094117300926997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119914609020125489734569329 89935956765094117300926997)
        ·
          refine ⟨4215747973363786748480953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89935956765094117300926997 4215747973363786748480953)
          ·
            refine ⟨3161810980022840061360715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4215747973363786748480953 3161810980022840061360715)
            ·
              refine ⟨4742716470034260092041073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3161810980022840061360715 4742716470034260092041073)
              ·
                refine ⟨3557037352525695069030805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4742716470034260092041073 3557037352525695069030805)
                ·
                  refine ⟨166736125899641956360819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3557037352525695069030805 166736125899641956360819)
                  ·
                    rfl

theorem cell23_2922457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 6].length) (baseStart_2922457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922457 prefixEnd_2922457 := by exact prefixLift 2922457
  have htrace : WordTrace (prefixWord ++ tailWord_2922457) baseStart_2922457 baseEnd_2922457 := by
    simpa [prefixWord, tailWord_2922457, baseEnd_2922457] using wordTrace_append hprefix tailTrace_2922457
  have hstable : (prefixWord ++ tailWord_2922457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922457).length < 2 ^ (prefixWord ++ tailWord_2922457).sum := by decide
  have hdescent : baseEnd_2922457 < baseStart_2922457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922467 : List Nat := [1, 1, 1, 6, 1, 2, 1, 3, 3, 1, 3]
def baseStart_2922467 : Nat := 118140960795 + 2922467 * 2 ^ 59
def prefixEnd_2922467 : Nat := 4983230072969 + 3 ^ 40 * 2922467 * 2
def baseEnd_2922467 : Nat := 1500630267903322568122325

theorem tailTrace_2922467 : CollatzResearch.WordTrace tailWord_2922467 prefixEnd_2922467 1500630267903322568122325 := by
  unfold tailWord_2922467
  simp only [CollatzResearch.WordTrace]
  refine ⟨106591128303408651471925655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71060752202272434314617103 106591128303408651471925655)
  ·
    refine ⟨159886692455112977207888483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106591128303408651471925655 159886692455112977207888483)
    ·
      refine ⟨239830038682669465811832725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159886692455112977207888483 239830038682669465811832725)
      ·
        refine ⟨11242033063250131209929659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 239830038682669465811832725 11242033063250131209929659)
        ·
          refine ⟨16863049594875196814894489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11242033063250131209929659 16863049594875196814894489)
          ·
            refine ⟨12647287196156397611170867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16863049594875196814894489 12647287196156397611170867)
            ·
              refine ⟨18970930794234596416756301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12647287196156397611170867 18970930794234596416756301)
              ·
                refine ⟨7114099047837973656283613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18970930794234596416756301 7114099047837973656283613)
                ·
                  refine ⟨2667787142939240121106355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7114099047837973656283613 2667787142939240121106355)
                  ·
                    refine ⟨4001680714408860181659533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2667787142939240121106355 4001680714408860181659533)
                    ·
                      refine ⟨1500630267903322568122325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4001680714408860181659533 1500630267903322568122325)
                      ·
                        rfl

theorem cell23_2922467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_2922467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922467 prefixEnd_2922467 := by exact prefixLift 2922467
  have htrace : WordTrace (prefixWord ++ tailWord_2922467) baseStart_2922467 baseEnd_2922467 := by
    simpa [prefixWord, tailWord_2922467, baseEnd_2922467] using wordTrace_append hprefix tailTrace_2922467
  have hstable : (prefixWord ++ tailWord_2922467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922467).length < 2 ^ (prefixWord ++ tailWord_2922467).sum := by decide
  have hdescent : baseEnd_2922467 < baseStart_2922467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922494 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_2922494 : Nat := 118140960795 + 2922494 * 2 ^ 59
def prefixEnd_2922494 : Nat := 4983230072969 + 3 ^ 40 * 2922494 * 2
def baseEnd_2922494 : Nat := 1500644131880993962484701

theorem tailTrace_2922494 : CollatzResearch.WordTrace tailWord_2922494 prefixEnd_2922494 1500644131880993962484701 := by
  unfold tailWord_2922494
  simp only [CollatzResearch.WordTrace]
  refine ⟨13324014134288854385394817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71061408716207223388772357 13324014134288854385394817)
  ·
    refine ⟨9993010600716640789046113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13324014134288854385394817 9993010600716640789046113)
    ·
      refine ⟨7494757950537480591784585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9993010600716640789046113 7494757950537480591784585)
      ·
        refine ⟨5621068462903110443838439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7494757950537480591784585 5621068462903110443838439)
        ·
          refine ⟨8431602694354665665757659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5621068462903110443838439 8431602694354665665757659)
          ·
            refine ⟨12647404041531998498636489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8431602694354665665757659 12647404041531998498636489)
            ·
              refine ⟨9485553031148998873977367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12647404041531998498636489 9485553031148998873977367)
              ·
                refine ⟨14228329546723498310966051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9485553031148998873977367 14228329546723498310966051)
                ·
                  refine ⟨21342494320085247466449077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14228329546723498310966051 21342494320085247466449077)
                  ·
                    refine ⟨2000858842507991949979601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21342494320085247466449077 2000858842507991949979601)
                    ·
                      refine ⟨1500644131880993962484701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2000858842507991949979601 1500644131880993962484701)
                      ·
                        rfl

theorem cell23_2922494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_2922494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922494 prefixEnd_2922494 := by exact prefixLift 2922494
  have htrace : WordTrace (prefixWord ++ tailWord_2922494) baseStart_2922494 baseEnd_2922494 := by
    simpa [prefixWord, tailWord_2922494, baseEnd_2922494] using wordTrace_append hprefix tailTrace_2922494
  have hstable : (prefixWord ++ tailWord_2922494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922494).length < 2 ^ (prefixWord ++ tailWord_2922494).sum := by decide
  have hdescent : baseEnd_2922494 < baseStart_2922494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922501 : List Nat := [1, 3, 1, 1, 2, 6, 1, 3, 1, 1, 3]
def baseStart_2922501 : Nat := 118140960795 + 2922501 * 2 ^ 59
def prefixEnd_2922501 : Nat := 4983230072969 + 3 ^ 40 * 2922501 * 2
def baseEnd_2922501 : Nat := 1500647726245575435097169

theorem tailTrace_2922501 : CollatzResearch.WordTrace tailWord_2922501 prefixEnd_2922501 1500647726245575435097169 := by
  unfold tailWord_2922501
  simp only [CollatzResearch.WordTrace]
  refine ⟨106592368385285475278663357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71061578923523650185775571 106592368385285475278663357)
  ·
    refine ⟨39972138144482053229498759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106592368385285475278663357 39972138144482053229498759)
    ·
      refine ⟨59958207216723079844248139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39972138144482053229498759 59958207216723079844248139)
      ·
        refine ⟨89937310825084619766372209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59958207216723079844248139 89937310825084619766372209)
        ·
          refine ⟨67452983118813464824779157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89937310825084619766372209 67452983118813464824779157)
          ·
            refine ⟨3161858583694381163661523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67452983118813464824779157 3161858583694381163661523)
            ·
              refine ⟨4742787875541571745492285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3161858583694381163661523 4742787875541571745492285)
              ·
                refine ⟨1778545453328089404559607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4742787875541571745492285 1778545453328089404559607)
                ·
                  refine ⟨2667818179992134106839411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1778545453328089404559607 2667818179992134106839411)
                  ·
                    refine ⟨4001727269988201160259117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2667818179992134106839411 4001727269988201160259117)
                    ·
                      refine ⟨1500647726245575435097169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4001727269988201160259117 1500647726245575435097169)
                      ·
                        rfl

theorem cell23_2922501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 1, 1, 3].length) (baseStart_2922501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922501 prefixEnd_2922501 := by exact prefixLift 2922501
  have htrace : WordTrace (prefixWord ++ tailWord_2922501) baseStart_2922501 baseEnd_2922501 := by
    simpa [prefixWord, tailWord_2922501, baseEnd_2922501] using wordTrace_append hprefix tailTrace_2922501
  have hstable : (prefixWord ++ tailWord_2922501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922501).length < 2 ^ (prefixWord ++ tailWord_2922501).sum := by decide
  have hdescent : baseEnd_2922501 < baseStart_2922501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922530 : List Nat := [3, 3, 1, 1, 1, 2, 4, 8]
def baseStart_2922530 : Nat := 118140960795 + 2922530 * 2 ^ 59
def prefixEnd_2922530 : Nat := 4983230072969 + 3 ^ 40 * 2922530 * 2
def baseEnd_2922530 : Nat := 55580096932761326727205

theorem tailTrace_2922530 : CollatzResearch.WordTrace tailWord_2922530 prefixEnd_2922530 55580096932761326727205 := by
  unfold tailWord_2922530
  simp only [CollatzResearch.WordTrace]
  refine ⟨26648356525545103307867261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71062284068120275487646029 26648356525545103307867261)
  ·
    refine ⟨9993133697079413740450223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26648356525545103307867261 9993133697079413740450223)
    ·
      refine ⟨14989700545619120610675335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9993133697079413740450223 14989700545619120610675335)
      ·
        refine ⟨22484550818428680916013003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14989700545619120610675335 22484550818428680916013003)
        ·
          refine ⟨33726826227643021374019505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22484550818428680916013003 33726826227643021374019505)
          ·
            refine ⟨25295119670732266030514629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33726826227643021374019505 25295119670732266030514629)
            ·
              refine ⟨4742834938262299880721493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25295119670732266030514629 4742834938262299880721493)
              ·
                refine ⟨55580096932761326727205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4742834938262299880721493 55580096932761326727205)
                ·
                  rfl

theorem cell23_2922530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 8].length) (baseStart_2922530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922530 prefixEnd_2922530 := by exact prefixLift 2922530
  have htrace : WordTrace (prefixWord ++ tailWord_2922530) baseStart_2922530 baseEnd_2922530 := by
    simpa [prefixWord, tailWord_2922530, baseEnd_2922530] using wordTrace_append hprefix tailTrace_2922530
  have hstable : (prefixWord ++ tailWord_2922530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922530).length < 2 ^ (prefixWord ++ tailWord_2922530).sum := by decide
  have hdescent : baseEnd_2922530 < baseStart_2922530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922543 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 4, 7]
def baseStart_2922543 : Nat := 118140960795 + 2922543 * 2 ^ 59
def prefixEnd_2922543 : Nat := 4983230072969 + 3 ^ 40 * 2922543 * 2
def baseEnd_2922543 : Nat := 500223097477688090257325

theorem tailTrace_2922543 : CollatzResearch.WordTrace tailWord_2922543 prefixEnd_2922543 500223097477688090257325 := by
  unfold tailWord_2922543
  simp only [CollatzResearch.WordTrace]
  refine ⟨106593900251133316451692283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71062600167422210967794855 106593900251133316451692283)
  ·
    refine ⟨159890850376699974677538425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106593900251133316451692283 159890850376699974677538425)
    ·
      refine ⟨119918137782524981008153819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159890850376699974677538425 119918137782524981008153819)
      ·
        refine ⟨179877206673787471512230729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119918137782524981008153819 179877206673787471512230729)
        ·
          refine ⟨134907905005340603634173047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179877206673787471512230729 134907905005340603634173047)
          ·
            refine ⟨202361857508010905451259571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134907905005340603634173047 202361857508010905451259571)
            ·
              refine ⟨303542786262016358176889357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202361857508010905451259571 303542786262016358176889357)
              ·
                refine ⟨113828544848256134316333509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 303542786262016358176889357 113828544848256134316333509)
                ·
                  refine ⟨21342852159048025184312533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113828544848256134316333509 21342852159048025184312533)
                  ·
                    refine ⟨500223097477688090257325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21342852159048025184312533 500223097477688090257325)
                    ·
                      rfl

theorem cell23_2922543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 7].length) (baseStart_2922543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922543 prefixEnd_2922543 := by exact prefixLift 2922543
  have htrace : WordTrace (prefixWord ++ tailWord_2922543) baseStart_2922543 baseEnd_2922543 := by
    simpa [prefixWord, tailWord_2922543, baseEnd_2922543] using wordTrace_append hprefix tailTrace_2922543
  have hstable : (prefixWord ++ tailWord_2922543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922543).length < 2 ^ (prefixWord ++ tailWord_2922543).sum := by decide
  have hdescent : baseEnd_2922543 < baseStart_2922543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922544 : List Nat := [2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 3]
def baseStart_2922544 : Nat := 118140960795 + 2922544 * 2 ^ 59
def prefixEnd_2922544 : Nat := 4983230072969 + 3 ^ 40 * 2922544 * 2
def baseEnd_2922544 : Nat := 1500669805913718766859471

theorem tailTrace_2922544 : CollatzResearch.WordTrace tailWord_2922544 prefixEnd_2922544 1500669805913718766859471 := by
  unfold tailWord_2922544
  simp only [CollatzResearch.WordTrace]
  refine ⟨53296968362064846811239343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71062624482753129081652457 53296968362064846811239343)
  ·
    refine ⟨79945452543097270216859015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53296968362064846811239343 79945452543097270216859015)
    ·
      refine ⟨119918178814645905325288523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79945452543097270216859015 119918178814645905325288523)
      ·
        refine ⟨179877268221968857987932785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119918178814645905325288523 179877268221968857987932785)
        ·
          refine ⟨134907951166476643490949589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179877268221968857987932785 134907951166476643490949589)
          ·
            refine ⟨3161905105464296331819131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 134907951166476643490949589 3161905105464296331819131)
            ·
              refine ⟨4742857658196444497728697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3161905105464296331819131 4742857658196444497728697)
              ·
                refine ⟨3557143243647333373296523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4742857658196444497728697 3557143243647333373296523)
                ·
                  refine ⟨5335714865471000059944785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3557143243647333373296523 5335714865471000059944785)
                  ·
                    refine ⟨4001786149103250044958589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5335714865471000059944785 4001786149103250044958589)
                    ·
                      refine ⟨1500669805913718766859471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4001786149103250044958589 1500669805913718766859471)
                      ·
                        rfl

theorem cell23_2922544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 3].length) (baseStart_2922544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922544 prefixEnd_2922544 := by exact prefixLift 2922544
  have htrace : WordTrace (prefixWord ++ tailWord_2922544) baseStart_2922544 baseEnd_2922544 := by
    simpa [prefixWord, tailWord_2922544, baseEnd_2922544] using wordTrace_append hprefix tailTrace_2922544
  have hstable : (prefixWord ++ tailWord_2922544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922544).length < 2 ^ (prefixWord ++ tailWord_2922544).sum := by decide
  have hdescent : baseEnd_2922544 < baseStart_2922544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922557 : List Nat := [1, 4, 1, 3, 1, 1, 3, 2, 1, 3, 3]
def baseStart_2922557 : Nat := 118140960795 + 2922557 * 2 ^ 59
def prefixEnd_2922557 : Nat := 4983230072969 + 3 ^ 40 * 2922557 * 2
def baseEnd_2922557 : Nat := 1500676481162227215996911

theorem tailTrace_2922557 : CollatzResearch.WordTrace tailWord_2922557 prefixEnd_2922557 1500676481162227215996911 := by
  unfold tailWord_2922557
  simp only [CollatzResearch.WordTrace]
  refine ⟨106594410873082596842701925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71062940582055064561801283 106594410873082596842701925)
  ·
    refine ⟨19986452038702986908006611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106594410873082596842701925 19986452038702986908006611)
    ·
      refine ⟨29979678058054480362009917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19986452038702986908006611 29979678058054480362009917)
      ·
        refine ⟨11242379271770430135753719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29979678058054480362009917 11242379271770430135753719)
        ·
          refine ⟨16863568907655645203630579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11242379271770430135753719 16863568907655645203630579)
          ·
            refine ⟨25295353361483467805445869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16863568907655645203630579 25295353361483467805445869)
            ·
              refine ⟨9485757510556300427042201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25295353361483467805445869 9485757510556300427042201)
              ·
                refine ⟨7114318132917225320281651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9485757510556300427042201 7114318132917225320281651)
                ·
                  refine ⟨10671477199375837980422477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7114318132917225320281651 10671477199375837980422477)
                  ·
                    refine ⟨4001803949765939242658429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10671477199375837980422477 4001803949765939242658429)
                    ·
                      refine ⟨1500676481162227215996911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4001803949765939242658429 1500676481162227215996911)
                      ·
                        rfl

theorem cell23_2922557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_2922557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922557 prefixEnd_2922557 := by exact prefixLift 2922557
  have htrace : WordTrace (prefixWord ++ tailWord_2922557) baseStart_2922557 baseEnd_2922557 := by
    simpa [prefixWord, tailWord_2922557, baseEnd_2922557] using wordTrace_append hprefix tailTrace_2922557
  have hstable : (prefixWord ++ tailWord_2922557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922557).length < 2 ^ (prefixWord ++ tailWord_2922557).sum := by decide
  have hdescent : baseEnd_2922557 < baseStart_2922557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922561 : List Nat := [1, 2, 5, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_2922561 : Nat := 118140960795 + 2922561 * 2 ^ 59
def prefixEnd_2922561 : Nat := 4983230072969 + 3 ^ 40 * 2922561 * 2
def baseEnd_2922561 : Nat := 1500678535084845200346893

theorem tailTrace_2922561 : CollatzResearch.WordTrace tailWord_2922561 prefixEnd_2922561 1500678535084845200346893 := by
  unfold tailWord_2922561
  simp only [CollatzResearch.WordTrace]
  refine ⟨106594556765068105525847537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71063037843378737017231691 106594556765068105525847537)
  ·
    refine ⟨79945917573801079144385653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106594556765068105525847537 79945917573801079144385653)
    ·
      refine ⟨7494929772543851169786155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79945917573801079144385653 7494929772543851169786155)
      ·
        refine ⟨11242394658815776754679233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7494929772543851169786155 11242394658815776754679233)
        ·
          refine ⟨8431795994111832566009425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11242394658815776754679233 8431795994111832566009425)
          ·
            refine ⟨6323846995583874424507069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8431795994111832566009425 6323846995583874424507069)
            ·
              refine ⟨2371442623343952909190151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6323846995583874424507069 2371442623343952909190151)
              ·
                refine ⟨3557163935015929363785227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2371442623343952909190151 3557163935015929363785227)
                ·
                  refine ⟨5335745902523894045677841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3557163935015929363785227 5335745902523894045677841)
                  ·
                    refine ⟨4001809426892920534258381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5335745902523894045677841 4001809426892920534258381)
                    ·
                      refine ⟨1500678535084845200346893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4001809426892920534258381 1500678535084845200346893)
                      ·
                        rfl

theorem cell23_2922561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_2922561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922561 prefixEnd_2922561 := by exact prefixLift 2922561
  have htrace : WordTrace (prefixWord ++ tailWord_2922561) baseStart_2922561 baseEnd_2922561 := by
    simpa [prefixWord, tailWord_2922561, baseEnd_2922561] using wordTrace_append hprefix tailTrace_2922561
  have hstable : (prefixWord ++ tailWord_2922561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922561).length < 2 ^ (prefixWord ++ tailWord_2922561).sum := by decide
  have hdescent : baseEnd_2922561 < baseStart_2922561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922574 : List Nat := [4, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3]
def baseStart_2922574 : Nat := 118140960795 + 2922574 * 2 ^ 59
def prefixEnd_2922574 : Nat := 4983230072969 + 3 ^ 40 * 2922574 * 2
def baseEnd_2922574 : Nat := 1500685210333353649484333

theorem tailTrace_2922574 : CollatzResearch.WordTrace tailWord_2922574 prefixEnd_2922574 1500685210333353649484333 := by
  unfold tailWord_2922574
  simp only [CollatzResearch.WordTrace]
  refine ⟨13324378864252626093258847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71063353942680672497380517 13324378864252626093258847)
  ·
    refine ⟨19986568296378939139888271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13324378864252626093258847 19986568296378939139888271)
    ·
      refine ⟨29979852444568408709832407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19986568296378939139888271 29979852444568408709832407)
      ·
        refine ⟨44969778666852613064748611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29979852444568408709832407 44969778666852613064748611)
        ·
          refine ⟨67454668000278919597122917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44969778666852613064748611 67454668000278919597122917)
          ·
            refine ⟨12647750250052297424460547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67454668000278919597122917 12647750250052297424460547)
            ·
              refine ⟨18971625375078446136690821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12647750250052297424460547 18971625375078446136690821)
              ·
                refine ⟨3557179757827208650629529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18971625375078446136690821 3557179757827208650629529)
                ·
                  refine ⟨2667884818370406487972147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3557179757827208650629529 2667884818370406487972147)
                  ·
                    refine ⟨4001827227555609731958221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2667884818370406487972147 4001827227555609731958221)
                    ·
                      refine ⟨1500685210333353649484333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4001827227555609731958221 1500685210333353649484333)
                      ·
                        rfl

theorem cell23_2922574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_2922574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922574 prefixEnd_2922574 := by exact prefixLift 2922574
  have htrace : WordTrace (prefixWord ++ tailWord_2922574) baseStart_2922574 baseEnd_2922574 := by
    simpa [prefixWord, tailWord_2922574, baseEnd_2922574] using wordTrace_append hprefix tailTrace_2922574
  have hstable : (prefixWord ++ tailWord_2922574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922574).length < 2 ^ (prefixWord ++ tailWord_2922574).sum := by decide
  have hdescent : baseEnd_2922574 < baseStart_2922574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922631 : List Nat := [1, 1, 4, 2, 1, 1, 5, 2, 2, 2, 2]
def baseStart_2922631 : Nat := 118140960795 + 2922631 * 2 ^ 59
def prefixEnd_2922631 : Nat := 4983230072969 + 3 ^ 40 * 2922631 * 2
def baseEnd_2922631 : Nat := 1500714478730659926471571

theorem tailTrace_2922631 : CollatzResearch.WordTrace tailWord_2922631 prefixEnd_2922631 1500714478730659926471571 := by
  unfold tailWord_2922631
  simp only [CollatzResearch.WordTrace]
  refine ⟨106597109874814507480895747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71064739916543004987263831 106597109874814507480895747)
  ·
    refine ⟨159895664812221761221343621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106597109874814507480895747 159895664812221761221343621)
    ·
      refine ⟨29980437152291580229001929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159895664812221761221343621 29980437152291580229001929)
      ·
        refine ⟨22485327864218685171751447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29980437152291580229001929 22485327864218685171751447)
        ·
          refine ⟨33727991796328027757627171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22485327864218685171751447 33727991796328027757627171)
          ·
            refine ⟨50591987694492041636440757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33727991796328027757627171 50591987694492041636440757)
            ·
              refine ⟨4742998846358628903416321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50591987694492041636440757 4742998846358628903416321)
              ·
                refine ⟨3557249134768971677562241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4742998846358628903416321 3557249134768971677562241)
                ·
                  refine ⟨2667936851076728758171681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3557249134768971677562241 2667936851076728758171681)
                  ·
                    refine ⟨2000952638307546568628761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2667936851076728758171681 2000952638307546568628761)
                    ·
                      refine ⟨1500714478730659926471571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2000952638307546568628761 1500714478730659926471571)
                      ·
                        rfl

theorem cell23_2922631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_2922631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922631 prefixEnd_2922631 := by exact prefixLift 2922631
  have htrace : WordTrace (prefixWord ++ tailWord_2922631) baseStart_2922631 baseEnd_2922631 := by
    simpa [prefixWord, tailWord_2922631, baseEnd_2922631] using wordTrace_append hprefix tailTrace_2922631
  have hstable : (prefixWord ++ tailWord_2922631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922631).length < 2 ^ (prefixWord ++ tailWord_2922631).sum := by decide
  have hdescent : baseEnd_2922631 < baseStart_2922631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922648 : List Nat := [2, 1, 2, 4, 4, 1, 1, 1, 1, 4, 2]
def baseStart_2922648 : Nat := 118140960795 + 2922648 * 2 ^ 59
def prefixEnd_2922648 : Nat := 4983230072969 + 3 ^ 40 * 2922648 * 2
def baseEnd_2922648 : Nat := 1500723207901786359958993

theorem tailTrace_2922648 : CollatzResearch.WordTrace tailWord_2922648 prefixEnd_2922648 1500723207901786359958993 := by
  unfold tailWord_2922648
  simp only [CollatzResearch.WordTrace]
  refine ⟨53298864957876459692132299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71065153277168612922843065 53298864957876459692132299)
  ·
    refine ⟨79948297436814689538198449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53298864957876459692132299 79948297436814689538198449)
    ·
      refine ⟨59961223077611017153648837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79948297436814689538198449 59961223077611017153648837)
      ·
        refine ⟨11242729327052065716309157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59961223077611017153648837 11242729327052065716309157)
        ·
          refine ⟨2108011748822262321807967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11242729327052065716309157 2108011748822262321807967)
          ·
            refine ⟨3162017623233393482711951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2108011748822262321807967 3162017623233393482711951)
            ·
              refine ⟨4743026434850090224067927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3162017623233393482711951 4743026434850090224067927)
              ·
                refine ⟨7114539652275135336101891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4743026434850090224067927 7114539652275135336101891)
                ·
                  refine ⟨10671809478412703004152837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7114539652275135336101891 10671809478412703004152837)
                  ·
                    refine ⟨2000964277202381813278657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10671809478412703004152837 2000964277202381813278657)
                    ·
                      refine ⟨1500723207901786359958993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2000964277202381813278657 1500723207901786359958993)
                      ·
                        rfl

theorem cell23_2922648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_2922648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922648 prefixEnd_2922648 := by exact prefixLift 2922648
  have htrace : WordTrace (prefixWord ++ tailWord_2922648) baseStart_2922648 baseEnd_2922648 := by
    simpa [prefixWord, tailWord_2922648, baseEnd_2922648] using wordTrace_append hprefix tailTrace_2922648
  have hstable : (prefixWord ++ tailWord_2922648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922648).length < 2 ^ (prefixWord ++ tailWord_2922648).sum := by decide
  have hdescent : baseEnd_2922648 < baseStart_2922648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922684 : List Nat := [2, 2, 2, 3, 3, 1, 1, 2, 2, 5]
def baseStart_2922684 : Nat := 118140960795 + 2922684 * 2 ^ 59
def prefixEnd_2922684 : Nat := 4983230072969 + 3 ^ 40 * 2922684 * 2
def baseEnd_2922684 : Nat := 500247231068449406369609

theorem tailTrace_2922684 : CollatzResearch.WordTrace tailWord_2922684 prefixEnd_2922684 500247231068449406369609 := by
  unfold tailWord_2922684
  simp only [CollatzResearch.WordTrace]
  refine ⟨53299521471811248766287553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71066028629081665021716737 53299521471811248766287553)
  ·
    refine ⟨39974641103858436574715665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53299521471811248766287553 39974641103858436574715665)
    ·
      refine ⟨29980980827893827431036749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39974641103858436574715665 29980980827893827431036749)
      ·
        refine ⟨11242867810460185286638781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29980980827893827431036749 11242867810460185286638781)
        ·
          refine ⟨4216075428922569482489543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11242867810460185286638781 4216075428922569482489543)
          ·
            refine ⟨6324113143383854223734315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4216075428922569482489543 6324113143383854223734315)
            ·
              refine ⟨9486169715075781335601473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6324113143383854223734315 9486169715075781335601473)
              ·
                refine ⟨7114627286306836001701105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9486169715075781335601473 7114627286306836001701105)
                ·
                  refine ⟨5335970464730127001275829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7114627286306836001701105 5335970464730127001275829)
                  ·
                    refine ⟨500247231068449406369609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5335970464730127001275829 500247231068449406369609)
                    ·
                      rfl

theorem cell23_2922684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_2922684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922684 prefixEnd_2922684 := by exact prefixLift 2922684
  have htrace : WordTrace (prefixWord ++ tailWord_2922684) baseStart_2922684 baseEnd_2922684 := by
    simpa [prefixWord, tailWord_2922684, baseEnd_2922684] using wordTrace_append hprefix tailTrace_2922684
  have hstable : (prefixWord ++ tailWord_2922684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922684).length < 2 ^ (prefixWord ++ tailWord_2922684).sum := by decide
  have hdescent : baseEnd_2922684 < baseStart_2922684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922697 : List Nat := [1, 2, 1, 1, 2, 1, 1, 7, 3, 4]
def baseStart_2922697 : Nat := 118140960795 + 2922697 * 2 ^ 59
def prefixEnd_2922697 : Nat := 4983230072969 + 3 ^ 40 * 2922697 * 2
def baseEnd_2922697 : Nat := 500249456151285556082089

theorem tailTrace_2922697 : CollatzResearch.WordTrace tailWord_2922697 prefixEnd_2922697 500249456151285556082089 := by
  unfold tailWord_2922697
  simp only [CollatzResearch.WordTrace]
  refine ⟨106599517092575400752798345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71066344728383600501865563 106599517092575400752798345)
  ·
    refine ⟨79949637819431550564598759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106599517092575400752798345 79949637819431550564598759)
    ·
      refine ⟨119924456729147325846898139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79949637819431550564598759 119924456729147325846898139)
      ·
        refine ⟨179886685093720988770347209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119924456729147325846898139 179886685093720988770347209)
        ·
          refine ⟨134915013820290741577760407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179886685093720988770347209 134915013820290741577760407)
          ·
            refine ⟨202372520730436112366640611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134915013820290741577760407 202372520730436112366640611)
            ·
              refine ⟨303558781095654168549960917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202372520730436112366640611 303558781095654168549960917)
              ·
                refine ⟨7114658931929394575389709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 303558781095654168549960917 7114658931929394575389709)
                ·
                  refine ⟨2667997099473522965771141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7114658931929394575389709 2667997099473522965771141)
                  ·
                    refine ⟨500249456151285556082089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2667997099473522965771141 500249456151285556082089)
                    ·
                      rfl

theorem cell23_2922697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 4].length) (baseStart_2922697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922697 prefixEnd_2922697 := by exact prefixLift 2922697
  have htrace : WordTrace (prefixWord ++ tailWord_2922697) baseStart_2922697 baseEnd_2922697 := by
    simpa [prefixWord, tailWord_2922697, baseEnd_2922697] using wordTrace_append hprefix tailTrace_2922697
  have hstable : (prefixWord ++ tailWord_2922697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922697).length < 2 ^ (prefixWord ++ tailWord_2922697).sum := by decide
  have hdescent : baseEnd_2922697 < baseStart_2922697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922748 : List Nat := [2, 2, 2, 1, 4, 1, 4, 2, 1, 4]
def baseStart_2922748 : Nat := 118140960795 + 2922748 * 2 ^ 59
def prefixEnd_2922748 : Nat := 4983230072969 + 3 ^ 40 * 2922748 * 2
def baseEnd_2922748 : Nat := 500258185322411989569511

theorem tailTrace_2922748 : CollatzResearch.WordTrace tailWord_2922748 prefixEnd_2922748 500258185322411989569511 := by
  unfold tailWord_2922748
  simp only [CollatzResearch.WordTrace]
  refine ⟨53300688607695318231452449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71067584810260424308603265 53300688607695318231452449)
  ·
    refine ⟨39975516455771488673589337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53300688607695318231452449 39975516455771488673589337)
    ·
      refine ⟨29981637341828616505192003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39975516455771488673589337 29981637341828616505192003)
      ·
        refine ⟨44972456012742924757788005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29981637341828616505192003 44972456012742924757788005)
        ·
          refine ⟨8432335502389298392085251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44972456012742924757788005 8432335502389298392085251)
          ·
            refine ⟨12648503253583947588127877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8432335502389298392085251 12648503253583947588127877)
            ·
              refine ⟨2371594360046990172773977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12648503253583947588127877 2371594360046990172773977)
              ·
                refine ⟨1778695770035242629580483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2371594360046990172773977 1778695770035242629580483)
                ·
                  refine ⟨2668043655052863944370725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1778695770035242629580483 2668043655052863944370725)
                  ·
                    refine ⟨500258185322411989569511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2668043655052863944370725 500258185322411989569511)
                    ·
                      rfl

theorem cell23_2922748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_2922748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922748 prefixEnd_2922748 := by exact prefixLift 2922748
  have htrace : WordTrace (prefixWord ++ tailWord_2922748) baseStart_2922748 baseEnd_2922748 := by
    simpa [prefixWord, tailWord_2922748, baseEnd_2922748] using wordTrace_append hprefix tailTrace_2922748
  have hstable : (prefixWord ++ tailWord_2922748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922748).length < 2 ^ (prefixWord ++ tailWord_2922748).sum := by decide
  have hdescent : baseEnd_2922748 < baseStart_2922748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922764 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 1, 5, 2]
def baseStart_2922764 : Nat := 118140960795 + 2922764 * 2 ^ 59
def prefixEnd_2922764 : Nat := 4983230072969 + 3 ^ 40 * 2922764 * 2
def baseEnd_2922764 : Nat := 1500782771657707906108459

theorem tailTrace_2922764 : CollatzResearch.WordTrace tailWord_2922764 prefixEnd_2922764 1500782771657707906108459 := by
  unfold tailWord_2922764
  simp only [CollatzResearch.WordTrace]
  refine ⟨53300980391666335597743673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71067973855555114130324897 53300980391666335597743673)
  ·
    refine ⟨39975735293749751698307755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53300980391666335597743673 39975735293749751698307755)
    ·
      refine ⟨59963602940624627547461633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39975735293749751698307755 59963602940624627547461633)
      ·
        refine ⟨44972702205468470660596225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59963602940624627547461633 44972702205468470660596225)
        ·
          refine ⟨33729526654101352995447169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44972702205468470660596225 33729526654101352995447169)
          ·
            refine ⟨25297144990576014746585377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33729526654101352995447169 25297144990576014746585377)
            ·
              refine ⟨18972858742932011059939033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25297144990576014746585377 18972858742932011059939033)
              ·
                refine ⟨14229644057199008294954275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18972858742932011059939033 14229644057199008294954275)
                ·
                  refine ⟨21344466085798512442431413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14229644057199008294954275 21344466085798512442431413)
                  ·
                    refine ⟨2001043695543610541477945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21344466085798512442431413 2001043695543610541477945)
                    ·
                      refine ⟨1500782771657707906108459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2001043695543610541477945 1500782771657707906108459)
                      ·
                        rfl

theorem cell23_2922764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_2922764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922764 prefixEnd_2922764 := by exact prefixLift 2922764
  have htrace : WordTrace (prefixWord ++ tailWord_2922764) baseStart_2922764 baseEnd_2922764 := by
    simpa [prefixWord, tailWord_2922764, baseEnd_2922764] using wordTrace_append hprefix tailTrace_2922764
  have hstable : (prefixWord ++ tailWord_2922764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922764).length < 2 ^ (prefixWord ++ tailWord_2922764).sum := by decide
  have hdescent : baseEnd_2922764 < baseStart_2922764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922787 : List Nat := [1, 1, 1, 4, 2, 2, 1, 4, 1, 6]
def baseStart_2922787 : Nat := 118140960795 + 2922787 * 2 ^ 59
def prefixEnd_2922787 : Nat := 4983230072969 + 3 ^ 40 * 2922787 * 2
def baseEnd_2922787 : Nat := 500264860570920438706951

theorem tailTrace_2922787 : CollatzResearch.WordTrace tailWord_2922787 prefixEnd_2922787 500264860570920438706951 := by
  unfold tailWord_2922787
  simp only [CollatzResearch.WordTrace]
  refine ⟨106602799662249346123574615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71068533108166230749049743 106602799662249346123574615)
  ·
    refine ⟨159904199493374019185361923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106602799662249346123574615 159904199493374019185361923)
    ·
      refine ⟨239856299240061028778042885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159904199493374019185361923 239856299240061028778042885)
      ·
        refine ⟨44973056107511442895883041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239856299240061028778042885 44973056107511442895883041)
        ·
          refine ⟨33729792080633582171912281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44973056107511442895883041 33729792080633582171912281)
          ·
            refine ⟨25297344060475186628934211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33729792080633582171912281 25297344060475186628934211)
            ·
              refine ⟨37946016090712779943401317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25297344060475186628934211 37946016090712779943401317)
              ·
                refine ⟨7114878017008646239387747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37946016090712779943401317 7114878017008646239387747)
                ·
                  refine ⟨10672317025512969359081621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7114878017008646239387747 10672317025512969359081621)
                  ·
                    refine ⟨500264860570920438706951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10672317025512969359081621 500264860570920438706951)
                    ·
                      rfl

theorem cell23_2922787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 6].length) (baseStart_2922787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922787 prefixEnd_2922787 := by exact prefixLift 2922787
  have htrace : WordTrace (prefixWord ++ tailWord_2922787) baseStart_2922787 baseEnd_2922787 := by
    simpa [prefixWord, tailWord_2922787, baseEnd_2922787] using wordTrace_append hprefix tailTrace_2922787
  have hstable : (prefixWord ++ tailWord_2922787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922787).length < 2 ^ (prefixWord ++ tailWord_2922787).sum := by decide
  have hdescent : baseEnd_2922787 < baseStart_2922787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922788 : List Nat := [2, 3, 1, 3, 1, 2, 1, 5, 1, 1, 3]
def baseStart_2922788 : Nat := 118140960795 + 2922788 * 2 ^ 59
def prefixEnd_2922788 : Nat := 4983230072969 + 3 ^ 40 * 2922788 * 2
def baseEnd_2922788 : Nat := 1500795095193415812208349

theorem tailTrace_2922788 : CollatzResearch.WordTrace tailWord_2922788 prefixEnd_2922788 1500795095193415812208349 := by
  unfold tailWord_2922788
  simp only [CollatzResearch.WordTrace]
  refine ⟨53301418067622861647180509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71068557423497148862907345 53301418067622861647180509)
  ·
    refine ⟨19988031775358573117692691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53301418067622861647180509 19988031775358573117692691)
    ·
      refine ⟨29982047663037859676539037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19988031775358573117692691 29982047663037859676539037)
      ·
        refine ⟨11243267873639197378702139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29982047663037859676539037 11243267873639197378702139)
        ·
          refine ⟨16864901810458796068053209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11243267873639197378702139 16864901810458796068053209)
          ·
            refine ⟨12648676357844097051039907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16864901810458796068053209 12648676357844097051039907)
            ·
              refine ⟨18973014536766145576559861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12648676357844097051039907 18973014536766145576559861)
              ·
                refine ⟨1778720112821826147802487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18973014536766145576559861 1778720112821826147802487)
                ·
                  refine ⟨2668080169232739221703731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1778720112821826147802487 2668080169232739221703731)
                  ·
                    refine ⟨4002120253849108832555597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2668080169232739221703731 4002120253849108832555597)
                    ·
                      refine ⟨1500795095193415812208349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4002120253849108832555597 1500795095193415812208349)
                      ·
                        rfl

theorem cell23_2922788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_2922788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922788 prefixEnd_2922788 := by exact prefixLift 2922788
  have htrace : WordTrace (prefixWord ++ tailWord_2922788) baseStart_2922788 baseEnd_2922788 := by
    simpa [prefixWord, tailWord_2922788, baseEnd_2922788] using wordTrace_append hprefix tailTrace_2922788
  have hstable : (prefixWord ++ tailWord_2922788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922788).length < 2 ^ (prefixWord ++ tailWord_2922788).sum := by decide
  have hdescent : baseEnd_2922788 < baseStart_2922788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922807 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 4]
def baseStart_2922807 : Nat := 118140960795 + 2922807 * 2 ^ 59
def prefixEnd_2922807 : Nat := 4983230072969 + 3 ^ 40 * 2922807 * 2
def baseEnd_2922807 : Nat := 1500804851325851237870761

theorem tailTrace_2922807 : CollatzResearch.WordTrace tailWord_2922807 prefixEnd_2922807 1500804851325851237870761 := by
  unfold tailWord_2922807
  simp only [CollatzResearch.WordTrace]
  refine ⟨106603529122176889539302675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71069019414784593026201783 106603529122176889539302675)
  ·
    refine ⟨159905293683265334308954013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106603529122176889539302675 159905293683265334308954013)
    ·
      refine ⟨59964485131224500365857755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159905293683265334308954013 59964485131224500365857755)
      ·
        refine ⟨89946727696836750548786633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59964485131224500365857755 89946727696836750548786633)
        ·
          refine ⟨67460045772627562911589975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89946727696836750548786633 67460045772627562911589975)
          ·
            refine ⟨101190068658941344367384963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67460045772627562911589975 101190068658941344367384963)
            ·
              refine ⟨151785102988412016551077445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101190068658941344367384963 151785102988412016551077445)
              ·
                refine ⟨28459706810327253103327021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151785102988412016551077445 28459706810327253103327021)
                ·
                  refine ⟨10672390053872719913747633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28459706810327253103327021 10672390053872719913747633)
                  ·
                    refine ⟨8004292540404539935310725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10672390053872719913747633 8004292540404539935310725)
                    ·
                      refine ⟨1500804851325851237870761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8004292540404539935310725 1500804851325851237870761)
                      ·
                        rfl

theorem cell23_2922807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_2922807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922807 prefixEnd_2922807 := by exact prefixLift 2922807
  have htrace : WordTrace (prefixWord ++ tailWord_2922807) baseStart_2922807 baseEnd_2922807 := by
    simpa [prefixWord, tailWord_2922807, baseEnd_2922807] using wordTrace_append hprefix tailTrace_2922807
  have hstable : (prefixWord ++ tailWord_2922807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922807).length < 2 ^ (prefixWord ++ tailWord_2922807).sum := by decide
  have hdescent : baseEnd_2922807 < baseStart_2922807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922814 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_2922814 : Nat := 118140960795 + 2922814 * 2 ^ 59
def prefixEnd_2922814 : Nat := 4983230072969 + 3 ^ 40 * 2922814 * 2
def baseEnd_2922814 : Nat := 1500808445690432710483229

theorem tailTrace_2922814 : CollatzResearch.WordTrace tailWord_2922814 prefixEnd_2922814 1500808445690432710483229 := by
  unfold tailWord_2922814
  simp only [CollatzResearch.WordTrace]
  refine ⟨13325473054143941216850937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71069189622101019823204997 13325473054143941216850937)
  ·
    refine ⟨9994104790607955912638203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13325473054143941216850937 9994104790607955912638203)
    ·
      refine ⟨14991157185911933868957305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9994104790607955912638203 14991157185911933868957305)
      ·
        refine ⟨11243367889433950401717979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14991157185911933868957305 11243367889433950401717979)
        ·
          refine ⟨16865051834150925602576969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11243367889433950401717979 16865051834150925602576969)
          ·
            refine ⟨12648788875613194201932727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16865051834150925602576969 12648788875613194201932727)
            ·
              refine ⟨18973183313419791302899091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12648788875613194201932727 18973183313419791302899091)
              ·
                refine ⟨28459774970129686954348637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18973183313419791302899091 28459774970129686954348637)
                ·
                  refine ⟨10672415613798632607880739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28459774970129686954348637 10672415613798632607880739)
                  ·
                    refine ⟨16008623420697948911821109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10672415613798632607880739 16008623420697948911821109)
                    ·
                      refine ⟨1500808445690432710483229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16008623420697948911821109 1500808445690432710483229)
                      ·
                        rfl

theorem cell23_2922814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_2922814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922814 prefixEnd_2922814 := by exact prefixLift 2922814
  have htrace : WordTrace (prefixWord ++ tailWord_2922814) baseStart_2922814 baseEnd_2922814 := by
    simpa [prefixWord, tailWord_2922814, baseEnd_2922814] using wordTrace_append hprefix tailTrace_2922814
  have hstable : (prefixWord ++ tailWord_2922814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922814).length < 2 ^ (prefixWord ++ tailWord_2922814).sum := by decide
  have hdescent : baseEnd_2922814 < baseStart_2922814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2922824 : List Nat := [2, 1, 3, 1, 1, 2, 5, 1, 1, 2, 4]
def baseStart_2922824 : Nat := 118140960795 + 2922824 * 2 ^ 59
def prefixEnd_2922824 : Nat := 4983230072969 + 3 ^ 40 * 2922824 * 2
def baseEnd_2922824 : Nat := 1500813580496977671358183

theorem tailTrace_2922824 : CollatzResearch.WordTrace tailWord_2922824 prefixEnd_2922824 1500813580496977671358183 := by
  unfold tailWord_2922824
  simp only [CollatzResearch.WordTrace]
  refine ⟨53302074581557650721335763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71069432775410200961781017 53302074581557650721335763)
  ·
    refine ⟨79953111872336476082003645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53302074581557650721335763 79953111872336476082003645)
    ·
      refine ⟨29982416952126178530751367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79953111872336476082003645 29982416952126178530751367)
      ·
        refine ⟨44973625428189267796127051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29982416952126178530751367 44973625428189267796127051)
        ·
          refine ⟨67460438142283901694190577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44973625428189267796127051 67460438142283901694190577)
          ·
            refine ⟨50595328606712926270642933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67460438142283901694190577 50595328606712926270642933)
            ·
              refine ⟨4743312056879336837872775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50595328606712926270642933 4743312056879336837872775)
              ·
                refine ⟨7114968085319005256809163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4743312056879336837872775 7114968085319005256809163)
                ·
                  refine ⟨10672452127978507885213745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7114968085319005256809163 10672452127978507885213745)
                  ·
                    refine ⟨8004339095983880913910309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10672452127978507885213745 8004339095983880913910309)
                    ·
                      refine ⟨1500813580496977671358183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8004339095983880913910309 1500813580496977671358183)
                      ·
                        rfl

theorem cell23_2922824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_2922824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2922824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2922824 prefixEnd_2922824 := by exact prefixLift 2922824
  have htrace : WordTrace (prefixWord ++ tailWord_2922824) baseStart_2922824 baseEnd_2922824 := by
    simpa [prefixWord, tailWord_2922824, baseEnd_2922824] using wordTrace_append hprefix tailTrace_2922824
  have hstable : (prefixWord ++ tailWord_2922824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2922824).length < 2 ^ (prefixWord ++ tailWord_2922824).sum := by decide
  have hdescent : baseEnd_2922824 < baseStart_2922824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2922824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
