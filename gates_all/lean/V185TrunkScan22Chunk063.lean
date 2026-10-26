import V185TrunkScan22Chunk062

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_566250 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 7]
def baseStart_566250 : Nat := 118140960795 + 566250 * 2 ^ 59
def prefixEnd_566250 : Nat := 4983230072969 + 3 ^ 40 * 566250 * 2
def baseEnd_566250 : Nat := 64612982357447728437971

theorem tailTrace_566250 : CollatzResearch.WordTrace tailWord_566250 prefixEnd_566250 64612982357447728437971 := by
  unfold tailWord_566250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5163208549645108161452051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13768556132386955097205469 5163208549645108161452051)
  ·
    refine ⟨7744812824467662242178077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5163208549645108161452051 7744812824467662242178077)
    ·
      refine ⟨2904304809175373340816779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7744812824467662242178077 2904304809175373340816779)
      ·
        refine ⟨4356457213763060011225169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2904304809175373340816779 4356457213763060011225169)
        ·
          refine ⟨3267342910322295008418877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4356457213763060011225169 3267342910322295008418877)
          ·
            refine ⟨1225253591370860628157079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3267342910322295008418877 1225253591370860628157079)
            ·
              refine ⟨1837880387056290942235619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225253591370860628157079 1837880387056290942235619)
              ·
                refine ⟨2756820580584436413353429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837880387056290942235619 2756820580584436413353429)
                ·
                  refine ⟨64612982357447728437971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2756820580584436413353429 64612982357447728437971)
                  ·
                    rfl

theorem cell22_566250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_566250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566250 prefixEnd_566250 := by exact prefixLift 566250
  have htrace : WordTrace (prefixWord ++ tailWord_566250) baseStart_566250 baseEnd_566250 := by
    simpa [prefixWord, tailWord_566250, baseEnd_566250] using wordTrace_append hprefix tailTrace_566250
  have hstable : (prefixWord ++ tailWord_566250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566250).length < 2 ^ (prefixWord ++ tailWord_566250).sum := by decide
  have hdescent : baseEnd_566250 < baseStart_566250 := by decide
  rcases family_descends (prefixWord ++ tailWord_566250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566254 : List Nat := [4, 1, 2, 1, 4, 1, 2, 1, 3, 3]
def baseStart_566254 : Nat := 118140960795 + 566254 * 2 ^ 59
def prefixEnd_566254 : Nat := 4983230072969 + 3 ^ 40 * 566254 * 2
def baseEnd_566254 : Nat := 193840316354088508213901

theorem tailTrace_566254 : CollatzResearch.WordTrace tailWord_566254 prefixEnd_566254 193840316354088508213901 := by
  unfold tailWord_566254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2581622511320742666119227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13768653393710627552635877 2581622511320742666119227)
  ·
    refine ⟨3872433766981113999178841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2581622511320742666119227 3872433766981113999178841)
    ·
      refine ⟨2904325325235835499384131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3872433766981113999178841 2904325325235835499384131)
      ·
        refine ⟨4356487987853753249076197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2904325325235835499384131 4356487987853753249076197)
        ·
          refine ⟨816841497722578734201787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4356487987853753249076197 816841497722578734201787)
          ·
            refine ⟨1225262246583868101302681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816841497722578734201787 1225262246583868101302681)
            ·
              refine ⟨918946684937901075977011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225262246583868101302681 918946684937901075977011)
              ·
                refine ⟨1378420027406851613965517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 918946684937901075977011 1378420027406851613965517)
                ·
                  refine ⟨516907510277569355237069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1378420027406851613965517 516907510277569355237069)
                  ·
                    refine ⟨193840316354088508213901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 516907510277569355237069 193840316354088508213901)
                    ·
                      rfl

theorem cell22_566254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_566254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566254 prefixEnd_566254 := by exact prefixLift 566254
  have htrace : WordTrace (prefixWord ++ tailWord_566254) baseStart_566254 baseEnd_566254 := by
    simpa [prefixWord, tailWord_566254, baseEnd_566254] using wordTrace_append hprefix tailTrace_566254
  have hstable : (prefixWord ++ tailWord_566254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566254).length < 2 ^ (prefixWord ++ tailWord_566254).sum := by decide
  have hdescent : baseEnd_566254 < baseStart_566254 := by decide
  rcases family_descends (prefixWord ++ tailWord_566254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566260 : List Nat := [2, 6, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_566260 : Nat := 118140960795 + 566260 * 2 ^ 59
def prefixEnd_566260 : Nat := 4983230072969 + 3 ^ 40 * 566260 * 2
def baseEnd_566260 : Nat := 193842370276706492563883

theorem tailTrace_566260 : CollatzResearch.WordTrace tailWord_566260 prefixEnd_566260 193842370276706492563883 := by
  unfold tailWord_566260
  simp only [CollatzResearch.WordTrace]
  refine ⟨10326599464272102176836117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13768799285696136235781489 10326599464272102176836117)
  ·
    refine ⟨484059349887754789539193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10326599464272102176836117 484059349887754789539193)
    ·
      refine ⟨363044512415816092154395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 484059349887754789539193 363044512415816092154395)
      ·
        refine ⟨544566768623724138231593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363044512415816092154395 544566768623724138231593)
        ·
          refine ⟨408425076467793103673695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 544566768623724138231593 408425076467793103673695)
          ·
            refine ⟨612637614701689655510543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408425076467793103673695 612637614701689655510543)
            ·
              refine ⟨918956422052534483265815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612637614701689655510543 918956422052534483265815)
              ·
                refine ⟨1378434633078801724898723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 918956422052534483265815 1378434633078801724898723)
                ·
                  refine ⟨2067651949618202587348085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1378434633078801724898723 2067651949618202587348085)
                  ·
                    refine ⟨193842370276706492563883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2067651949618202587348085 193842370276706492563883)
                    ·
                      rfl

theorem cell22_566260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_566260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566260 prefixEnd_566260 := by exact prefixLift 566260
  have htrace : WordTrace (prefixWord ++ tailWord_566260) baseStart_566260 baseEnd_566260 := by
    simpa [prefixWord, tailWord_566260, baseEnd_566260] using wordTrace_append hprefix tailTrace_566260
  have hstable : (prefixWord ++ tailWord_566260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566260).length < 2 ^ (prefixWord ++ tailWord_566260).sum := by decide
  have hdescent : baseEnd_566260 < baseStart_566260 := by decide
  rcases family_descends (prefixWord ++ tailWord_566260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566325 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 6, 4]
def baseStart_566325 : Nat := 118140960795 + 566325 * 2 ^ 59
def prefixEnd_566325 : Nat := 4983230072969 + 3 ^ 40 * 566325 * 2
def baseEnd_566325 : Nat := 193864621105067989688683

theorem tailTrace_566325 : CollatzResearch.WordTrace tailWord_566325 prefixEnd_566325 193864621105067989688683 := by
  unfold tailWord_566325
  simp only [CollatzResearch.WordTrace]
  refine ⟨20655569673308720454788429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13770379782205813636525619 20655569673308720454788429)
  ·
    refine ⟨7745838627490770170545661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20655569673308720454788429 7745838627490770170545661)
    ·
      refine ⟨2904689485309038813954623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7745838627490770170545661 2904689485309038813954623)
      ·
        refine ⟨4357034227963558220931935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2904689485309038813954623 4357034227963558220931935)
        ·
          refine ⟨6535551341945337331397903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4357034227963558220931935 6535551341945337331397903)
          ·
            refine ⟨9803327012918005997096855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6535551341945337331397903 9803327012918005997096855)
            ·
              refine ⟨14704990519377008995645283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9803327012918005997096855 14704990519377008995645283)
              ·
                refine ⟨22057485779065513493467925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14704990519377008995645283 22057485779065513493467925)
                ·
                  refine ⟨1033944645893695945006309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22057485779065513493467925 1033944645893695945006309)
                  ·
                    refine ⟨193864621105067989688683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1033944645893695945006309 193864621105067989688683)
                    ·
                      rfl

theorem cell22_566325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_566325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566325 prefixEnd_566325 := by exact prefixLift 566325
  have htrace : WordTrace (prefixWord ++ tailWord_566325) baseStart_566325 baseEnd_566325 := by
    simpa [prefixWord, tailWord_566325, baseEnd_566325] using wordTrace_append hprefix tailTrace_566325
  have hstable : (prefixWord ++ tailWord_566325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566325).length < 2 ^ (prefixWord ++ tailWord_566325).sum := by decide
  have hdescent : baseEnd_566325 < baseStart_566325 := by decide
  rcases family_descends (prefixWord ++ tailWord_566325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566372 : List Nat := [2, 3, 1, 1, 2, 1, 1, 5, 3, 3]
def baseStart_566372 : Nat := 118140960795 + 566372 * 2 ^ 59
def prefixEnd_566372 : Nat := 4983230072969 + 3 ^ 40 * 566372 * 2
def baseEnd_566372 : Nat := 193880710165575533763539

theorem tailTrace_566372 : CollatzResearch.WordTrace tailWord_566372 prefixEnd_566372 193880710165575533763539 := by
  unfold tailWord_566372
  simp only [CollatzResearch.WordTrace]
  refine ⟨10328641952069223740874685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13771522602758964987832913 10328641952069223740874685)
  ·
    refine ⟨3873240732025958902828007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10328641952069223740874685 3873240732025958902828007)
    ·
      refine ⟨5809861098038938354242011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3873240732025958902828007 5809861098038938354242011)
      ·
        refine ⟨8714791647058407531363017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5809861098038938354242011 8714791647058407531363017)
        ·
          refine ⟨6536093735293805648522263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8714791647058407531363017 6536093735293805648522263)
          ·
            refine ⟨9804140602940708472783395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6536093735293805648522263 9804140602940708472783395)
            ·
              refine ⟨14706210904411062709175093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9804140602940708472783395 14706210904411062709175093)
              ·
                refine ⟨1378707272288537128985165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14706210904411062709175093 1378707272288537128985165)
                ·
                  refine ⟨517015227108201423369437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1378707272288537128985165 517015227108201423369437)
                  ·
                    refine ⟨193880710165575533763539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 517015227108201423369437 193880710165575533763539)
                    ·
                      rfl

theorem cell22_566372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_566372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566372 prefixEnd_566372 := by exact prefixLift 566372
  have htrace : WordTrace (prefixWord ++ tailWord_566372) baseStart_566372 baseEnd_566372 := by
    simpa [prefixWord, tailWord_566372, baseEnd_566372] using wordTrace_append hprefix tailTrace_566372
  have hstable : (prefixWord ++ tailWord_566372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566372).length < 2 ^ (prefixWord ++ tailWord_566372).sum := by decide
  have hdescent : baseEnd_566372 < baseStart_566372 := by decide
  rcases family_descends (prefixWord ++ tailWord_566372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566449 : List Nat := [1, 2, 2, 5, 1, 1, 1, 4, 1, 4]
def baseStart_566449 : Nat := 118140960795 + 566449 * 2 ^ 59
def prefixEnd_566449 : Nat := 4983230072969 + 3 ^ 40 * 566449 * 2
def baseEnd_566449 : Nat := 193907068839172999588303

theorem tailTrace_566449 : CollatzResearch.WordTrace tailWord_566449 prefixEnd_566449 193907068839172999588303 := by
  unfold tailWord_566449
  simp only [CollatzResearch.WordTrace]
  refine ⟨20660092324859489632302401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13773394883239659754868267 20660092324859489632302401)
  ·
    refine ⟨15495069243644617224226801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20660092324859489632302401 15495069243644617224226801)
    ·
      refine ⟨11621301932733462918170101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15495069243644617224226801 11621301932733462918170101)
      ·
        refine ⟨1089497056193762148578447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11621301932733462918170101 1089497056193762148578447)
        ·
          refine ⟨1634245584290643222867671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1089497056193762148578447 1634245584290643222867671)
          ·
            refine ⟨2451368376435964834301507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1634245584290643222867671 2451368376435964834301507)
            ·
              refine ⟨3677052564653947251452261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2451368376435964834301507 3677052564653947251452261)
              ·
                refine ⟨689447355872615109647299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3677052564653947251452261 689447355872615109647299)
                ·
                  refine ⟨1034171033808922664470949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 689447355872615109647299 1034171033808922664470949)
                  ·
                    refine ⟨193907068839172999588303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1034171033808922664470949 193907068839172999588303)
                    ·
                      rfl

theorem cell22_566449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_566449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566449 prefixEnd_566449 := by exact prefixLift 566449
  have htrace : WordTrace (prefixWord ++ tailWord_566449) baseStart_566449 baseEnd_566449 := by
    simpa [prefixWord, tailWord_566449, baseEnd_566449] using wordTrace_append hprefix tailTrace_566449
  have hstable : (prefixWord ++ tailWord_566449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566449).length < 2 ^ (prefixWord ++ tailWord_566449).sum := by decide
  have hdescent : baseEnd_566449 < baseStart_566449 := by decide
  rcases family_descends (prefixWord ++ tailWord_566449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566496 : List Nat := [2, 1, 1, 3, 1, 4, 4, 1, 2, 3]
def baseStart_566496 : Nat := 118140960795 + 566496 * 2 ^ 59
def prefixEnd_566496 : Nat := 4983230072969 + 3 ^ 40 * 566496 * 2
def baseEnd_566496 : Nat := 193923157899680543663159

theorem tailTrace_566496 : CollatzResearch.WordTrace tailWord_566496 prefixEnd_566496 193923157899680543663159 := by
  unfold tailWord_566496
  simp only [CollatzResearch.WordTrace]
  refine ⟨10330903277844608329631671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13774537703792811106175561 10330903277844608329631671)
  ·
    refine ⟨15496354916766912494447507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10330903277844608329631671 15496354916766912494447507)
    ·
      refine ⟨23244532375150368741671261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15496354916766912494447507 23244532375150368741671261)
      ·
        refine ⟨8716699640681388278126723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23244532375150368741671261 8716699640681388278126723)
        ·
          refine ⟨13075049461022082417190085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8716699640681388278126723 13075049461022082417190085)
          ·
            refine ⟨2451571773941640453223141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13075049461022082417190085 2451571773941640453223141)
            ·
              refine ⟨459669707614057584979339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2451571773941640453223141 459669707614057584979339)
              ·
                refine ⟨689504561421086377469009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459669707614057584979339 689504561421086377469009)
                ·
                  refine ⟨517128421065814783101757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 689504561421086377469009 517128421065814783101757)
                  ·
                    refine ⟨193923157899680543663159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 517128421065814783101757 193923157899680543663159)
                    ·
                      rfl

theorem cell22_566496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 2, 3].length) (baseStart_566496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566496 prefixEnd_566496 := by exact prefixLift 566496
  have htrace : WordTrace (prefixWord ++ tailWord_566496) baseStart_566496 baseEnd_566496 := by
    simpa [prefixWord, tailWord_566496, baseEnd_566496] using wordTrace_append hprefix tailTrace_566496
  have hstable : (prefixWord ++ tailWord_566496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566496).length < 2 ^ (prefixWord ++ tailWord_566496).sum := by decide
  have hdescent : baseEnd_566496 < baseStart_566496 := by decide
  rcases family_descends (prefixWord ++ tailWord_566496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566552 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 1, 7]
def baseStart_566552 : Nat := 118140960795 + 566552 * 2 ^ 59
def prefixEnd_566552 : Nat := 4983230072969 + 3 ^ 40 * 566552 * 2
def baseEnd_566552 : Nat := 193942327844115064262987

theorem tailTrace_566552 : CollatzResearch.WordTrace tailWord_566552 prefixEnd_566552 193942327844115064262987 := by
  unfold tailWord_566552
  simp only [CollatzResearch.WordTrace]
  refine ⟨10331924521743169111650955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13775899362324225482201273 10331924521743169111650955)
  ·
    refine ⟨15497886782614753667476433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10331924521743169111650955 15497886782614753667476433)
    ·
      refine ⟨11623415086961065250607325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15497886782614753667476433 11623415086961065250607325)
      ·
        refine ⟨4358780657610399468977747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11623415086961065250607325 4358780657610399468977747)
        ·
          refine ⟨6538170986415599203466621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4358780657610399468977747 6538170986415599203466621)
          ·
            refine ⟨2451814119905849701299983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6538170986415599203466621 2451814119905849701299983)
            ·
              refine ⟨3677721179858774551949975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2451814119905849701299983 3677721179858774551949975)
              ·
                refine ⟨5516581769788161827924963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3677721179858774551949975 5516581769788161827924963)
                ·
                  refine ⟨8274872654682242741887445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5516581769788161827924963 8274872654682242741887445)
                  ·
                    refine ⟨193942327844115064262987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8274872654682242741887445 193942327844115064262987)
                    ·
                      rfl

theorem cell22_566552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_566552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566552 prefixEnd_566552 := by exact prefixLift 566552
  have htrace : WordTrace (prefixWord ++ tailWord_566552) baseStart_566552 baseEnd_566552 := by
    simpa [prefixWord, tailWord_566552, baseEnd_566552] using wordTrace_append hprefix tailTrace_566552
  have hstable : (prefixWord ++ tailWord_566552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566552).length < 2 ^ (prefixWord ++ tailWord_566552).sum := by decide
  have hdescent : baseEnd_566552 < baseStart_566552 := by decide
  rcases family_descends (prefixWord ++ tailWord_566552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566554 : List Nat := [3, 1, 1, 3, 3, 1, 2, 3, 5]
def baseStart_566554 : Nat := 118140960795 + 566554 * 2 ^ 59
def prefixEnd_566554 : Nat := 4983230072969 + 3 ^ 40 * 566554 * 2
def baseEnd_566554 : Nat := 64647670828329241904327

theorem tailTrace_566554 : CollatzResearch.WordTrace tailWord_566554 prefixEnd_566554 64647670828329241904327 := by
  unfold tailWord_566554
  simp only [CollatzResearch.WordTrace]
  refine ⟨5165980497369773141218679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13775947992986061709916477 5165980497369773141218679)
  ·
    refine ⟨7748970746054659711828019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5165980497369773141218679 7748970746054659711828019)
    ·
      refine ⟨11623456119081989567742029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7748970746054659711828019 11623456119081989567742029)
      ·
        refine ⟨4358796044655746087903261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11623456119081989567742029 4358796044655746087903261)
        ·
          refine ⟨1634548516745904782963723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4358796044655746087903261 1634548516745904782963723)
          ·
            refine ⟨2451822775118857174445585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1634548516745904782963723 2451822775118857174445585)
            ·
              refine ⟨1838867081339142880834189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2451822775118857174445585 1838867081339142880834189)
              ·
                refine ⟨689575155502178580312821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1838867081339142880834189 689575155502178580312821)
                ·
                  refine ⟨64647670828329241904327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 689575155502178580312821 64647670828329241904327)
                  ·
                    rfl

theorem cell22_566554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_566554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566554 prefixEnd_566554 := by exact prefixLift 566554
  have htrace : WordTrace (prefixWord ++ tailWord_566554) baseStart_566554 baseEnd_566554 := by
    simpa [prefixWord, tailWord_566554, baseEnd_566554] using wordTrace_append hprefix tailTrace_566554
  have hstable : (prefixWord ++ tailWord_566554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566554).length < 2 ^ (prefixWord ++ tailWord_566554).sum := by decide
  have hdescent : baseEnd_566554 < baseStart_566554 := by decide
  rcases family_descends (prefixWord ++ tailWord_566554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566597 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 3, 5]
def baseStart_566597 : Nat := 118140960795 + 566597 * 2 ^ 59
def prefixEnd_566597 : Nat := 4983230072969 + 3 ^ 40 * 566597 * 2
def baseEnd_566597 : Nat := 193957732263749946887849

theorem tailTrace_566597 : CollatzResearch.WordTrace tailWord_566597 prefixEnd_566597 193957732263749946887849 := by
  unfold tailWord_566597
  simp only [CollatzResearch.WordTrace]
  refine ⟨20665490328323310908690045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13776993552215540605793363 20665490328323310908690045)
  ·
    refine ⟨7749558873121241590758767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20665490328323310908690045 7749558873121241590758767)
    ·
      refine ⟨11624338309681862386138151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7749558873121241590758767 11624338309681862386138151)
      ·
        refine ⟨17436507464522793579207227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11624338309681862386138151 17436507464522793579207227)
        ·
          refine ⟨26154761196784190368810841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17436507464522793579207227 26154761196784190368810841)
          ·
            refine ⟨19616070897588142776608131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26154761196784190368810841 19616070897588142776608131)
            ·
              refine ⟨29424106346382214164912197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19616070897588142776608131 29424106346382214164912197)
              ·
                refine ⟨5517019939946665155921037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29424106346382214164912197 5517019939946665155921037)
                ·
                  refine ⟨2068882477479999433470389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5517019939946665155921037 2068882477479999433470389)
                  ·
                    refine ⟨193957732263749946887849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2068882477479999433470389 193957732263749946887849)
                    ·
                      rfl

theorem cell22_566597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_566597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566597 prefixEnd_566597 := by exact prefixLift 566597
  have htrace : WordTrace (prefixWord ++ tailWord_566597) baseStart_566597 baseEnd_566597 := by
    simpa [prefixWord, tailWord_566597, baseEnd_566597] using wordTrace_append hprefix tailTrace_566597
  have hstable : (prefixWord ++ tailWord_566597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566597).length < 2 ^ (prefixWord ++ tailWord_566597).sum := by decide
  have hdescent : baseEnd_566597 < baseStart_566597 := by decide
  rcases family_descends (prefixWord ++ tailWord_566597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566599 : List Nat := [1, 1, 4, 1, 2, 4, 2, 1, 6]
def baseStart_566599 : Nat := 118140960795 + 566599 * 2 ^ 59
def prefixEnd_566599 : Nat := 4983230072969 + 3 ^ 40 * 566599 * 2
def baseEnd_566599 : Nat := 64652805634874202779281

theorem tailTrace_566599 : CollatzResearch.WordTrace tailWord_566599 prefixEnd_566599 64652805634874202779281 := by
  unfold tailWord_566599
  simp only [CollatzResearch.WordTrace]
  refine ⟨20665563274316065250262851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13777042182877376833508567 20665563274316065250262851)
  ·
    refine ⟨30998344911474097875394277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20665563274316065250262851 30998344911474097875394277)
    ·
      refine ⟨5812189670901393351636427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30998344911474097875394277 5812189670901393351636427)
      ·
        refine ⟨8718284506352090027454641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5812189670901393351636427 8718284506352090027454641)
        ·
          refine ⟨6538713379764067520590981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8718284506352090027454641 6538713379764067520590981)
          ·
            refine ⟨1226008758705762660110809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6538713379764067520590981 1226008758705762660110809)
            ·
              refine ⟨919506569029321995083107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1226008758705762660110809 919506569029321995083107)
              ·
                refine ⟨1379259853543982992624661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919506569029321995083107 1379259853543982992624661)
                ·
                  refine ⟨64652805634874202779281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1379259853543982992624661 64652805634874202779281)
                  ·
                    rfl

theorem cell22_566599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 6].length) (baseStart_566599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566599 prefixEnd_566599 := by exact prefixLift 566599
  have htrace : WordTrace (prefixWord ++ tailWord_566599) baseStart_566599 baseEnd_566599 := by
    simpa [prefixWord, tailWord_566599, baseEnd_566599] using wordTrace_append hprefix tailTrace_566599
  have hstable : (prefixWord ++ tailWord_566599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566599).length < 2 ^ (prefixWord ++ tailWord_566599).sum := by decide
  have hdescent : baseEnd_566599 < baseStart_566599 := by decide
  rcases family_descends (prefixWord ++ tailWord_566599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566605 : List Nat := [1, 6, 1, 3, 1, 1, 3, 1, 5]
def baseStart_566605 : Nat := 118140960795 + 566605 * 2 ^ 59
def prefixEnd_566605 : Nat := 4983230072969 + 3 ^ 40 * 566605 * 2
def baseEnd_566605 : Nat := 64653490275746864229275

theorem tailTrace_566605 : CollatzResearch.WordTrace tailWord_566605 prefixEnd_566605 64653490275746864229275 := by
  unfold tailWord_566605
  simp only [CollatzResearch.WordTrace]
  refine ⟨20665782112294328274981269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13777188074862885516654179 20665782112294328274981269)
  ·
    refine ⟨968708536513796637889747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20665782112294328274981269 968708536513796637889747)
    ·
      refine ⟨1453062804770694956834621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 968708536513796637889747 1453062804770694956834621)
      ·
        refine ⟨544898551789010608812983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1453062804770694956834621 544898551789010608812983)
        ·
          refine ⟨817347827683515913219475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544898551789010608812983 817347827683515913219475)
          ·
            refine ⟨1226021741525273869829213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817347827683515913219475 1226021741525273869829213)
            ·
              refine ⟨459758153071977701185955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1226021741525273869829213 459758153071977701185955)
              ·
                refine ⟨689637229607966551778933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459758153071977701185955 689637229607966551778933)
                ·
                  refine ⟨64653490275746864229275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 689637229607966551778933 64653490275746864229275)
                  ·
                    rfl

theorem cell22_566605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_566605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566605 prefixEnd_566605 := by exact prefixLift 566605
  have htrace : WordTrace (prefixWord ++ tailWord_566605) baseStart_566605 baseEnd_566605 := by
    simpa [prefixWord, tailWord_566605, baseEnd_566605] using wordTrace_append hprefix tailTrace_566605
  have hstable : (prefixWord ++ tailWord_566605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566605).length < 2 ^ (prefixWord ++ tailWord_566605).sum := by decide
  have hdescent : baseEnd_566605 < baseStart_566605 := by decide
  rcases family_descends (prefixWord ++ tailWord_566605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566629 : List Nat := [1, 3, 1, 3, 1, 2, 2, 3, 2, 4]
def baseStart_566629 : Nat := 118140960795 + 566629 * 2 ^ 59
def prefixEnd_566629 : Nat := 4983230072969 + 3 ^ 40 * 566629 * 2
def baseEnd_566629 : Nat := 193968686517712530087751

theorem tailTrace_566629 : CollatzResearch.WordTrace tailWord_566629 prefixEnd_566629 193968686517712530087751 := by
  unfold tailWord_566629
  simp only [CollatzResearch.WordTrace]
  refine ⟨20666657464207380373854941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13777771642804920249236627 20666657464207380373854941)
  ·
    refine ⟨7749996549077767640195603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20666657464207380373854941 7749996549077767640195603)
    ·
      refine ⟨11624994823616651460293405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7749996549077767640195603 11624994823616651460293405)
      ·
        refine ⟨4359373058856244297610027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11624994823616651460293405 4359373058856244297610027)
        ·
          refine ⟨6539059588284366446415041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4359373058856244297610027 6539059588284366446415041)
          ·
            refine ⟨4904294691213274834811281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6539059588284366446415041 4904294691213274834811281)
            ·
              refine ⟨3678221018409956126108461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4904294691213274834811281 3678221018409956126108461)
              ·
                refine ⟨1379332881903733547290673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3678221018409956126108461 1379332881903733547290673)
                ·
                  refine ⟨1034499661427800160468005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1379332881903733547290673 1034499661427800160468005)
                  ·
                    refine ⟨193968686517712530087751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1034499661427800160468005 193968686517712530087751)
                    ·
                      rfl

theorem cell22_566629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_566629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566629 prefixEnd_566629 := by exact prefixLift 566629
  have htrace : WordTrace (prefixWord ++ tailWord_566629) baseStart_566629 baseEnd_566629 := by
    simpa [prefixWord, tailWord_566629, baseEnd_566629] using wordTrace_append hprefix tailTrace_566629
  have hstable : (prefixWord ++ tailWord_566629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566629).length < 2 ^ (prefixWord ++ tailWord_566629).sum := by decide
  have hdescent : baseEnd_566629 < baseStart_566629 := by decide
  rcases family_descends (prefixWord ++ tailWord_566629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566665 : List Nat := [1, 2, 1, 1, 7, 2, 2, 1, 2, 3]
def baseStart_566665 : Nat := 118140960795 + 566665 * 2 ^ 59
def prefixEnd_566665 : Nat := 4983230072969 + 3 ^ 40 * 566665 * 2
def baseEnd_566665 : Nat := 193981010053420436187641

theorem tailTrace_566665 : CollatzResearch.WordTrace tailWord_566665 prefixEnd_566665 193981010053420436187641 := by
  unfold tailWord_566665
  simp only [CollatzResearch.WordTrace]
  refine ⟨20667970492076958522165449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13778646994717972348110299 20667970492076958522165449)
  ·
    refine ⟨15500977869057718891624087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20667970492076958522165449 15500977869057718891624087)
    ·
      refine ⟨23251466803586578337436131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15500977869057718891624087 23251466803586578337436131)
      ·
        refine ⟨34877200205379867506154197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23251466803586578337436131 34877200205379867506154197)
        ·
          refine ⟨817434379813590644675489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 34877200205379867506154197 817434379813590644675489)
          ·
            refine ⟨613075784860192983506617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 817434379813590644675489 613075784860192983506617)
            ·
              refine ⟨459806838645144737629963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 613075784860192983506617 459806838645144737629963)
              ·
                refine ⟨689710257967717106444945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459806838645144737629963 689710257967717106444945)
                ·
                  refine ⟨517282693475787829833709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 689710257967717106444945 517282693475787829833709)
                  ·
                    refine ⟨193981010053420436187641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 517282693475787829833709 193981010053420436187641)
                    ·
                      rfl

theorem cell22_566665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 2, 3].length) (baseStart_566665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566665 prefixEnd_566665 := by exact prefixLift 566665
  have htrace : WordTrace (prefixWord ++ tailWord_566665) baseStart_566665 baseEnd_566665 := by
    simpa [prefixWord, tailWord_566665, baseEnd_566665] using wordTrace_append hprefix tailTrace_566665
  have hstable : (prefixWord ++ tailWord_566665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566665).length < 2 ^ (prefixWord ++ tailWord_566665).sum := by decide
  have hdescent : baseEnd_566665 < baseStart_566665 := by decide
  rcases family_descends (prefixWord ++ tailWord_566665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566734 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 8]
def baseStart_566734 : Nat := 118140960795 + 566734 * 2 ^ 59
def prefixEnd_566734 : Nat := 4983230072969 + 3 ^ 40 * 566734 * 2
def baseEnd_566734 : Nat := 64668210054509085404143

theorem tailTrace_566734 : CollatzResearch.WordTrace tailWord_566734 prefixEnd_566734 64668210054509085404143 := by
  unfold tailWord_566734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2583810891103372913303407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13780324752551322204284837 2583810891103372913303407)
  ·
    refine ⟨3875716336655059369955111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2583810891103372913303407 3875716336655059369955111)
    ·
      refine ⟨5813574504982589054932667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3875716336655059369955111 5813574504982589054932667)
      ·
        refine ⟨8720361757473883582399001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5813574504982589054932667 8720361757473883582399001)
        ·
          refine ⟨6540271318105412686799251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8720361757473883582399001 6540271318105412686799251)
          ·
            refine ⟨9810406977158119030198877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6540271318105412686799251 9810406977158119030198877)
            ·
              refine ⟨3678902616434294636324579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9810406977158119030198877 3678902616434294636324579)
              ·
                refine ⟨5518353924651441954486869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3678902616434294636324579 5518353924651441954486869)
                ·
                  refine ⟨64668210054509085404143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5518353924651441954486869 64668210054509085404143)
                  ·
                    rfl

theorem cell22_566734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_566734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566734 prefixEnd_566734 := by exact prefixLift 566734
  have htrace : WordTrace (prefixWord ++ tailWord_566734) baseStart_566734 baseEnd_566734 := by
    simpa [prefixWord, tailWord_566734, baseEnd_566734] using wordTrace_append hprefix tailTrace_566734
  have hstable : (prefixWord ++ tailWord_566734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566734).length < 2 ^ (prefixWord ++ tailWord_566734).sum := by decide
  have hdescent : baseEnd_566734 < baseStart_566734 := by decide
  rcases family_descends (prefixWord ++ tailWord_566734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566753 : List Nat := [1, 2, 3, 1, 2, 3, 4, 1, 1, 4]
def baseStart_566753 : Nat := 118140960795 + 566753 * 2 ^ 59
def prefixEnd_566753 : Nat := 4983230072969 + 3 ^ 40 * 566753 * 2
def baseEnd_566753 : Nat := 194011134251817539987371

theorem tailTrace_566753 : CollatzResearch.WordTrace tailWord_566753 prefixEnd_566753 194011134251817539987371 := by
  unfold tailWord_566753
  simp only [CollatzResearch.WordTrace]
  refine ⟨20671180115758149551368913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13780786743838766367579275 20671180115758149551368913)
  ·
    refine ⟨15503385086818612163526685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20671180115758149551368913 15503385086818612163526685)
    ·
      refine ⟨5813769407556979561322507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15503385086818612163526685 5813769407556979561322507)
      ·
        refine ⟨8720654111335469341983761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5813769407556979561322507 8720654111335469341983761)
        ·
          refine ⟨6540490583501602006487821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8720654111335469341983761 6540490583501602006487821)
          ·
            refine ⟨2452683968813100752432933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6540490583501602006487821 2452683968813100752432933)
            ·
              refine ⟨459878244152456391081175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2452683968813100752432933 459878244152456391081175)
              ·
                refine ⟨689817366228684586621763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459878244152456391081175 689817366228684586621763)
                ·
                  refine ⟨1034726049343026879932645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 689817366228684586621763 1034726049343026879932645)
                  ·
                    refine ⟨194011134251817539987371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1034726049343026879932645 194011134251817539987371)
                    ·
                      rfl

theorem cell22_566753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_566753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566753 prefixEnd_566753 := by exact prefixLift 566753
  have htrace : WordTrace (prefixWord ++ tailWord_566753) baseStart_566753 baseEnd_566753 := by
    simpa [prefixWord, tailWord_566753, baseEnd_566753] using wordTrace_append hprefix tailTrace_566753
  have hstable : (prefixWord ++ tailWord_566753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566753).length < 2 ^ (prefixWord ++ tailWord_566753).sum := by decide
  have hdescent : baseEnd_566753 < baseStart_566753 := by decide
  rcases family_descends (prefixWord ++ tailWord_566753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566796 : List Nat := [2, 2, 1, 2, 5, 1, 1, 8]
def baseStart_566796 : Nat := 118140960795 + 566796 * 2 ^ 59
def prefixEnd_566796 : Nat := 4983230072969 + 3 ^ 40 * 566796 * 2
def baseEnd_566796 : Nat := 21558428225619973462471

theorem tailTrace_566796 : CollatzResearch.WordTrace tailWord_566796 prefixEnd_566796 21558428225619973462471 := by
  unfold tailWord_566796
  simp only [CollatzResearch.WordTrace]
  refine ⟨10336374227301183947592121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13781832303068245263456161 10336374227301183947592121)
  ·
    refine ⟨7752280670475887960694091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10336374227301183947592121 7752280670475887960694091)
    ·
      refine ⟨11628421005713831941041137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7752280670475887960694091 11628421005713831941041137)
      ·
        refine ⟨8721315754285373955780853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11628421005713831941041137 8721315754285373955780853)
        ·
          refine ⟨817623351964253808354455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8721315754285373955780853 817623351964253808354455)
          ·
            refine ⟨1226435027946380712531683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817623351964253808354455 1226435027946380712531683)
            ·
              refine ⟨1839652541919571068797525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1226435027946380712531683 1839652541919571068797525)
              ·
                refine ⟨21558428225619973462471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1839652541919571068797525 21558428225619973462471)
                ·
                  rfl

theorem cell22_566796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 8].length) (baseStart_566796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566796 prefixEnd_566796 := by exact prefixLift 566796
  have htrace : WordTrace (prefixWord ++ tailWord_566796) baseStart_566796 baseEnd_566796 := by
    simpa [prefixWord, tailWord_566796, baseEnd_566796] using wordTrace_append hprefix tailTrace_566796
  have hstable : (prefixWord ++ tailWord_566796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566796).length < 2 ^ (prefixWord ++ tailWord_566796).sum := by decide
  have hdescent : baseEnd_566796 < baseStart_566796 := by decide
  rcases family_descends (prefixWord ++ tailWord_566796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566826 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 2, 6]
def baseStart_566826 : Nat := 118140960795 + 566826 * 2 ^ 59
def prefixEnd_566826 : Nat := 4983230072969 + 3 ^ 40 * 566826 * 2
def baseEnd_566826 : Nat := 194036123643669682912147

theorem tailTrace_566826 : CollatzResearch.WordTrace tailWord_566826 prefixEnd_566826 194036123643669682912147 := by
  unfold tailWord_566826
  simp only [CollatzResearch.WordTrace]
  refine ⟨5168460661123420754694083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13782561762995788679184221 5168460661123420754694083)
  ·
    refine ⟨7752690991685131132041125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5168460661123420754694083 7752690991685131132041125)
    ·
      refine ⟨1453629560940962087257711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7752690991685131132041125 1453629560940962087257711)
      ·
        refine ⟨2180444341411443130886567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1453629560940962087257711 2180444341411443130886567)
        ·
          refine ⟨3270666512117164696329851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2180444341411443130886567 3270666512117164696329851)
          ·
            refine ⟨4905999768175747044494777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3270666512117164696329851 4905999768175747044494777)
            ·
              refine ⟨3679499826131810283371083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4905999768175747044494777 3679499826131810283371083)
              ·
                refine ⟨5519249739197715425056625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3679499826131810283371083 5519249739197715425056625)
                ·
                  refine ⟨4139437304398286568792469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5519249739197715425056625 4139437304398286568792469)
                  ·
                    refine ⟨194036123643669682912147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4139437304398286568792469 194036123643669682912147)
                    ·
                      rfl

theorem cell22_566826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_566826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566826 prefixEnd_566826 := by exact prefixLift 566826
  have htrace : WordTrace (prefixWord ++ tailWord_566826) baseStart_566826 baseEnd_566826 := by
    simpa [prefixWord, tailWord_566826, baseEnd_566826] using wordTrace_append hprefix tailTrace_566826
  have hstable : (prefixWord ++ tailWord_566826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566826).length < 2 ^ (prefixWord ++ tailWord_566826).sum := by decide
  have hdescent : baseEnd_566826 < baseStart_566826 := by decide
  rcases family_descends (prefixWord ++ tailWord_566826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566888 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 3, 4]
def baseStart_566888 : Nat := 118140960795 + 566888 * 2 ^ 59
def prefixEnd_566888 : Nat := 4983230072969 + 3 ^ 40 * 566888 * 2
def baseEnd_566888 : Nat := 194057347510722187861957

theorem tailTrace_566888 : CollatzResearch.WordTrace tailWord_566888 prefixEnd_566888 194057347510722187861957 := by
  unfold tailWord_566888
  simp only [CollatzResearch.WordTrace]
  refine ⟨10338051985134533803766659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13784069313512711738355545 10338051985134533803766659)
  ·
    refine ⟨15507077977701800705649989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10338051985134533803766659 15507077977701800705649989)
    ·
      refine ⟨2907577120819087632309373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15507077977701800705649989 2907577120819087632309373)
      ·
        refine ⟨1090341420307157862116015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2907577120819087632309373 1090341420307157862116015)
        ·
          refine ⟨1635512130460736793174023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1090341420307157862116015 1635512130460736793174023)
          ·
            refine ⟨2453268195691105189761035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1635512130460736793174023 2453268195691105189761035)
            ·
              refine ⟨3679902293536657784641553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453268195691105189761035 3679902293536657784641553)
              ·
                refine ⟨2759926720152493338481165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3679902293536657784641553 2759926720152493338481165)
                ·
                  refine ⟨1034972520057185001930437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2759926720152493338481165 1034972520057185001930437)
                  ·
                    refine ⟨194057347510722187861957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1034972520057185001930437 194057347510722187861957)
                    ·
                      rfl

theorem cell22_566888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_566888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566888 prefixEnd_566888 := by exact prefixLift 566888
  have htrace : WordTrace (prefixWord ++ tailWord_566888) baseStart_566888 baseEnd_566888 := by
    simpa [prefixWord, tailWord_566888, baseEnd_566888] using wordTrace_append hprefix tailTrace_566888
  have hstable : (prefixWord ++ tailWord_566888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566888).length < 2 ^ (prefixWord ++ tailWord_566888).sum := by decide
  have hdescent : baseEnd_566888 < baseStart_566888 := by decide
  rcases family_descends (prefixWord ++ tailWord_566888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566922 : List Nat := [3, 1, 2, 3, 2, 3, 2, 1, 1, 4]
def baseStart_566922 : Nat := 118140960795 + 566922 * 2 ^ 59
def prefixEnd_566922 : Nat := 4983230072969 + 3 ^ 40 * 566922 * 2
def baseEnd_566922 : Nat := 194068986405557432511853

theorem tailTrace_566922 : CollatzResearch.WordTrace tailWord_566922 prefixEnd_566922 194068986405557432511853 := by
  unfold tailWord_566922
  simp only [CollatzResearch.WordTrace]
  refine ⟨5169336013036472853567755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13784896034763927609514013 5169336013036472853567755)
  ·
    refine ⟨7754004019554709280351633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5169336013036472853567755 7754004019554709280351633)
    ·
      refine ⟨5815503014666031960263725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7754004019554709280351633 5815503014666031960263725)
      ·
        refine ⟨2180813630499761985098897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5815503014666031960263725 2180813630499761985098897)
        ·
          refine ⟨1635610222874821488824173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2180813630499761985098897 1635610222874821488824173)
          ·
            refine ⟨613353833578058058309065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1635610222874821488824173 613353833578058058309065)
            ·
              refine ⟨460015375183543543731799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 613353833578058058309065 460015375183543543731799)
              ·
                refine ⟨690023062775315315597699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460015375183543543731799 690023062775315315597699)
                ·
                  refine ⟨1035034594162972973396549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690023062775315315597699 1035034594162972973396549)
                  ·
                    refine ⟨194068986405557432511853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1035034594162972973396549 194068986405557432511853)
                    ·
                      rfl

theorem cell22_566922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_566922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566922 prefixEnd_566922 := by exact prefixLift 566922
  have htrace : WordTrace (prefixWord ++ tailWord_566922) baseStart_566922 baseEnd_566922 := by
    simpa [prefixWord, tailWord_566922, baseEnd_566922] using wordTrace_append hprefix tailTrace_566922
  have hstable : (prefixWord ++ tailWord_566922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566922).length < 2 ^ (prefixWord ++ tailWord_566922).sum := by decide
  have hdescent : baseEnd_566922 < baseStart_566922 := by decide
  rcases family_descends (prefixWord ++ tailWord_566922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566935 : List Nat := [1, 1, 3, 3, 2, 2, 3, 2, 2, 3]
def baseStart_566935 : Nat := 118140960795 + 566935 * 2 ^ 59
def prefixEnd_566935 : Nat := 4983230072969 + 3 ^ 40 * 566935 * 2
def baseEnd_566935 : Nat := 194073436571229731936813

theorem tailTrace_566935 : CollatzResearch.WordTrace tailWord_566935 prefixEnd_566935 194073436571229731936813 := by
  unfold tailWord_566935
  simp only [CollatzResearch.WordTrace]
  refine ⟨20677818201098794634494259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13785212134065863089662839 20677818201098794634494259)
  ·
    refine ⟨31016727301648191951741389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20677818201098794634494259 31016727301648191951741389)
    ·
      refine ⟨11631272738118071981903021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31016727301648191951741389 11631272738118071981903021)
      ·
        refine ⟨4361727276794276993213633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11631272738118071981903021 4361727276794276993213633)
        ·
          refine ⟨3271295457595707744910225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4361727276794276993213633 3271295457595707744910225)
          ·
            refine ⟨2453471593196780808682669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3271295457595707744910225 2453471593196780808682669)
            ·
              refine ⟨920051847448792803256001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2453471593196780808682669 920051847448792803256001)
              ·
                refine ⟨690038885586594602442001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 920051847448792803256001 690038885586594602442001)
                ·
                  refine ⟨517529164189945951831501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 690038885586594602442001 517529164189945951831501)
                  ·
                    refine ⟨194073436571229731936813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 517529164189945951831501 194073436571229731936813)
                    ·
                      rfl

theorem cell22_566935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_566935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566935 prefixEnd_566935 := by exact prefixLift 566935
  have htrace : WordTrace (prefixWord ++ tailWord_566935) baseStart_566935 baseEnd_566935 := by
    simpa [prefixWord, tailWord_566935, baseEnd_566935] using wordTrace_append hprefix tailTrace_566935
  have hstable : (prefixWord ++ tailWord_566935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566935).length < 2 ^ (prefixWord ++ tailWord_566935).sum := by decide
  have hdescent : baseEnd_566935 < baseStart_566935 := by decide
  rcases family_descends (prefixWord ++ tailWord_566935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566963 : List Nat := [1, 1, 1, 2, 3, 3, 1, 4, 3, 3]
def baseStart_566963 : Nat := 118140960795 + 566963 * 2 ^ 59
def prefixEnd_566963 : Nat := 4983230072969 + 3 ^ 40 * 566963 * 2
def baseEnd_566963 : Nat := 194083021543446992236727

theorem tailTrace_566963 : CollatzResearch.WordTrace tailWord_566963 prefixEnd_566963 194083021543446992236727 := by
  unfold tailWord_566963
  simp only [CollatzResearch.WordTrace]
  refine ⟨20678839444997355416513543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13785892963331570277675695 20678839444997355416513543)
  ·
    refine ⟨31018259167496033124770315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20678839444997355416513543 31018259167496033124770315)
    ·
      refine ⟨46527388751244049687155473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31018259167496033124770315 46527388751244049687155473)
      ·
        refine ⟨34895541563433037265366605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46527388751244049687155473 34895541563433037265366605)
        ·
          refine ⟨13085828086287388974512477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34895541563433037265366605 13085828086287388974512477)
          ·
            refine ⟨4907185532357770865442179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13085828086287388974512477 4907185532357770865442179)
            ·
              refine ⟨7360778298536656298163269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4907185532357770865442179 7360778298536656298163269)
              ·
                refine ⟨1380145930975623055905613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7360778298536656298163269 1380145930975623055905613)
                ·
                  refine ⟨517554724115858645964605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1380145930975623055905613 517554724115858645964605)
                  ·
                    refine ⟨194083021543446992236727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 517554724115858645964605 194083021543446992236727)
                    ·
                      rfl

theorem cell22_566963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 3].length) (baseStart_566963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566963 prefixEnd_566963 := by exact prefixLift 566963
  have htrace : WordTrace (prefixWord ++ tailWord_566963) baseStart_566963 baseEnd_566963 := by
    simpa [prefixWord, tailWord_566963, baseEnd_566963] using wordTrace_append hprefix tailTrace_566963
  have hstable : (prefixWord ++ tailWord_566963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566963).length < 2 ^ (prefixWord ++ tailWord_566963).sum := by decide
  have hdescent : baseEnd_566963 < baseStart_566963 := by decide
  rcases family_descends (prefixWord ++ tailWord_566963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566976 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 9]
def baseStart_566976 : Nat := 118140960795 + 566976 * 2 ^ 59
def prefixEnd_566976 : Nat := 4983230072969 + 3 ^ 40 * 566976 * 2
def baseEnd_566976 : Nat := 64695823903039763887229

theorem tailTrace_566976 : CollatzResearch.WordTrace tailWord_566976 prefixEnd_566976 64695823903039763887229 := by
  unfold tailWord_566976
  simp only [CollatzResearch.WordTrace]
  refine ⟨10339656796975129318368391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13786209062633505757824521 10339656796975129318368391)
  ·
    refine ⟨15509485195462693977552587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10339656796975129318368391 15509485195462693977552587)
    ·
      refine ⟨23264227793194040966328881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15509485195462693977552587 23264227793194040966328881)
      ·
        refine ⟨17448170844895530724746661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23264227793194040966328881 17448170844895530724746661)
        ·
          refine ⟨3271532033417912010889999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17448170844895530724746661 3271532033417912010889999)
          ·
            refine ⟨4907298050126868016334999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3271532033417912010889999 4907298050126868016334999)
            ·
              refine ⟨7360947075190302024502499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4907298050126868016334999 7360947075190302024502499)
              ·
                refine ⟨11041420612785453036753749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7360947075190302024502499 11041420612785453036753749)
                ·
                  refine ⟨64695823903039763887229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11041420612785453036753749 64695823903039763887229)
                  ·
                    rfl

theorem cell22_566976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 9].length) (baseStart_566976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566976 prefixEnd_566976 := by exact prefixLift 566976
  have htrace : WordTrace (prefixWord ++ tailWord_566976) baseStart_566976 baseEnd_566976 := by
    simpa [prefixWord, tailWord_566976, baseEnd_566976] using wordTrace_append hprefix tailTrace_566976
  have hstable : (prefixWord ++ tailWord_566976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566976).length < 2 ^ (prefixWord ++ tailWord_566976).sum := by decide
  have hdescent : baseEnd_566976 < baseStart_566976 := by decide
  rcases family_descends (prefixWord ++ tailWord_566976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566982 : List Nat := [6, 1, 2, 1, 1, 3, 8]
def baseStart_566982 : Nat := 118140960795 + 566982 * 2 ^ 59
def prefixEnd_566982 : Nat := 4983230072969 + 3 ^ 40 * 566982 * 2
def baseEnd_566982 : Nat := 7188500949323602815247

theorem tailTrace_566982 : CollatzResearch.WordTrace tailWord_566982 prefixEnd_566982 7188500949323602815247 := by
  unfold tailWord_566982
  simp only [CollatzResearch.WordTrace]
  refine ⟨646235388497766301920475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13786354954619014440970133 646235388497766301920475)
  ·
    refine ⟨969353082746649452880713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 646235388497766301920475 969353082746649452880713)
    ·
      refine ⟨727014812059987089660535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 969353082746649452880713 727014812059987089660535)
      ·
        refine ⟨1090522218089980634490803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 727014812059987089660535 1090522218089980634490803)
        ·
          refine ⟨1635783327134970951736205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1090522218089980634490803 1635783327134970951736205)
          ·
            refine ⟨613418747675614106901077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1635783327134970951736205 613418747675614106901077)
            ·
              refine ⟨7188500949323602815247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 613418747675614106901077 7188500949323602815247)
              ·
                rfl

theorem cell22_566982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 8].length) (baseStart_566982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566982 prefixEnd_566982 := by exact prefixLift 566982
  have htrace : WordTrace (prefixWord ++ tailWord_566982) baseStart_566982 baseEnd_566982 := by
    simpa [prefixWord, tailWord_566982, baseEnd_566982] using wordTrace_append hprefix tailTrace_566982
  have hstable : (prefixWord ++ tailWord_566982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566982).length < 2 ^ (prefixWord ++ tailWord_566982).sum := by decide
  have hdescent : baseEnd_566982 < baseStart_566982 := by decide
  rcases family_descends (prefixWord ++ tailWord_566982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566991 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 4, 5]
def baseStart_566991 : Nat := 118140960795 + 566991 * 2 ^ 59
def prefixEnd_566991 : Nat := 4983230072969 + 3 ^ 40 * 566991 * 2
def baseEnd_566991 : Nat := 194092606515664252536641

theorem tailTrace_566991 : CollatzResearch.WordTrace tailWord_566991 prefixEnd_566991 194092606515664252536641 := by
  unfold tailWord_566991
  simp only [CollatzResearch.WordTrace]
  refine ⟨20679860688895916198532827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13786573792597277465688551 20679860688895916198532827)
  ·
    refine ⟨31019791033343874297799241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20679860688895916198532827 31019791033343874297799241)
    ·
      refine ⟨23264843275007905723349431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31019791033343874297799241 23264843275007905723349431)
      ·
        refine ⟨34897264912511858585024147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23264843275007905723349431 34897264912511858585024147)
        ·
          refine ⟨52345897368767787877536221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34897264912511858585024147 52345897368767787877536221)
          ·
            refine ⟨19629711513287920454076083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52345897368767787877536221 19629711513287920454076083)
            ·
              refine ⟨29444567269931880681114125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19629711513287920454076083 29444567269931880681114125)
              ·
                refine ⟨11041712726224455255417797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29444567269931880681114125 11041712726224455255417797)
                ·
                  refine ⟨2070321136167085360390837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11041712726224455255417797 2070321136167085360390837)
                  ·
                    refine ⟨194092606515664252536641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2070321136167085360390837 194092606515664252536641)
                    ·
                      rfl

theorem cell22_566991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_566991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_566991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_566991 prefixEnd_566991 := by exact prefixLift 566991
  have htrace : WordTrace (prefixWord ++ tailWord_566991) baseStart_566991 baseEnd_566991 := by
    simpa [prefixWord, tailWord_566991, baseEnd_566991] using wordTrace_append hprefix tailTrace_566991
  have hstable : (prefixWord ++ tailWord_566991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566991).length < 2 ^ (prefixWord ++ tailWord_566991).sum := by decide
  have hdescent : baseEnd_566991 < baseStart_566991 := by decide
  rcases family_descends (prefixWord ++ tailWord_566991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567023 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 3, 4]
def baseStart_567023 : Nat := 118140960795 + 567023 * 2 ^ 59
def prefixEnd_567023 : Nat := 4983230072969 + 3 ^ 40 * 567023 * 2
def baseEnd_567023 : Nat := 194103560769626835736543

theorem tailTrace_567023 : CollatzResearch.WordTrace tailWord_567023 prefixEnd_567023 194103560769626835736543 := by
  unfold tailWord_567023
  simp only [CollatzResearch.WordTrace]
  refine ⟨20681027824779985663697723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13787351883186657109131815 20681027824779985663697723)
  ·
    refine ⟨31021541737169978495546585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20681027824779985663697723 31021541737169978495546585)
    ·
      refine ⟨23266156302877483871659939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31021541737169978495546585 23266156302877483871659939)
      ·
        refine ⟨34899234454316225807489909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23266156302877483871659939 34899234454316225807489909)
        ·
          refine ⟨3271803230092146169452179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34899234454316225807489909 3271803230092146169452179)
          ·
            refine ⟨4907704845138219254178269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3271803230092146169452179 4907704845138219254178269)
            ·
              refine ⟨1840389316926832220316851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4907704845138219254178269 1840389316926832220316851)
              ·
                refine ⟨2760583975390248330475277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840389316926832220316851 2760583975390248330475277)
                ·
                  refine ⟨1035218990771343123928229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2760583975390248330475277 1035218990771343123928229)
                  ·
                    refine ⟨194103560769626835736543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1035218990771343123928229 194103560769626835736543)
                    ·
                      rfl

theorem cell22_567023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_567023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567023 prefixEnd_567023 := by exact prefixLift 567023
  have htrace : WordTrace (prefixWord ++ tailWord_567023) baseStart_567023 baseEnd_567023 := by
    simpa [prefixWord, tailWord_567023, baseEnd_567023] using wordTrace_append hprefix tailTrace_567023
  have hstable : (prefixWord ++ tailWord_567023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567023).length < 2 ^ (prefixWord ++ tailWord_567023).sum := by decide
  have hdescent : baseEnd_567023 < baseStart_567023 := by decide
  rcases family_descends (prefixWord ++ tailWord_567023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567068 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 1, 6]
def baseStart_567068 : Nat := 118140960795 + 567068 * 2 ^ 59
def prefixEnd_567068 : Nat := 4983230072969 + 3 ^ 40 * 567068 * 2
def baseEnd_567068 : Nat := 194118965189261718361405

theorem tailTrace_567068 : CollatzResearch.WordTrace tailWord_567068 prefixEnd_567068 194118965189261718361405 := by
  unfold tailWord_567068
  simp only [CollatzResearch.WordTrace]
  refine ⟨10341334554808479174542929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13788446073077972232723905 10341334554808479174542929)
  ·
    refine ⟨7756000916106359380907197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10341334554808479174542929 7756000916106359380907197)
    ·
      refine ⟨2908500343539884767840199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7756000916106359380907197 2908500343539884767840199)
      ·
        refine ⟨4362750515309827151760299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2908500343539884767840199 4362750515309827151760299)
        ·
          refine ⟨6544125772964740727640449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4362750515309827151760299 6544125772964740727640449)
          ·
            refine ⟨4908094329723555545730337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6544125772964740727640449 4908094329723555545730337)
            ·
              refine ⟨3681070747292666659297753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4908094329723555545730337 3681070747292666659297753)
              ·
                refine ⟨2760803060469499994473315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3681070747292666659297753 2760803060469499994473315)
                ·
                  refine ⟨4141204590704249991709973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2760803060469499994473315 4141204590704249991709973)
                  ·
                    refine ⟨194118965189261718361405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4141204590704249991709973 194118965189261718361405)
                    ·
                      rfl

theorem cell22_567068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_567068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567068 prefixEnd_567068 := by exact prefixLift 567068
  have htrace : WordTrace (prefixWord ++ tailWord_567068) baseStart_567068 baseEnd_567068 := by
    simpa [prefixWord, tailWord_567068, baseEnd_567068] using wordTrace_append hprefix tailTrace_567068
  have hstable : (prefixWord ++ tailWord_567068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567068).length < 2 ^ (prefixWord ++ tailWord_567068).sum := by decide
  have hdescent : baseEnd_567068 < baseStart_567068 := by decide
  rcases family_descends (prefixWord ++ tailWord_567068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567149 : List Nat := [1, 5, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_567149 : Nat := 118140960795 + 567149 * 2 ^ 59
def prefixEnd_567149 : Nat := 4983230072969 + 3 ^ 40 * 567149 * 2
def baseEnd_567149 : Nat := 194146693144604507086157

theorem tailTrace_567149 : CollatzResearch.WordTrace tailWord_567149 prefixEnd_567149 194146693144604507086157 := by
  unfold tailWord_567149
  simp only [CollatzResearch.WordTrace]
  refine ⟨20685623422323509182784501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13790415614882339455189667 20685623422323509182784501)
  ·
    refine ⟨1939277195842828985886047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20685623422323509182784501 1939277195842828985886047)
    ·
      refine ⟨2908915793764243478829071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1939277195842828985886047 2908915793764243478829071)
      ·
        refine ⟨4363373690646365218243607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2908915793764243478829071 4363373690646365218243607)
        ·
          refine ⟨6545060535969547827365411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4363373690646365218243607 6545060535969547827365411)
          ·
            refine ⟨9817590803954321741048117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6545060535969547827365411 9817590803954321741048117)
            ·
              refine ⟨920399137870717663223261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9817590803954321741048117 920399137870717663223261)
              ·
                refine ⟨345149676701519123708723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 920399137870717663223261 345149676701519123708723)
                ·
                  refine ⟨517724515052278685563085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345149676701519123708723 517724515052278685563085)
                  ·
                    refine ⟨194146693144604507086157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 517724515052278685563085 194146693144604507086157)
                    ·
                      rfl

theorem cell22_567149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_567149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567149 prefixEnd_567149 := by exact prefixLift 567149
  have htrace : WordTrace (prefixWord ++ tailWord_567149) baseStart_567149 baseEnd_567149 := by
    simpa [prefixWord, tailWord_567149, baseEnd_567149] using wordTrace_append hprefix tailTrace_567149
  have hstable : (prefixWord ++ tailWord_567149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567149).length < 2 ^ (prefixWord ++ tailWord_567149).sum := by decide
  have hdescent : baseEnd_567149 < baseStart_567149 := by decide
  rcases family_descends (prefixWord ++ tailWord_567149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567166 : List Nat := [4, 2, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_567166 : Nat := 118140960795 + 567166 * 2 ^ 59
def prefixEnd_567166 : Nat := 4983230072969 + 3 ^ 40 * 567166 * 2
def baseEnd_567166 : Nat := 194152512592022129411105

theorem tailTrace_567166 : CollatzResearch.WordTrace tailWord_567166 prefixEnd_567166 194152512592022129411105 := by
  unfold tailWord_567166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2585780432907740135769169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13790828975507947390768901 2585780432907740135769169)
  ·
    refine ⟨1939335324680805101826877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2585780432907740135769169 1939335324680805101826877)
    ·
      refine ⟨727250746755301913185079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1939335324680805101826877 727250746755301913185079)
      ·
        refine ⟨1090876120132952869777619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 727250746755301913185079 1090876120132952869777619)
        ·
          refine ⟨1636314180199429304666429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1090876120132952869777619 1636314180199429304666429)
          ·
            refine ⟨613617817574785989249911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1636314180199429304666429 613617817574785989249911)
            ·
              refine ⟨920426726362178983874867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613617817574785989249911 920426726362178983874867)
              ·
                refine ⟨1380640089543268475812301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 920426726362178983874867 1380640089543268475812301)
                ·
                  refine ⟨517740033578725678429613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1380640089543268475812301 517740033578725678429613)
                  ·
                    refine ⟨194152512592022129411105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 517740033578725678429613 194152512592022129411105)
                    ·
                      rfl

theorem cell22_567166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_567166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567166 prefixEnd_567166 := by exact prefixLift 567166
  have htrace : WordTrace (prefixWord ++ tailWord_567166) baseStart_567166 baseEnd_567166 := by
    simpa [prefixWord, tailWord_567166, baseEnd_567166] using wordTrace_append hprefix tailTrace_567166
  have hstable : (prefixWord ++ tailWord_567166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567166).length < 2 ^ (prefixWord ++ tailWord_567166).sum := by decide
  have hdescent : baseEnd_567166 < baseStart_567166 := by decide
  rcases family_descends (prefixWord ++ tailWord_567166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567205 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 6, 3]
def baseStart_567205 : Nat := 118140960795 + 567205 * 2 ^ 59
def prefixEnd_567205 : Nat := 4983230072969 + 3 ^ 40 * 567205 * 2
def baseEnd_567205 : Nat := 194165863089039027685985

theorem tailTrace_567205 : CollatzResearch.WordTrace tailWord_567205 prefixEnd_567205 194165863089039027685985 := by
  unfold tailWord_567205
  simp only [CollatzResearch.WordTrace]
  refine ⟨20687665910120630746823069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13791777273413753831215379 20687665910120630746823069)
  ·
    refine ⟨7757874716295236530058651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20687665910120630746823069 7757874716295236530058651)
    ·
      refine ⟨11636812074442854795087977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7757874716295236530058651 11636812074442854795087977)
      ·
        refine ⟨8727609055832141096315983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11636812074442854795087977 8727609055832141096315983)
        ·
          refine ⟨13091413583748211644473975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8727609055832141096315983 13091413583748211644473975)
          ·
            refine ⟨19637120375622317466710963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13091413583748211644473975 19637120375622317466710963)
            ·
              refine ⟨29455680563433476200066445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19637120375622317466710963 29455680563433476200066445)
              ·
                refine ⟨11045880211287553575024917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29455680563433476200066445 11045880211287553575024917)
                ·
                  refine ⟨517775634904104073829293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11045880211287553575024917 517775634904104073829293)
                  ·
                    refine ⟨194165863089039027685985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 517775634904104073829293 194165863089039027685985)
                    ·
                      rfl

theorem cell22_567205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_567205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567205 prefixEnd_567205 := by exact prefixLift 567205
  have htrace : WordTrace (prefixWord ++ tailWord_567205) baseStart_567205 baseEnd_567205 := by
    simpa [prefixWord, tailWord_567205, baseEnd_567205] using wordTrace_append hprefix tailTrace_567205
  have hstable : (prefixWord ++ tailWord_567205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567205).length < 2 ^ (prefixWord ++ tailWord_567205).sum := by decide
  have hdescent : baseEnd_567205 < baseStart_567205 := by decide
  rcases family_descends (prefixWord ++ tailWord_567205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567252 : List Nat := [2, 4, 1, 2, 1, 1, 5, 6]
def baseStart_567252 : Nat := 118140960795 + 567252 * 2 ^ 59
def prefixEnd_567252 : Nat := 4983230072969 + 3 ^ 40 * 567252 * 2
def baseEnd_567252 : Nat := 21575772461060730195649

theorem tailTrace_567252 : CollatzResearch.WordTrace tailWord_567252 prefixEnd_567252 21575772461060730195649 := by
  unfold tailWord_567252
  simp only [CollatzResearch.WordTrace]
  refine ⟨10344690070475178886892005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13792920093966905182522673 10344690070475178886892005)
  ·
    refine ⟨1939629388214096041292251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10344690070475178886892005 1939629388214096041292251)
    ·
      refine ⟨2909444082321144061938377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1939629388214096041292251 2909444082321144061938377)
      ·
        refine ⟨2182083061740858046453783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2909444082321144061938377 2182083061740858046453783)
        ·
          refine ⟨3273124592611287069680675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2182083061740858046453783 3273124592611287069680675)
          ·
            refine ⟨4909686888916930604521013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3273124592611287069680675 4909686888916930604521013)
            ·
              refine ⟨460283145835962244173845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4909686888916930604521013 460283145835962244173845)
              ·
                refine ⟨21575772461060730195649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 460283145835962244173845 21575772461060730195649)
                ·
                  rfl

theorem cell22_567252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 6].length) (baseStart_567252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567252 prefixEnd_567252 := by exact prefixLift 567252
  have htrace : WordTrace (prefixWord ++ tailWord_567252) baseStart_567252 baseEnd_567252 := by
    simpa [prefixWord, tailWord_567252, baseEnd_567252] using wordTrace_append hprefix tailTrace_567252
  have hstable : (prefixWord ++ tailWord_567252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567252).length < 2 ^ (prefixWord ++ tailWord_567252).sum := by decide
  have hdescent : baseEnd_567252 < baseStart_567252 := by decide
  rcases family_descends (prefixWord ++ tailWord_567252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567254 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_567254 : Nat := 118140960795 + 567254 * 2 ^ 59
def prefixEnd_567254 : Nat := 4983230072969 + 3 ^ 40 * 567254 * 2
def baseEnd_567254 : Nat := 194182636790419233210835

theorem tailTrace_567254 : CollatzResearch.WordTrace tailWord_567254 prefixEnd_567254 194182636790419233210835 := by
  unfold tailWord_567254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1293090817933944507209801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13792968724628741410237877 1293090817933944507209801)
  ·
    refine ⟨969818113450458380407351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1293090817933944507209801 969818113450458380407351)
    ·
      refine ⟨1454727170175687570611027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 969818113450458380407351 1454727170175687570611027)
      ·
        refine ⟨2182090755263531355916541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1454727170175687570611027 2182090755263531355916541)
        ·
          refine ⟨818284033223824258468703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2182090755263531355916541 818284033223824258468703)
          ·
            refine ⟨1227426049835736387703055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818284033223824258468703 1227426049835736387703055)
            ·
              refine ⟨1841139074753604581554583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1227426049835736387703055 1841139074753604581554583)
              ·
                refine ⟨2761708612130406872331875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1841139074753604581554583 2761708612130406872331875)
                ·
                  refine ⟨4142562918195610308497813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2761708612130406872331875 4142562918195610308497813)
                  ·
                    refine ⟨194182636790419233210835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4142562918195610308497813 194182636790419233210835)
                    ·
                      rfl

theorem cell22_567254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_567254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567254 prefixEnd_567254 := by exact prefixLift 567254
  have htrace : WordTrace (prefixWord ++ tailWord_567254) baseStart_567254 baseEnd_567254 := by
    simpa [prefixWord, tailWord_567254, baseEnd_567254] using wordTrace_append hprefix tailTrace_567254
  have hstable : (prefixWord ++ tailWord_567254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567254).length < 2 ^ (prefixWord ++ tailWord_567254).sum := by decide
  have hdescent : baseEnd_567254 < baseStart_567254 := by decide
  rcases family_descends (prefixWord ++ tailWord_567254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567260 : List Nat := [2, 2, 6, 1, 1, 2, 2, 1, 1, 4]
def baseStart_567260 : Nat := 118140960795 + 567260 * 2 ^ 59
def prefixEnd_567260 : Nat := 4983230072969 + 3 ^ 40 * 567260 * 2
def baseEnd_567260 : Nat := 194184690713037217560817

theorem tailTrace_567260 : CollatzResearch.WordTrace tailWord_567260 prefixEnd_567260 194184690713037217560817 := by
  unfold tailWord_567260
  simp only [CollatzResearch.WordTrace]
  refine ⟨10344835962460687570037617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13793114616614250093383489 10344835962460687570037617)
  ·
    refine ⟨7758626971845515677528213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10344835962460687570037617 7758626971845515677528213)
    ·
      refine ⟨363685639305258547384135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7758626971845515677528213 363685639305258547384135)
      ·
        refine ⟨545528458957887821076203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363685639305258547384135 545528458957887821076203)
        ·
          refine ⟨818292688436831731614305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545528458957887821076203 818292688436831731614305)
          ·
            refine ⟨613719516327623798710729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 818292688436831731614305 613719516327623798710729)
            ·
              refine ⟨460289637245717849033047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 613719516327623798710729 460289637245717849033047)
              ·
                refine ⟨690434455868576773549571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460289637245717849033047 690434455868576773549571)
                ·
                  refine ⟨1035651683802865160324357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690434455868576773549571 1035651683802865160324357)
                  ·
                    refine ⟨194184690713037217560817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1035651683802865160324357 194184690713037217560817)
                    ·
                      rfl

theorem cell22_567260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_567260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567260 prefixEnd_567260 := by exact prefixLift 567260
  have htrace : WordTrace (prefixWord ++ tailWord_567260) baseStart_567260 baseEnd_567260 := by
    simpa [prefixWord, tailWord_567260, baseEnd_567260] using wordTrace_append hprefix tailTrace_567260
  have hstable : (prefixWord ++ tailWord_567260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567260).length < 2 ^ (prefixWord ++ tailWord_567260).sum := by decide
  have hdescent : baseEnd_567260 < baseStart_567260 := by decide
  rcases family_descends (prefixWord ++ tailWord_567260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567327 : List Nat := [1, 1, 2, 4, 1, 2, 1, 5, 1, 4]
def baseStart_567327 : Nat := 118140960795 + 567327 * 2 ^ 59
def prefixEnd_567327 : Nat := 4983230072969 + 3 ^ 40 * 567327 * 2
def baseEnd_567327 : Nat := 194207626182271376135611

theorem tailTrace_567327 : CollatzResearch.WordTrace tailWord_567327 prefixEnd_567327 194207626182271376135611 := by
  unfold tailWord_567327
  simp only [CollatzResearch.WordTrace]
  refine ⟨20692115615678645582764235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13794743743785763721842823 20692115615678645582764235)
  ·
    refine ⟨31038173423517968374146353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20692115615678645582764235 31038173423517968374146353)
    ·
      refine ⟨23278630067638476280609765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31038173423517968374146353 23278630067638476280609765)
      ·
        refine ⟨4364743137682214302614331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23278630067638476280609765 4364743137682214302614331)
        ·
          refine ⟨6547114706523321453921497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4364743137682214302614331 6547114706523321453921497)
          ·
            refine ⟨4910336029892491090441123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6547114706523321453921497 4910336029892491090441123)
            ·
              refine ⟨7365504044838736635661685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4910336029892491090441123 7365504044838736635661685)
              ·
                refine ⟨690516004203631559593283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7365504044838736635661685 690516004203631559593283)
                ·
                  refine ⟨1035774006305447339389925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690516004203631559593283 1035774006305447339389925)
                  ·
                    refine ⟨194207626182271376135611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1035774006305447339389925 194207626182271376135611)
                    ·
                      rfl

theorem cell22_567327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 4].length) (baseStart_567327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567327 prefixEnd_567327 := by exact prefixLift 567327
  have htrace : WordTrace (prefixWord ++ tailWord_567327) baseStart_567327 baseEnd_567327 := by
    simpa [prefixWord, tailWord_567327, baseEnd_567327] using wordTrace_append hprefix tailTrace_567327
  have hstable : (prefixWord ++ tailWord_567327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567327).length < 2 ^ (prefixWord ++ tailWord_567327).sum := by decide
  have hdescent : baseEnd_567327 < baseStart_567327 := by decide
  rcases family_descends (prefixWord ++ tailWord_567327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567335 : List Nat := [1, 1, 7, 1, 2, 1, 3, 2, 1, 3]
def baseStart_567335 : Nat := 118140960795 + 567335 * 2 ^ 59
def prefixEnd_567335 : Nat := 4983230072969 + 3 ^ 40 * 567335 * 2
def baseEnd_567335 : Nat := 194210364745762021935587

theorem tailTrace_567335 : CollatzResearch.WordTrace tailWord_567335 prefixEnd_567335 194210364745762021935587 := by
  unfold tailWord_567335
  simp only [CollatzResearch.WordTrace]
  refine ⟨20692407399649662949055459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13794938266433108632703639 20692407399649662949055459)
  ·
    refine ⟨31038611099474494423583189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20692407399649662949055459 31038611099474494423583189)
    ·
      refine ⟨727467447643933463052731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 31038611099474494423583189 727467447643933463052731)
      ·
        refine ⟨1091201171465900194579097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 727467447643933463052731 1091201171465900194579097)
        ·
          refine ⟨818400878599425145934323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1091201171465900194579097 818400878599425145934323)
          ·
            refine ⟨1227601317899137718901485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818400878599425145934323 1227601317899137718901485)
            ·
              refine ⟨460350494212176644588057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1227601317899137718901485 460350494212176644588057)
              ·
                refine ⟨345262870659132483441043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 460350494212176644588057 345262870659132483441043)
                ·
                  refine ⟨517894305988698725161565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345262870659132483441043 517894305988698725161565)
                  ·
                    refine ⟨194210364745762021935587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 517894305988698725161565 194210364745762021935587)
                    ·
                      rfl

theorem cell22_567335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_567335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567335 prefixEnd_567335 := by exact prefixLift 567335
  have htrace : WordTrace (prefixWord ++ tailWord_567335) baseStart_567335 baseEnd_567335 := by
    simpa [prefixWord, tailWord_567335, baseEnd_567335] using wordTrace_append hprefix tailTrace_567335
  have hstable : (prefixWord ++ tailWord_567335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567335).length < 2 ^ (prefixWord ++ tailWord_567335).sum := by decide
  have hdescent : baseEnd_567335 < baseStart_567335 := by decide
  rcases family_descends (prefixWord ++ tailWord_567335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567340 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 5, 5]
def baseStart_567340 : Nat := 118140960795 + 567340 * 2 ^ 59
def prefixEnd_567340 : Nat := 4983230072969 + 3 ^ 40 * 567340 * 2
def baseEnd_567340 : Nat := 194212076347943675560571

theorem tailTrace_567340 : CollatzResearch.WordTrace tailWord_567340 prefixEnd_567340 194212076347943675560571 := by
  unfold tailWord_567340
  simp only [CollatzResearch.WordTrace]
  refine ⟨10346294882315774401493737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13795059843087699201991649 10346294882315774401493737)
  ·
    refine ⟨7759721161736830801120303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10346294882315774401493737 7759721161736830801120303)
    ·
      refine ⟨11639581742605246201680455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7759721161736830801120303 11639581742605246201680455)
      ·
        refine ⟨17459372613907869302520683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11639581742605246201680455 17459372613907869302520683)
        ·
          refine ⟨26189058920861803953781025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17459372613907869302520683 26189058920861803953781025)
          ·
            refine ⟨19641794190646352965335769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26189058920861803953781025 19641794190646352965335769)
            ·
              refine ⟨14731345642984764724001827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19641794190646352965335769 14731345642984764724001827)
              ·
                refine ⟨22097018464477147086002741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14731345642984764724001827 22097018464477147086002741)
                ·
                  refine ⟨2071595481044732539312757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22097018464477147086002741 2071595481044732539312757)
                  ·
                    refine ⟨194212076347943675560571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2071595481044732539312757 194212076347943675560571)
                    ·
                      rfl

theorem cell22_567340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_567340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567340 prefixEnd_567340 := by exact prefixLift 567340
  have htrace : WordTrace (prefixWord ++ tailWord_567340) baseStart_567340 baseEnd_567340 := by
    simpa [prefixWord, tailWord_567340, baseEnd_567340] using wordTrace_append hprefix tailTrace_567340
  have hstable : (prefixWord ++ tailWord_567340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567340).length < 2 ^ (prefixWord ++ tailWord_567340).sum := by decide
  have hdescent : baseEnd_567340 < baseStart_567340 := by decide
  rcases family_descends (prefixWord ++ tailWord_567340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567348 : List Nat := [2, 5, 1, 2, 2, 2, 2, 1, 5]
def baseStart_567348 : Nat := 118140960795 + 567348 * 2 ^ 59
def prefixEnd_567348 : Nat := 4983230072969 + 3 ^ 40 * 567348 * 2
def baseEnd_567348 : Nat := 64738271637144773786849

theorem tailTrace_567348 : CollatzResearch.WordTrace tailWord_567348 prefixEnd_567348 64738271637144773786849 := by
  unfold tailWord_567348
  simp only [CollatzResearch.WordTrace]
  refine ⟨10346440774301283084639349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13795254365735044112852465 10346440774301283084639349)
  ·
    refine ⟨969978822590745289184939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10346440774301283084639349 969978822590745289184939)
    ·
      refine ⟨1454968233886117933777409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 969978822590745289184939 1454968233886117933777409)
      ·
        refine ⟨1091226175414588450333057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1454968233886117933777409 1091226175414588450333057)
        ·
          refine ⟨818419631560941337749793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1091226175414588450333057 818419631560941337749793)
          ·
            refine ⟨613814723670706003312345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 818419631560941337749793 613814723670706003312345)
            ·
              refine ⟨460361042753029502484259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 613814723670706003312345 460361042753029502484259)
              ·
                refine ⟨690541564129544253726389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460361042753029502484259 690541564129544253726389)
                ·
                  refine ⟨64738271637144773786849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 690541564129544253726389 64738271637144773786849)
                  ·
                    rfl

theorem cell22_567348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_567348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567348 prefixEnd_567348 := by exact prefixLift 567348
  have htrace : WordTrace (prefixWord ++ tailWord_567348) baseStart_567348 baseEnd_567348 := by
    simpa [prefixWord, tailWord_567348, baseEnd_567348] using wordTrace_append hprefix tailTrace_567348
  have hstable : (prefixWord ++ tailWord_567348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567348).length < 2 ^ (prefixWord ++ tailWord_567348).sum := by decide
  have hdescent : baseEnd_567348 < baseStart_567348 := by decide
  rcases family_descends (prefixWord ++ tailWord_567348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567357 : List Nat := [1, 4, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_567357 : Nat := 118140960795 + 567357 * 2 ^ 59
def prefixEnd_567357 : Nat := 4983230072969 + 3 ^ 40 * 567357 * 2
def baseEnd_567357 : Nat := 194217895795361297885519

theorem tailTrace_567357 : CollatzResearch.WordTrace tailWord_567357 prefixEnd_567357 194217895795361297885519 := by
  unfold tailWord_567357
  simp only [CollatzResearch.WordTrace]
  refine ⟨20693209805569960706356325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13795473203713307137570883 20693209805569960706356325)
  ·
    refine ⟨3879976838544367632441811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20693209805569960706356325 3879976838544367632441811)
    ·
      refine ⟨5819965257816551448662717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3879976838544367632441811 5819965257816551448662717)
      ·
        refine ⟨2182486971681206793248519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5819965257816551448662717 2182486971681206793248519)
        ·
          refine ⟨3273730457521810189872779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2182486971681206793248519 3273730457521810189872779)
          ·
            refine ⟨4910595686282715284809169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3273730457521810189872779 4910595686282715284809169)
            ·
              refine ⟨3682946764712036463606877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4910595686282715284809169 3682946764712036463606877)
              ·
                refine ⟨1381105036767013673852579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3682946764712036463606877 1381105036767013673852579)
                ·
                  refine ⟨2071657555150520510778869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381105036767013673852579 2071657555150520510778869)
                  ·
                    refine ⟨194217895795361297885519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2071657555150520510778869 194217895795361297885519)
                    ·
                      rfl

theorem cell22_567357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_567357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567357 prefixEnd_567357 := by exact prefixLift 567357
  have htrace : WordTrace (prefixWord ++ tailWord_567357) baseStart_567357 baseEnd_567357 := by
    simpa [prefixWord, tailWord_567357, baseEnd_567357] using wordTrace_append hprefix tailTrace_567357
  have hstable : (prefixWord ++ tailWord_567357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567357).length < 2 ^ (prefixWord ++ tailWord_567357).sum := by decide
  have hdescent : baseEnd_567357 < baseStart_567357 := by decide
  rcases family_descends (prefixWord ++ tailWord_567357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567361 : List Nat := [1, 2, 5, 1, 2, 3, 1, 2, 1, 4]
def baseStart_567361 : Nat := 118140960795 + 567361 * 2 ^ 59
def prefixEnd_567361 : Nat := 4983230072969 + 3 ^ 40 * 567361 * 2
def baseEnd_567361 : Nat := 194219265077106620785507

theorem tailTrace_567361 : CollatzResearch.WordTrace tailWord_567361 prefixEnd_567361 194219265077106620785507 := by
  unfold tailWord_567361
  simp only [CollatzResearch.WordTrace]
  refine ⟨20693355697555469389501937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13795570465036979593001291 20693355697555469389501937)
  ·
    refine ⟨15520016773166602042126453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20693355697555469389501937 15520016773166602042126453)
    ·
      refine ⟨1455001572484368941449355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15520016773166602042126453 1455001572484368941449355)
      ·
        refine ⟨2182502358726553412174033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1455001572484368941449355 2182502358726553412174033)
        ·
          refine ⟨1636876769044915059130525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2182502358726553412174033 1636876769044915059130525)
          ·
            refine ⟨613828788391843147173947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1636876769044915059130525 613828788391843147173947)
            ·
              refine ⟨920743182587764720760921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613828788391843147173947 920743182587764720760921)
              ·
                refine ⟨690557386940823540570691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 920743182587764720760921 690557386940823540570691)
                ·
                  refine ⟨1035836080411235310856037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690557386940823540570691 1035836080411235310856037)
                  ·
                    refine ⟨194219265077106620785507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1035836080411235310856037 194219265077106620785507)
                    ·
                      rfl

theorem cell22_567361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_567361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567361 prefixEnd_567361 := by exact prefixLift 567361
  have htrace : WordTrace (prefixWord ++ tailWord_567361) baseStart_567361 baseEnd_567361 := by
    simpa [prefixWord, tailWord_567361, baseEnd_567361] using wordTrace_append hprefix tailTrace_567361
  have hstable : (prefixWord ++ tailWord_567361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567361).length < 2 ^ (prefixWord ++ tailWord_567361).sum := by decide
  have hdescent : baseEnd_567361 < baseStart_567361 := by decide
  rcases family_descends (prefixWord ++ tailWord_567361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567372 : List Nat := [2, 2, 1, 3, 1, 1, 3, 3, 2, 4]
def baseStart_567372 : Nat := 118140960795 + 567372 * 2 ^ 59
def prefixEnd_567372 : Nat := 4983230072969 + 3 ^ 40 * 567372 * 2
def baseEnd_567372 : Nat := 194223030601906258760473

theorem tailTrace_567372 : CollatzResearch.WordTrace tailWord_567372 prefixEnd_567372 194223030601906258760473 := by
  unfold tailWord_567372
  simp only [CollatzResearch.WordTrace]
  refine ⟨10346878450257809134076185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13795837933677078845434913 10346878450257809134076185)
  ·
    refine ⟨7760158837693356850557139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10346878450257809134076185 7760158837693356850557139)
    ·
      refine ⟨11640238256540035275835709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7760158837693356850557139 11640238256540035275835709)
      ·
        refine ⟨4365089346202513228438391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11640238256540035275835709 4365089346202513228438391)
        ·
          refine ⟨6547634019303769842657587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4365089346202513228438391 6547634019303769842657587)
          ·
            refine ⟨9821451028955654763986381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6547634019303769842657587 9821451028955654763986381)
            ·
              refine ⟨3683044135858370536494893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9821451028955654763986381 3683044135858370536494893)
              ·
                refine ⟨1381141550946888951185585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3683044135858370536494893 1381141550946888951185585)
                ·
                  refine ⟨1035856163210166713389189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1381141550946888951185585 1035856163210166713389189)
                  ·
                    refine ⟨194223030601906258760473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1035856163210166713389189 194223030601906258760473)
                    ·
                      rfl

theorem cell22_567372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_567372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567372 prefixEnd_567372 := by exact prefixLift 567372
  have htrace : WordTrace (prefixWord ++ tailWord_567372) baseStart_567372 baseEnd_567372 := by
    simpa [prefixWord, tailWord_567372, baseEnd_567372] using wordTrace_append hprefix tailTrace_567372
  have hstable : (prefixWord ++ tailWord_567372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567372).length < 2 ^ (prefixWord ++ tailWord_567372).sum := by decide
  have hdescent : baseEnd_567372 < baseStart_567372 := by decide
  rcases family_descends (prefixWord ++ tailWord_567372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567479 : List Nat := [1, 1, 3, 1, 4, 2, 1, 4, 1, 4]
def baseStart_567479 : Nat := 118140960795 + 567479 * 2 ^ 59
def prefixEnd_567479 : Nat := 4983230072969 + 3 ^ 40 * 567479 * 2
def baseEnd_567479 : Nat := 194259658888593646335145

theorem tailTrace_567479 : CollatzResearch.WordTrace tailWord_567479 prefixEnd_567479 194259658888593646335145 := by
  unfold tailWord_567479
  simp only [CollatzResearch.WordTrace]
  refine ⟨20697659511127975542297491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13798439674085317028198327 20697659511127975542297491)
  ·
    refine ⟨31046489266691963313446237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20697659511127975542297491 31046489266691963313446237)
    ·
      refine ⟨11642433475009486242542339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31046489266691963313446237 11642433475009486242542339)
      ·
        refine ⟨17463650212514229363813509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11642433475009486242542339 17463650212514229363813509)
        ·
          refine ⟨3274434414846418005715033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17463650212514229363813509 3274434414846418005715033)
          ·
            refine ⟨2455825811134813504286275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3274434414846418005715033 2455825811134813504286275)
            ·
              refine ⟨3683738716702220256429413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2455825811134813504286275 3683738716702220256429413)
              ·
                refine ⟨690701009381666298080515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3683738716702220256429413 690701009381666298080515)
                ·
                  refine ⟨1036051514072499447120773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690701009381666298080515 1036051514072499447120773)
                  ·
                    refine ⟨194259658888593646335145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1036051514072499447120773 194259658888593646335145)
                    ·
                      rfl

theorem cell22_567479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_567479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567479 prefixEnd_567479 := by exact prefixLift 567479
  have htrace : WordTrace (prefixWord ++ tailWord_567479) baseStart_567479 baseEnd_567479 := by
    simpa [prefixWord, tailWord_567479, baseEnd_567479] using wordTrace_append hprefix tailTrace_567479
  have hstable : (prefixWord ++ tailWord_567479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567479).length < 2 ^ (prefixWord ++ tailWord_567479).sum := by decide
  have hdescent : baseEnd_567479 < baseStart_567479 := by decide
  rcases family_descends (prefixWord ++ tailWord_567479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567537 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 2, 7]
def baseStart_567537 : Nat := 118140960795 + 567537 * 2 ^ 59
def prefixEnd_567537 : Nat := 4983230072969 + 3 ^ 40 * 567537 * 2
def baseEnd_567537 : Nat := 194279513473900828384967

theorem tailTrace_567537 : CollatzResearch.WordTrace tailWord_567537 prefixEnd_567537 194279513473900828384967 := by
  unfold tailWord_567537
  simp only [CollatzResearch.WordTrace]
  refine ⟨20699774944917851447908865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13799849963278567631939243 20699774944917851447908865)
  ·
    refine ⟨15524831208688388585931649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20699774944917851447908865 15524831208688388585931649)
    ·
      refine ⟨11643623406516291439448737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15524831208688388585931649 11643623406516291439448737)
      ·
        refine ⟨8732717554887218579586553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11643623406516291439448737 8732717554887218579586553)
        ·
          refine ⟨6549538166165413934689915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8732717554887218579586553 6549538166165413934689915)
          ·
            refine ⟨9824307249248120902034873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6549538166165413934689915 9824307249248120902034873)
            ·
              refine ⟨7368230436936090676526155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9824307249248120902034873 7368230436936090676526155)
              ·
                refine ⟨11052345655404136014789233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7368230436936090676526155 11052345655404136014789233)
                ·
                  refine ⟨8289259241553102011091925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11052345655404136014789233 8289259241553102011091925)
                  ·
                    refine ⟨194279513473900828384967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8289259241553102011091925 194279513473900828384967)
                    ·
                      rfl

theorem cell22_567537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_567537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567537 prefixEnd_567537 := by exact prefixLift 567537
  have htrace : WordTrace (prefixWord ++ tailWord_567537) baseStart_567537 baseEnd_567537 := by
    simpa [prefixWord, tailWord_567537, baseEnd_567537] using wordTrace_append hprefix tailTrace_567537
  have hstable : (prefixWord ++ tailWord_567537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567537).length < 2 ^ (prefixWord ++ tailWord_567537).sum := by decide
  have hdescent : baseEnd_567537 < baseStart_567537 := by decide
  rcases family_descends (prefixWord ++ tailWord_567537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567567 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 7]
def baseStart_567567 : Nat := 118140960795 + 567567 * 2 ^ 59
def prefixEnd_567567 : Nat := 4983230072969 + 3 ^ 40 * 567567 * 2
def baseEnd_567567 : Nat := 64763261028996916711625

theorem tailTrace_567567 : CollatzResearch.WordTrace tailWord_567567 prefixEnd_567567 64763261028996916711625 := by
  unfold tailWord_567567
  simp only [CollatzResearch.WordTrace]
  refine ⟨20700869134809166571500955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13800579423206111047667303 20700869134809166571500955)
  ·
    refine ⟨31051303702213749857251433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20700869134809166571500955 31051303702213749857251433)
    ·
      refine ⟨23288477776660312392938575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31051303702213749857251433 23288477776660312392938575)
      ·
        refine ⟨34932716664990468589407863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23288477776660312392938575 34932716664990468589407863)
        ·
          refine ⟨52399074997485702884111795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34932716664990468589407863 52399074997485702884111795)
          ·
            refine ⟨78598612496228554326167693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52399074997485702884111795 78598612496228554326167693)
            ·
              refine ⟨29474479686085707872312885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78598612496228554326167693 29474479686085707872312885)
              ·
                refine ⟨2763232470570535113029333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29474479686085707872312885 2763232470570535113029333)
                ·
                  refine ⟨64763261028996916711625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2763232470570535113029333 64763261028996916711625)
                  ·
                    rfl

theorem cell22_567567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 7].length) (baseStart_567567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567567 prefixEnd_567567 := by exact prefixLift 567567
  have htrace : WordTrace (prefixWord ++ tailWord_567567) baseStart_567567 baseEnd_567567 := by
    simpa [prefixWord, tailWord_567567, baseEnd_567567] using wordTrace_append hprefix tailTrace_567567
  have hstable : (prefixWord ++ tailWord_567567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567567).length < 2 ^ (prefixWord ++ tailWord_567567).sum := by decide
  have hdescent : baseEnd_567567 < baseStart_567567 := by decide
  rcases family_descends (prefixWord ++ tailWord_567567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567648 : List Nat := [2, 1, 1, 3, 5, 1, 2, 2, 1, 4]
def baseStart_567648 : Nat := 118140960795 + 567648 * 2 ^ 59
def prefixEnd_567648 : Nat := 4983230072969 + 3 ^ 40 * 567648 * 2
def baseEnd_567648 : Nat := 194317511042333538859627

theorem tailTrace_567648 : CollatzResearch.WordTrace tailWord_567648 prefixEnd_567648 194317511042333538859627 := by
  unfold tailWord_567648
  simp only [CollatzResearch.WordTrace]
  refine ⟨10351911723757858702599799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13802548965010478270133065 10351911723757858702599799)
  ·
    refine ⟨15527867585636788053899699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10351911723757858702599799 15527867585636788053899699)
    ·
      refine ⟨23291801378455182080849549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15527867585636788053899699 23291801378455182080849549)
      ·
        refine ⟨8734425516920693280318581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23291801378455182080849549 8734425516920693280318581)
        ·
          refine ⟨818852392211314995029867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8734425516920693280318581 818852392211314995029867)
          ·
            refine ⟨1228278588316972492544801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818852392211314995029867 1228278588316972492544801)
            ·
              refine ⟨921208941237729369408601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1228278588316972492544801 921208941237729369408601)
              ·
                refine ⟨690906705928297027056451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 921208941237729369408601 690906705928297027056451)
                ·
                  refine ⟨1036360058892445540584677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690906705928297027056451 1036360058892445540584677)
                  ·
                    refine ⟨194317511042333538859627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1036360058892445540584677 194317511042333538859627)
                    ·
                      rfl

theorem cell22_567648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 1, 4].length) (baseStart_567648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567648 prefixEnd_567648 := by exact prefixLift 567648
  have htrace : WordTrace (prefixWord ++ tailWord_567648) baseStart_567648 baseEnd_567648 := by
    simpa [prefixWord, tailWord_567648, baseEnd_567648] using wordTrace_append hprefix tailTrace_567648
  have hstable : (prefixWord ++ tailWord_567648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567648).length < 2 ^ (prefixWord ++ tailWord_567648).sum := by decide
  have hdescent : baseEnd_567648 < baseStart_567648 := by decide
  rcases family_descends (prefixWord ++ tailWord_567648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567661 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_567661 : Nat := 118140960795 + 567661 * 2 ^ 59
def prefixEnd_567661 : Nat := 4983230072969 + 3 ^ 40 * 567661 * 2
def baseEnd_567661 : Nat := 194321961208005838284587

theorem tailTrace_567661 : CollatzResearch.WordTrace tailWord_567661 prefixEnd_567661 194321961208005838284587 := by
  unfold tailWord_567661
  simp only [CollatzResearch.WordTrace]
  refine ⟨20704297596468620625422837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13802865064312413750281891 20704297596468620625422837)
  ·
    refine ⟨1941027899668933183633391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20704297596468620625422837 1941027899668933183633391)
    ·
      refine ⟨2911541849503399775450087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1941027899668933183633391 2911541849503399775450087)
      ·
        refine ⟨4367312774255099663175131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2911541849503399775450087 4367312774255099663175131)
        ·
          refine ⟨6550969161382649494762697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4367312774255099663175131 6550969161382649494762697)
          ·
            refine ⟨4913226871036987121072023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6550969161382649494762697 4913226871036987121072023)
            ·
              refine ⟨7369840306555480681608035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4913226871036987121072023 7369840306555480681608035)
              ·
                refine ⟨11054760459833221022412053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7369840306555480681608035 11054760459833221022412053)
                ·
                  refine ⟨518191896554682235425565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11054760459833221022412053 518191896554682235425565)
                  ·
                    refine ⟨194321961208005838284587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 518191896554682235425565 194321961208005838284587)
                    ·
                      rfl

theorem cell22_567661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_567661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567661 prefixEnd_567661 := by exact prefixLift 567661
  have htrace : WordTrace (prefixWord ++ tailWord_567661) baseStart_567661 baseEnd_567661 := by
    simpa [prefixWord, tailWord_567661, baseEnd_567661] using wordTrace_append hprefix tailTrace_567661
  have hstable : (prefixWord ++ tailWord_567661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567661).length < 2 ^ (prefixWord ++ tailWord_567661).sum := by decide
  have hdescent : baseEnd_567661 < baseStart_567661 := by decide
  rcases family_descends (prefixWord ++ tailWord_567661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567710 : List Nat := [4, 3, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_567710 : Nat := 118140960795 + 567710 * 2 ^ 59
def prefixEnd_567710 : Nat := 4983230072969 + 3 ^ 40 * 567710 * 2
def baseEnd_567710 : Nat := 194338734909386043809437

theorem tailTrace_567710 : CollatzResearch.WordTrace tailWord_567710 prefixEnd_567710 194338734909386043809437 := by
  unfold tailWord_567710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2588260596661387749244573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13804056515527401329304389 2588260596661387749244573)
  ·
    refine ⟨970597723748020405966715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2588260596661387749244573 970597723748020405966715)
    ·
      refine ⟨1455896585622030608950073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 970597723748020405966715 1455896585622030608950073)
      ·
        refine ⟨1091922439216522956712555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1455896585622030608950073 1091922439216522956712555)
        ·
          refine ⟨1637883658824784435068833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1091922439216522956712555 1637883658824784435068833)
          ·
            refine ⟨1228412744118588326301625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1637883658824784435068833 1228412744118588326301625)
            ·
              refine ⟨921309558088941244726219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1228412744118588326301625 921309558088941244726219)
              ·
                refine ⟨1381964337133411867089329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 921309558088941244726219 1381964337133411867089329)
                ·
                  refine ⟨1036473252850058900316997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1381964337133411867089329 1036473252850058900316997)
                  ·
                    refine ⟨194338734909386043809437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1036473252850058900316997 194338734909386043809437)
                    ·
                      rfl

theorem cell22_567710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_567710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567710 prefixEnd_567710 := by exact prefixLift 567710
  have htrace : WordTrace (prefixWord ++ tailWord_567710) baseStart_567710 baseEnd_567710 := by
    simpa [prefixWord, tailWord_567710, baseEnd_567710] using wordTrace_append hprefix tailTrace_567710
  have hstable : (prefixWord ++ tailWord_567710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567710).length < 2 ^ (prefixWord ++ tailWord_567710).sum := by decide
  have hdescent : baseEnd_567710 < baseStart_567710 := by decide
  rcases family_descends (prefixWord ++ tailWord_567710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567751 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 2, 5]
def baseStart_567751 : Nat := 118140960795 + 567751 * 2 ^ 59
def prefixEnd_567751 : Nat := 4983230072969 + 3 ^ 40 * 567751 * 2
def baseEnd_567751 : Nat := 194352770047275603534311

theorem tailTrace_567751 : CollatzResearch.WordTrace tailWord_567751 prefixEnd_567751 194352770047275603534311 := by
  unfold tailWord_567751
  simp only [CollatzResearch.WordTrace]
  refine ⟨20707580166142565996199107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13805053444095043997466071 20707580166142565996199107)
  ·
    refine ⟨31061370249213848994298661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20707580166142565996199107 31061370249213848994298661)
    ·
      refine ⟨5824006921727596686430999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31061370249213848994298661 5824006921727596686430999)
      ·
        refine ⟨8736010382591395029646499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5824006921727596686430999 8736010382591395029646499)
        ·
          refine ⟨13104015573887092544469749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8736010382591395029646499 13104015573887092544469749)
          ·
            refine ⟨1228501460051914926044039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13104015573887092544469749 1228501460051914926044039)
            ·
              refine ⟨1842752190077872389066059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228501460051914926044039 1842752190077872389066059)
              ·
                refine ⟨2764128285116808583599089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1842752190077872389066059 2764128285116808583599089)
                ·
                  refine ⟨2073096213837606437699317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2764128285116808583599089 2073096213837606437699317)
                  ·
                    refine ⟨194352770047275603534311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2073096213837606437699317 194352770047275603534311)
                    ·
                      rfl

theorem cell22_567751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_567751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567751 prefixEnd_567751 := by exact prefixLift 567751
  have htrace : WordTrace (prefixWord ++ tailWord_567751) baseStart_567751 baseEnd_567751 := by
    simpa [prefixWord, tailWord_567751, baseEnd_567751] using wordTrace_append hprefix tailTrace_567751
  have hstable : (prefixWord ++ tailWord_567751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567751).length < 2 ^ (prefixWord ++ tailWord_567751).sum := by decide
  have hdescent : baseEnd_567751 < baseStart_567751 := by decide
  rcases family_descends (prefixWord ++ tailWord_567751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567783 : List Nat := [1, 1, 5, 2, 1, 1, 3, 3, 1, 4]
def baseStart_567783 : Nat := 118140960795 + 567783 * 2 ^ 59
def prefixEnd_567783 : Nat := 4983230072969 + 3 ^ 40 * 567783 * 2
def baseEnd_567783 : Nat := 194363724301238186734213

theorem tailTrace_567783 : CollatzResearch.WordTrace tailWord_567783 prefixEnd_567783 194363724301238186734213 := by
  unfold tailWord_567783
  simp only [CollatzResearch.WordTrace]
  refine ⟨20708747302026635461364003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13805831534684423640909335 20708747302026635461364003)
  ·
    refine ⟨31063120953039953192046005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20708747302026635461364003 31063120953039953192046005)
    ·
      refine ⟨2912167589347495611754313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31063120953039953192046005 2912167589347495611754313)
      ·
        refine ⟨2184125692010621708815735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2912167589347495611754313 2184125692010621708815735)
        ·
          refine ⟨3276188538015932563223603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2184125692010621708815735 3276188538015932563223603)
          ·
            refine ⟨4914282807023898844835405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3276188538015932563223603 4914282807023898844835405)
            ·
              refine ⟨1842856052633962066813277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4914282807023898844835405 1842856052633962066813277)
              ·
                refine ⟨691071019737735775054979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1842856052633962066813277 691071019737735775054979)
                ·
                  refine ⟨1036606529606603662582469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 691071019737735775054979 1036606529606603662582469)
                  ·
                    refine ⟨194363724301238186734213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1036606529606603662582469 194363724301238186734213)
                    ·
                      rfl

theorem cell22_567783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_567783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567783 prefixEnd_567783 := by exact prefixLift 567783
  have htrace : WordTrace (prefixWord ++ tailWord_567783) baseStart_567783 baseEnd_567783 := by
    simpa [prefixWord, tailWord_567783, baseEnd_567783] using wordTrace_append hprefix tailTrace_567783
  have hstable : (prefixWord ++ tailWord_567783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567783).length < 2 ^ (prefixWord ++ tailWord_567783).sum := by decide
  have hdescent : baseEnd_567783 < baseStart_567783 := by decide
  rcases family_descends (prefixWord ++ tailWord_567783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567798 : List Nat := [5, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_567798 : Nat := 118140960795 + 567798 * 2 ^ 59
def prefixEnd_567798 : Nat := 4983230072969 + 3 ^ 40 * 567798 * 2
def baseEnd_567798 : Nat := 64789619702594382536389

theorem tailTrace_567798 : CollatzResearch.WordTrace tailWord_567798 prefixEnd_567798 64789619702594382536389 := by
  unfold tailWord_567798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1294330899810768313947503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13806196264648195348773365 1294330899810768313947503)
  ·
    refine ⟨1941496349716152470921255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1294330899810768313947503 1941496349716152470921255)
    ·
      refine ⟨2912244524574228706381883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1941496349716152470921255 2912244524574228706381883)
      ·
        refine ⟨4368366786861343059572825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2912244524574228706381883 4368366786861343059572825)
        ·
          refine ⟨3276275090146007294679619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4368366786861343059572825 3276275090146007294679619)
          ·
            refine ⟨4914412635219010942019429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3276275090146007294679619 4914412635219010942019429)
            ·
              refine ⟨921452369103564551628643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4914412635219010942019429 921452369103564551628643)
              ·
                refine ⟨1382178553655346827442965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 921452369103564551628643 1382178553655346827442965)
                ·
                  refine ⟨64789619702594382536389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1382178553655346827442965 64789619702594382536389)
                  ·
                    rfl

theorem cell22_567798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_567798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567798 prefixEnd_567798 := by exact prefixLift 567798
  have htrace : WordTrace (prefixWord ++ tailWord_567798) baseStart_567798 baseEnd_567798 := by
    simpa [prefixWord, tailWord_567798, baseEnd_567798] using wordTrace_append hprefix tailTrace_567798
  have hstable : (prefixWord ++ tailWord_567798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567798).length < 2 ^ (prefixWord ++ tailWord_567798).sum := by decide
  have hdescent : baseEnd_567798 < baseStart_567798 := by decide
  rcases family_descends (prefixWord ++ tailWord_567798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567813 : List Nat := [1, 3, 1, 1, 2, 2, 2, 5, 2, 3]
def baseStart_567813 : Nat := 118140960795 + 567813 * 2 ^ 59
def prefixEnd_567813 : Nat := 4983230072969 + 3 ^ 40 * 567813 * 2
def baseEnd_567813 : Nat := 194373993914328108484121

theorem tailTrace_567813 : CollatzResearch.WordTrace tailWord_567813 prefixEnd_567813 194373993914328108484121 := by
  unfold tailWord_567813
  simp only [CollatzResearch.WordTrace]
  refine ⟨20709841491917950584956093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13806560994611967056637395 20709841491917950584956093)
  ·
    refine ⟨7766190559469231469358535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20709841491917950584956093 7766190559469231469358535)
    ·
      refine ⟨11649285839203847204037803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7766190559469231469358535 11649285839203847204037803)
      ·
        refine ⟨17473928758805770806056705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11649285839203847204037803 17473928758805770806056705)
        ·
          refine ⟨13105446569104328104542529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17473928758805770806056705 13105446569104328104542529)
          ·
            refine ⟨9829084926828246078406897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13105446569104328104542529 9829084926828246078406897)
            ·
              refine ⟨7371813695121184558805173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9829084926828246078406897 7371813695121184558805173)
              ·
                refine ⟨691107533917611052387985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7371813695121184558805173 691107533917611052387985)
                ·
                  refine ⟨518330650438208289290989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 691107533917611052387985 518330650438208289290989)
                  ·
                    refine ⟨194373993914328108484121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 518330650438208289290989 194373993914328108484121)
                    ·
                      rfl

theorem cell22_567813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_567813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567813 prefixEnd_567813 := by exact prefixLift 567813
  have htrace : WordTrace (prefixWord ++ tailWord_567813) baseStart_567813 baseEnd_567813 := by
    simpa [prefixWord, tailWord_567813, baseEnd_567813] using wordTrace_append hprefix tailTrace_567813
  have hstable : (prefixWord ++ tailWord_567813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567813).length < 2 ^ (prefixWord ++ tailWord_567813).sum := by decide
  have hdescent : baseEnd_567813 < baseStart_567813 := by decide
  rcases family_descends (prefixWord ++ tailWord_567813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567961 : List Nat := [1, 2, 1, 2, 1, 2, 13]
def baseStart_567961 : Nat := 118140960795 + 567961 * 2 ^ 59
def prefixEnd_567961 : Nat := 4983230072969 + 3 ^ 40 * 567961 * 2
def baseEnd_567961 : Nat := 7200913234774261325321

theorem tailTrace_567961 : CollatzResearch.WordTrace tailWord_567961 prefixEnd_567961 7200913234774261325321 := by
  unfold tailWord_567961
  simp only [CollatzResearch.WordTrace]
  refine ⟨20715239495381771861343737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13810159663587847907562491 20715239495381771861343737)
  ·
    refine ⟨15536429621536328896007803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20715239495381771861343737 15536429621536328896007803)
    ·
      refine ⟨23304644432304493344011705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15536429621536328896007803 23304644432304493344011705)
      ·
        refine ⟨17478483324228370008008779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23304644432304493344011705 17478483324228370008008779)
        ·
          refine ⟨26217724986342555012013169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17478483324228370008008779 26217724986342555012013169)
          ·
            refine ⟨19663293739756916259009877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26217724986342555012013169 19663293739756916259009877)
            ·
              refine ⟨7200913234774261325321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 19663293739756916259009877 7200913234774261325321)
              ·
                rfl

theorem cell22_567961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 13].length) (baseStart_567961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567961 prefixEnd_567961 := by exact prefixLift 567961
  have htrace : WordTrace (prefixWord ++ tailWord_567961) baseStart_567961 baseEnd_567961 := by
    simpa [prefixWord, tailWord_567961, baseEnd_567961] using wordTrace_append hprefix tailTrace_567961
  have hstable : (prefixWord ++ tailWord_567961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567961).length < 2 ^ (prefixWord ++ tailWord_567961).sum := by decide
  have hdescent : baseEnd_567961 < baseStart_567961 := by decide
  rcases family_descends (prefixWord ++ tailWord_567961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567982 : List Nat := [4, 1, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_567982 : Nat := 118140960795 + 567982 * 2 ^ 59
def prefixEnd_567982 : Nat := 4983230072969 + 3 ^ 40 * 567982 * 2
def baseEnd_567982 : Nat := 194431846068068001008603

theorem tailTrace_567982 : CollatzResearch.WordTrace tailWord_567982 prefixEnd_567982 194431846068068001008603 := by
  unfold tailWord_567982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2589500678538211555982275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13810670285537128298572133 2589500678538211555982275)
  ·
    refine ⟨3884251017807317333973413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2589500678538211555982275 3884251017807317333973413)
    ·
      refine ⟨728297065838872000120015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3884251017807317333973413 728297065838872000120015)
      ·
        refine ⟨1092445598758308000180023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 728297065838872000120015 1092445598758308000180023)
        ·
          refine ⟨1638668398137462000270035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1092445598758308000180023 1638668398137462000270035)
          ·
            refine ⟨2458002597206193000405053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638668398137462000270035 2458002597206193000405053)
            ·
              refine ⟨921750973952322375151895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2458002597206193000405053 921750973952322375151895)
              ·
                refine ⟨1382626460928483562727843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 921750973952322375151895 1382626460928483562727843)
                ·
                  refine ⟨2073939691392725344091765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382626460928483562727843 2073939691392725344091765)
                  ·
                    refine ⟨194431846068068001008603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2073939691392725344091765 194431846068068001008603)
                    ·
                      rfl

theorem cell22_567982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_567982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_567982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_567982 prefixEnd_567982 := by exact prefixLift 567982
  have htrace : WordTrace (prefixWord ++ tailWord_567982) baseStart_567982 baseEnd_567982 := by
    simpa [prefixWord, tailWord_567982, baseEnd_567982] using wordTrace_append hprefix tailTrace_567982
  have hstable : (prefixWord ++ tailWord_567982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567982).length < 2 ^ (prefixWord ++ tailWord_567982).sum := by decide
  have hdescent : baseEnd_567982 < baseStart_567982 := by decide
  rcases family_descends (prefixWord ++ tailWord_567982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568001 : List Nat := [1, 2, 6, 2, 1, 2, 1, 3, 4]
def baseStart_568001 : Nat := 118140960795 + 568001 * 2 ^ 59
def prefixEnd_568001 : Nat := 4983230072969 + 3 ^ 40 * 568001 * 2
def baseEnd_568001 : Nat := 64812783385452761594515

theorem tailTrace_568001 : CollatzResearch.WordTrace tailWord_568001 prefixEnd_568001 64812783385452761594515 := by
  unfold tailWord_568001
  simp only [CollatzResearch.WordTrace]
  refine ⟨20716698415236858692799857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13811132276824572461866571 20716698415236858692799857)
  ·
    refine ⟨15537523811427644019599893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20716698415236858692799857 15537523811427644019599893)
    ·
      refine ⟨728321428660670813418745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15537523811427644019599893 728321428660670813418745)
      ·
        refine ⟨546241071495503110064059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 728321428660670813418745 546241071495503110064059)
        ·
          refine ⟨819361607243254665096089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546241071495503110064059 819361607243254665096089)
          ·
            refine ⟨614521205432440998822067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 819361607243254665096089 614521205432440998822067)
            ·
              refine ⟨921781808148661498233101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 614521205432440998822067 921781808148661498233101)
              ·
                refine ⟨345668178055748061837413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 921781808148661498233101 345668178055748061837413)
                ·
                  refine ⟨64812783385452761594515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 345668178055748061837413 64812783385452761594515)
                  ·
                    rfl

theorem cell22_568001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 4].length) (baseStart_568001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568001 prefixEnd_568001 := by exact prefixLift 568001
  have htrace : WordTrace (prefixWord ++ tailWord_568001) baseStart_568001 baseEnd_568001 := by
    simpa [prefixWord, tailWord_568001, baseEnd_568001] using wordTrace_append hprefix tailTrace_568001
  have hstable : (prefixWord ++ tailWord_568001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568001).length < 2 ^ (prefixWord ++ tailWord_568001).sum := by decide
  have hdescent : baseEnd_568001 < baseStart_568001 := by decide
  rcases family_descends (prefixWord ++ tailWord_568001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568023 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 7]
def baseStart_568023 : Nat := 118140960795 + 568023 * 2 ^ 59
def prefixEnd_568023 : Nat := 4983230072969 + 3 ^ 40 * 568023 * 2
def baseEnd_568023 : Nat := 64815293735319186911159

theorem tailTrace_568023 : CollatzResearch.WordTrace tailWord_568023 prefixEnd_568023 64815293735319186911159 := by
  unfold tailWord_568023
  simp only [CollatzResearch.WordTrace]
  refine ⟨20717500821157156450100723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13811667214104770966733815 20717500821157156450100723)
  ·
    refine ⟨31076251231735734675151085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20717500821157156450100723 31076251231735734675151085)
    ·
      refine ⟨11653594211900900503181657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31076251231735734675151085 11653594211900900503181657)
      ·
        refine ⟨8740195658925675377386243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11653594211900900503181657 8740195658925675377386243)
        ·
          refine ⟨13110293488388513066079365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8740195658925675377386243 13110293488388513066079365)
          ·
            refine ⟨2458180029072846199889881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13110293488388513066079365 2458180029072846199889881)
            ·
              refine ⟨1843635021804634649917411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2458180029072846199889881 1843635021804634649917411)
              ·
                refine ⟨2765452532706951974876117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1843635021804634649917411 2765452532706951974876117)
                ·
                  refine ⟨64815293735319186911159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2765452532706951974876117 64815293735319186911159)
                  ·
                    rfl

theorem cell22_568023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 7].length) (baseStart_568023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568023 prefixEnd_568023 := by exact prefixLift 568023
  have htrace : WordTrace (prefixWord ++ tailWord_568023) baseStart_568023 baseEnd_568023 := by
    simpa [prefixWord, tailWord_568023, baseEnd_568023] using wordTrace_append hprefix tailTrace_568023
  have hstable : (prefixWord ++ tailWord_568023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568023).length < 2 ^ (prefixWord ++ tailWord_568023).sum := by decide
  have hdescent : baseEnd_568023 < baseStart_568023 := by decide
  rcases family_descends (prefixWord ++ tailWord_568023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568083 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 3, 5]
def baseStart_568083 : Nat := 118140960795 + 568083 * 2 ^ 59
def prefixEnd_568083 : Nat := 4983230072969 + 3 ^ 40 * 568083 * 2
def baseEnd_568083 : Nat := 194466420432137404233293

theorem tailTrace_568083 : CollatzResearch.WordTrace tailWord_568083 prefixEnd_568083 194466420432137404233293 := by
  unfold tailWord_568083
  simp only [CollatzResearch.WordTrace]
  refine ⟨20719689200939786697284903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13813126133959857798189935 20719689200939786697284903)
  ·
    refine ⟨31079533801409680045927355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20719689200939786697284903 31079533801409680045927355)
    ·
      refine ⟨46619300702114520068891033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31079533801409680045927355 46619300702114520068891033)
      ·
        refine ⟨34964475526585890051668275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46619300702114520068891033 34964475526585890051668275)
        ·
          refine ⟨52446713289878835077502413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34964475526585890051668275 52446713289878835077502413)
          ·
            refine ⟨19667517483704563154063405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52446713289878835077502413 19667517483704563154063405)
            ·
              refine ⟨7375319056389211182773777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19667517483704563154063405 7375319056389211182773777)
              ·
                refine ⟨5531489292291908387080333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7375319056389211182773777 5531489292291908387080333)
                ·
                  refine ⟨2074308484609465645155125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5531489292291908387080333 2074308484609465645155125)
                  ·
                    refine ⟨194466420432137404233293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2074308484609465645155125 194466420432137404233293)
                    ·
                      rfl

theorem cell22_568083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 5].length) (baseStart_568083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568083 prefixEnd_568083 := by exact prefixLift 568083
  have htrace : WordTrace (prefixWord ++ tailWord_568083) baseStart_568083 baseEnd_568083 := by
    simpa [prefixWord, tailWord_568083, baseEnd_568083] using wordTrace_append hprefix tailTrace_568083
  have hstable : (prefixWord ++ tailWord_568083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568083).length < 2 ^ (prefixWord ++ tailWord_568083).sum := by decide
  have hdescent : baseEnd_568083 < baseStart_568083 := by decide
  rcases family_descends (prefixWord ++ tailWord_568083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568115 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 1, 6]
def baseStart_568115 : Nat := 118140960795 + 568115 * 2 ^ 59
def prefixEnd_568115 : Nat := 4983230072969 + 3 ^ 40 * 568115 * 2
def baseEnd_568115 : Nat := 194477374686099987433195

theorem tailTrace_568115 : CollatzResearch.WordTrace tailWord_568115 prefixEnd_568115 194477374686099987433195 := by
  unfold tailWord_568115
  simp only [CollatzResearch.WordTrace]
  refine ⟨20720856336823856162449799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13813904224549237441633199 20720856336823856162449799)
  ·
    refine ⟨31081284505235784243674699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20720856336823856162449799 31081284505235784243674699)
    ·
      refine ⟨46621926757853676365512049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31081284505235784243674699 46621926757853676365512049)
      ·
        refine ⟨34966445068390257274134037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46621926757853676365512049 34966445068390257274134037)
        ·
          refine ⟨1639052112580793309725033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34966445068390257274134037 1639052112580793309725033)
          ·
            refine ⟨1229289084435594982293775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1639052112580793309725033 1229289084435594982293775)
            ·
              refine ⟨1843933626653392473440663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1229289084435594982293775 1843933626653392473440663)
              ·
                refine ⟨2765900439980088710160995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1843933626653392473440663 2765900439980088710160995)
                ·
                  refine ⟨4148850659970133065241493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2765900439980088710160995 4148850659970133065241493)
                  ·
                    refine ⟨194477374686099987433195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4148850659970133065241493 194477374686099987433195)
                    ·
                      rfl

theorem cell22_568115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 6].length) (baseStart_568115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568115 prefixEnd_568115 := by exact prefixLift 568115
  have htrace : WordTrace (prefixWord ++ tailWord_568115) baseStart_568115 baseEnd_568115 := by
    simpa [prefixWord, tailWord_568115, baseEnd_568115] using wordTrace_append hprefix tailTrace_568115
  have hstable : (prefixWord ++ tailWord_568115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568115).length < 2 ^ (prefixWord ++ tailWord_568115).sum := by decide
  have hdescent : baseEnd_568115 < baseStart_568115 := by decide
  rcases family_descends (prefixWord ++ tailWord_568115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568128 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 1, 9]
def baseStart_568128 : Nat := 118140960795 + 568128 * 2 ^ 59
def prefixEnd_568128 : Nat := 4983230072969 + 3 ^ 40 * 568128 * 2
def baseEnd_568128 : Nat := 194481824851772286858155

theorem tailTrace_568128 : CollatzResearch.WordTrace tailWord_568128 prefixEnd_568128 194481824851772286858155 := by
  unfold tailWord_568128
  simp only [CollatzResearch.WordTrace]
  refine ⟨10360665242888379691336519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13814220323851172921782025 10360665242888379691336519)
  ·
    refine ⟨15540997864332569537004779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10360665242888379691336519 15540997864332569537004779)
    ·
      refine ⟨23311496796498854305507169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15540997864332569537004779 23311496796498854305507169)
      ·
        refine ⟨17483622597374140729130377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23311496796498854305507169 17483622597374140729130377)
        ·
          refine ⟨13112716948030605546847783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17483622597374140729130377 13112716948030605546847783)
          ·
            refine ⟨19669075422045908320271675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13112716948030605546847783 19669075422045908320271675)
            ·
              refine ⟨29503613133068862480407513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19669075422045908320271675 29503613133068862480407513)
              ·
                refine ⟨22127709849801646860305635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29503613133068862480407513 22127709849801646860305635)
                ·
                  refine ⟨33191564774702470290458453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22127709849801646860305635 33191564774702470290458453)
                  ·
                    refine ⟨194481824851772286858155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 33191564774702470290458453 194481824851772286858155)
                    ·
                      rfl

theorem cell22_568128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_568128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568128 prefixEnd_568128 := by exact prefixLift 568128
  have htrace : WordTrace (prefixWord ++ tailWord_568128) baseStart_568128 baseEnd_568128 := by
    simpa [prefixWord, tailWord_568128, baseEnd_568128] using wordTrace_append hprefix tailTrace_568128
  have hstable : (prefixWord ++ tailWord_568128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568128).length < 2 ^ (prefixWord ++ tailWord_568128).sum := by decide
  have hdescent : baseEnd_568128 < baseStart_568128 := by decide
  rcases family_descends (prefixWord ++ tailWord_568128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568179 : List Nat := [1, 1, 1, 2, 2, 1, 7, 3, 1, 3]
def baseStart_568179 : Nat := 118140960795 + 568179 * 2 ^ 59
def prefixEnd_568179 : Nat := 4983230072969 + 3 ^ 40 * 568179 * 2
def baseEnd_568179 : Nat := 194499283194025153832999

theorem tailTrace_568179 : CollatzResearch.WordTrace tailWord_568179 prefixEnd_568179 194499283194025153832999 := by
  unfold tailWord_568179
  simp only [CollatzResearch.WordTrace]
  refine ⟨20723190608591995092779591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13815460405727996728519727 20723190608591995092779591)
  ·
    refine ⟨31084785912887992639169387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20723190608591995092779591 31084785912887992639169387)
    ·
      refine ⟨46627178869331988958754081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31084785912887992639169387 46627178869331988958754081)
      ·
        refine ⟨34970384151998991719065561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46627178869331988958754081 34970384151998991719065561)
        ·
          refine ⟨26227788113999243789299171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34970384151998991719065561 26227788113999243789299171)
          ·
            refine ⟨39341682170998865683948757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26227788113999243789299171 39341682170998865683948757)
            ·
              refine ⟨922070675882785914467549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 39341682170998865683948757 922070675882785914467549)
              ·
                refine ⟨345776503456044717925331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 922070675882785914467549 345776503456044717925331)
                ·
                  refine ⟨518664755184067076887997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345776503456044717925331 518664755184067076887997)
                  ·
                    refine ⟨194499283194025153832999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 518664755184067076887997 194499283194025153832999)
                    ·
                      rfl

theorem cell22_568179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 1, 3].length) (baseStart_568179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568179 prefixEnd_568179 := by exact prefixLift 568179
  have htrace : WordTrace (prefixWord ++ tailWord_568179) baseStart_568179 baseEnd_568179 := by
    simpa [prefixWord, tailWord_568179, baseEnd_568179] using wordTrace_append hprefix tailTrace_568179
  have hstable : (prefixWord ++ tailWord_568179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568179).length < 2 ^ (prefixWord ++ tailWord_568179).sum := by decide
  have hdescent : baseEnd_568179 < baseStart_568179 := by decide
  rcases family_descends (prefixWord ++ tailWord_568179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568235 : List Nat := [1, 1, 1, 1, 2, 1, 1, 8, 1, 5]
def baseStart_568235 : Nat := 118140960795 + 568235 * 2 ^ 59
def prefixEnd_568235 : Nat := 4983230072969 + 3 ^ 40 * 568235 * 2
def baseEnd_568235 : Nat := 194518453138459674432827

theorem tailTrace_568235 : CollatzResearch.WordTrace tailWord_568235 prefixEnd_568235 194518453138459674432827 := by
  unfold tailWord_568235
  simp only [CollatzResearch.WordTrace]
  refine ⟨20725233096389116656818159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13816822064259411104545439 20725233096389116656818159)
  ·
    refine ⟨31087849644583674985227239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20725233096389116656818159 31087849644583674985227239)
    ·
      refine ⟨46631774466875512477840859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31087849644583674985227239 46631774466875512477840859)
      ·
        refine ⟨69947661700313268716761289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46631774466875512477840859 69947661700313268716761289)
        ·
          refine ⟨52460746275234951537570967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69947661700313268716761289 52460746275234951537570967)
          ·
            refine ⟨78691119412852427306356451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52460746275234951537570967 78691119412852427306356451)
            ·
              refine ⟨118036679119278640959534677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78691119412852427306356451 118036679119278640959534677)
              ·
                refine ⟨1383242333429046573744547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 118036679119278640959534677 1383242333429046573744547)
                ·
                  refine ⟨2074863500143569860616821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383242333429046573744547 2074863500143569860616821)
                  ·
                    refine ⟨194518453138459674432827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2074863500143569860616821 194518453138459674432827)
                    ·
                      rfl

theorem cell22_568235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 5].length) (baseStart_568235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568235 prefixEnd_568235 := by exact prefixLift 568235
  have htrace : WordTrace (prefixWord ++ tailWord_568235) baseStart_568235 baseEnd_568235 := by
    simpa [prefixWord, tailWord_568235, baseEnd_568235] using wordTrace_append hprefix tailTrace_568235
  have hstable : (prefixWord ++ tailWord_568235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568235).length < 2 ^ (prefixWord ++ tailWord_568235).sum := by decide
  have hdescent : baseEnd_568235 < baseStart_568235 := by decide
  rcases family_descends (prefixWord ++ tailWord_568235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568254 : List Nat := [4, 2, 1, 1, 1, 2, 3, 4, 4]
def baseStart_568254 : Nat := 118140960795 + 568254 * 2 ^ 59
def prefixEnd_568254 : Nat := 4983230072969 + 3 ^ 40 * 568254 * 2
def baseEnd_568254 : Nat := 64841652408916652735923

theorem tailTrace_568254 : CollatzResearch.WordTrace tailWord_568254 prefixEnd_568254 64841652408916652735923 := by
  unfold tailWord_568254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2590740760415035362719977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13817284055546855267839877 2590740760415035362719977)
  ·
    refine ⟨1943055570311276522039983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2590740760415035362719977 1943055570311276522039983)
    ·
      refine ⟨2914583355466914783059975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1943055570311276522039983 2914583355466914783059975)
      ·
        refine ⟨4371875033200372174589963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2914583355466914783059975 4371875033200372174589963)
        ·
          refine ⟨6557812549800558261884945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4371875033200372174589963 6557812549800558261884945)
          ·
            refine ⟨4918359412350418696413709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6557812549800558261884945 4918359412350418696413709)
            ·
              refine ⟨1844384779631407011155141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4918359412350418696413709 1844384779631407011155141)
              ·
                refine ⟨345822146180888814591589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1844384779631407011155141 345822146180888814591589)
                ·
                  refine ⟨64841652408916652735923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 345822146180888814591589 64841652408916652735923)
                  ·
                    rfl

theorem cell22_568254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_568254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568254 prefixEnd_568254 := by exact prefixLift 568254
  have htrace : WordTrace (prefixWord ++ tailWord_568254) baseStart_568254 baseEnd_568254 := by
    simpa [prefixWord, tailWord_568254, baseEnd_568254] using wordTrace_append hprefix tailTrace_568254
  have hstable : (prefixWord ++ tailWord_568254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568254).length < 2 ^ (prefixWord ++ tailWord_568254).sum := by decide
  have hdescent : baseEnd_568254 < baseStart_568254 := by decide
  rcases family_descends (prefixWord ++ tailWord_568254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568387 : List Nat := [1, 1, 1, 3, 1, 2, 4, 3, 1, 5]
def baseStart_568387 : Nat := 118140960795 + 568387 * 2 ^ 59
def prefixEnd_568387 : Nat := 4983230072969 + 3 ^ 40 * 568387 * 2
def baseEnd_568387 : Nat := 194570485844781944632361

theorem tailTrace_568387 : CollatzResearch.WordTrace tailWord_568387 prefixEnd_568387 194570485844781944632361 := by
  unfold tailWord_568387
  simp only [CollatzResearch.WordTrace]
  refine ⟨20730776991838446616351415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13820517994558964410900943 20730776991838446616351415)
  ·
    refine ⟨31096165487757669924527123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20730776991838446616351415 31096165487757669924527123)
    ·
      refine ⟨46644248231636504886790685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31096165487757669924527123 46644248231636504886790685)
      ·
        refine ⟨17491593086863689332546507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46644248231636504886790685 17491593086863689332546507)
        ·
          refine ⟨26237389630295533998819761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17491593086863689332546507 26237389630295533998819761)
          ·
            refine ⟨19678042222721650499114821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26237389630295533998819761 19678042222721650499114821)
            ·
              refine ⟨3689632916760309468584029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19678042222721650499114821 3689632916760309468584029)
              ·
                refine ⟨1383612343785116050719011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3689632916760309468584029 1383612343785116050719011)
                ·
                  refine ⟨2075418515677674076078517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383612343785116050719011 2075418515677674076078517)
                  ·
                    refine ⟨194570485844781944632361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2075418515677674076078517 194570485844781944632361)
                    ·
                      rfl

theorem cell22_568387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 5].length) (baseStart_568387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568387 prefixEnd_568387 := by exact prefixLift 568387
  have htrace : WordTrace (prefixWord ++ tailWord_568387) baseStart_568387 baseEnd_568387 := by
    simpa [prefixWord, tailWord_568387, baseEnd_568387] using wordTrace_append hprefix tailTrace_568387
  have hstable : (prefixWord ++ tailWord_568387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568387).length < 2 ^ (prefixWord ++ tailWord_568387).sum := by decide
  have hdescent : baseEnd_568387 < baseStart_568387 := by decide
  rcases family_descends (prefixWord ++ tailWord_568387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568391 : List Nat := [1, 1, 4, 1, 3, 4, 1, 2, 1, 4]
def baseStart_568391 : Nat := 118140960795 + 568391 * 2 ^ 59
def prefixEnd_568391 : Nat := 4983230072969 + 3 ^ 40 * 568391 * 2
def baseEnd_568391 : Nat := 194571855126527267532349

theorem tailTrace_568391 : CollatzResearch.WordTrace tailWord_568391 prefixEnd_568391 194571855126527267532349 := by
  unfold tailWord_568391
  simp only [CollatzResearch.WordTrace]
  refine ⟨20730922883823955299497027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13820615255882636866331351 20730922883823955299497027)
  ·
    refine ⟨31096384325735932949245541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20730922883823955299497027 31096384325735932949245541)
    ·
      refine ⟨5830572061075487427983539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31096384325735932949245541 5830572061075487427983539)
      ·
        refine ⟨8745858091613231141975309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5830572061075487427983539 8745858091613231141975309)
        ·
          refine ⟨3279696784354961678240741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8745858091613231141975309 3279696784354961678240741)
          ·
            refine ⟨614943147066555314670139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3279696784354961678240741 614943147066555314670139)
            ·
              refine ⟨922414720599832972005209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 614943147066555314670139 922414720599832972005209)
              ·
                refine ⟨691811040449874729003907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 922414720599832972005209 691811040449874729003907)
                ·
                  refine ⟨1037716560674812093505861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 691811040449874729003907 1037716560674812093505861)
                  ·
                    refine ⟨194571855126527267532349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1037716560674812093505861 194571855126527267532349)
                    ·
                      rfl

theorem cell22_568391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_568391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568391 prefixEnd_568391 := by exact prefixLift 568391
  have htrace : WordTrace (prefixWord ++ tailWord_568391) baseStart_568391 baseEnd_568391 := by
    simpa [prefixWord, tailWord_568391, baseEnd_568391] using wordTrace_append hprefix tailTrace_568391
  have hstable : (prefixWord ++ tailWord_568391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568391).length < 2 ^ (prefixWord ++ tailWord_568391).sum := by decide
  have hdescent : baseEnd_568391 < baseStart_568391 := by decide
  rcases family_descends (prefixWord ++ tailWord_568391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568404 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_568404 : Nat := 118140960795 + 568404 * 2 ^ 59
def prefixEnd_568404 : Nat := 4983230072969 + 3 ^ 40 * 568404 * 2
def baseEnd_568404 : Nat := 194576305292199566957309

theorem tailTrace_568404 : CollatzResearch.WordTrace tailWord_568404 prefixEnd_568404 194576305292199566957309 := by
  unfold tailWord_568404
  simp only [CollatzResearch.WordTrace]
  refine ⟨10365698516388429259860133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13820931355184572346480177 10365698516388429259860133)
  ·
    refine ⟨1943568471822830486223775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10365698516388429259860133 1943568471822830486223775)
    ·
      refine ⟨2915352707734245729335663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1943568471822830486223775 2915352707734245729335663)
      ·
        refine ⟨4373029061601368594003495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2915352707734245729335663 4373029061601368594003495)
        ·
          refine ⟨6559543592402052891005243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4373029061601368594003495 6559543592402052891005243)
          ·
            refine ⟨9839315388603079336507865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6559543592402052891005243 9839315388603079336507865)
            ·
              refine ⟨7379486541452309502380899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9839315388603079336507865 7379486541452309502380899)
              ·
                refine ⟨11069229812178464253571349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7379486541452309502380899 11069229812178464253571349)
                ·
                  refine ⟨518870147445865511886157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11069229812178464253571349 518870147445865511886157)
                  ·
                    refine ⟨194576305292199566957309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 518870147445865511886157 194576305292199566957309)
                    ·
                      rfl

theorem cell22_568404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_568404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568404 prefixEnd_568404 := by exact prefixLift 568404
  have htrace : WordTrace (prefixWord ++ tailWord_568404) baseStart_568404 baseEnd_568404 := by
    simpa [prefixWord, tailWord_568404, baseEnd_568404] using wordTrace_append hprefix tailTrace_568404
  have hstable : (prefixWord ++ tailWord_568404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568404).length < 2 ^ (prefixWord ++ tailWord_568404).sum := by decide
  have hdescent : baseEnd_568404 < baseStart_568404 := by decide
  rcases family_descends (prefixWord ++ tailWord_568404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568421 : List Nat := [1, 3, 1, 3, 2, 1, 4, 2, 2, 3]
def baseStart_568421 : Nat := 118140960795 + 568421 * 2 ^ 59
def prefixEnd_568421 : Nat := 4983230072969 + 3 ^ 40 * 568421 * 2
def baseEnd_568421 : Nat := 194582124739617189282257

theorem tailTrace_568421 : CollatzResearch.WordTrace tailWord_568421 prefixEnd_568421 194582124739617189282257 := by
  unfold tailWord_568421
  simp only [CollatzResearch.WordTrace]
  refine ⟨20732017073715270423089117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13821344715810180282059411 20732017073715270423089117)
  ·
    refine ⟨7774506402643226408658419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20732017073715270423089117 7774506402643226408658419)
    ·
      refine ⟨11661759603964839612987629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7774506402643226408658419 11661759603964839612987629)
      ·
        refine ⟨4373159851486814854870361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11661759603964839612987629 4373159851486814854870361)
        ·
          refine ⟨3279869888615111141152771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4373159851486814854870361 3279869888615111141152771)
          ·
            refine ⟨4919804832922666711729157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3279869888615111141152771 4919804832922666711729157)
            ·
              refine ⟨922463406173000008449217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4919804832922666711729157 922463406173000008449217)
              ·
                refine ⟨691847554629750006336913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 922463406173000008449217 691847554629750006336913)
                ·
                  refine ⟨518885665972312504752685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 691847554629750006336913 518885665972312504752685)
                  ·
                    refine ⟨194582124739617189282257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 518885665972312504752685 194582124739617189282257)
                    ·
                      rfl

theorem cell22_568421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_568421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568421 prefixEnd_568421 := by exact prefixLift 568421
  have htrace : WordTrace (prefixWord ++ tailWord_568421) baseStart_568421 baseEnd_568421 := by
    simpa [prefixWord, tailWord_568421, baseEnd_568421] using wordTrace_append hprefix tailTrace_568421
  have hstable : (prefixWord ++ tailWord_568421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568421).length < 2 ^ (prefixWord ++ tailWord_568421).sum := by decide
  have hdescent : baseEnd_568421 < baseStart_568421 := by decide
  rcases family_descends (prefixWord ++ tailWord_568421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568423 : List Nat := [1, 1, 5, 1, 1, 5, 2, 2, 4]
def baseStart_568423 : Nat := 118140960795 + 568423 * 2 ^ 59
def prefixEnd_568423 : Nat := 4983230072969 + 3 ^ 40 * 568423 * 2
def baseEnd_568423 : Nat := 64860936460163283577417

theorem tailTrace_568423 : CollatzResearch.WordTrace tailWord_568423 prefixEnd_568423 64860936460163283577417 := by
  unfold tailWord_568423
  simp only [CollatzResearch.WordTrace]
  refine ⟨20732090019708024764661923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13821393346472016509774615 20732090019708024764661923)
  ·
    refine ⟨31098135029562037146992885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20732090019708024764661923 31098135029562037146992885)
    ·
      refine ⟨2915450159021440982530583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31098135029562037146992885 2915450159021440982530583)
      ·
        refine ⟨4373175238532161473795875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2915450159021440982530583 4373175238532161473795875)
        ·
          refine ⟨6559762857798242210693813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4373175238532161473795875 6559762857798242210693813)
          ·
            refine ⟨614977767918585207252545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6559762857798242210693813 614977767918585207252545)
            ·
              refine ⟨461233325938938905439409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 614977767918585207252545 461233325938938905439409)
              ·
                refine ⟨345924994454204179079557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 461233325938938905439409 345924994454204179079557)
                ·
                  refine ⟨64860936460163283577417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 345924994454204179079557 64860936460163283577417)
                  ·
                    rfl

theorem cell22_568423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 4].length) (baseStart_568423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568423 prefixEnd_568423 := by exact prefixLift 568423
  have htrace : WordTrace (prefixWord ++ tailWord_568423) baseStart_568423 baseEnd_568423 := by
    simpa [prefixWord, tailWord_568423, baseEnd_568423] using wordTrace_append hprefix tailTrace_568423
  have hstable : (prefixWord ++ tailWord_568423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568423).length < 2 ^ (prefixWord ++ tailWord_568423).sum := by decide
  have hdescent : baseEnd_568423 < baseStart_568423 := by decide
  rcases family_descends (prefixWord ++ tailWord_568423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568453 : List Nat := [1, 3, 1, 1, 7, 1, 1, 1, 2, 4]
def baseStart_568453 : Nat := 118140960795 + 568453 * 2 ^ 59
def prefixEnd_568453 : Nat := 4983230072969 + 3 ^ 40 * 568453 * 2
def baseEnd_568453 : Nat := 194593078993579772482159

theorem tailTrace_568453 : CollatzResearch.WordTrace tailWord_568453 prefixEnd_568453 194593078993579772482159 := by
  unfold tailWord_568453
  simp only [CollatzResearch.WordTrace]
  refine ⟨20733184209599339888254013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13822122806399559925502675 20733184209599339888254013)
  ·
    refine ⟨7774944078599752458095255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20733184209599339888254013 7774944078599752458095255)
    ·
      refine ⟨11662416117899628687142883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7774944078599752458095255 11662416117899628687142883)
      ·
        refine ⟨17493624176849443030714325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11662416117899628687142883 17493624176849443030714325)
        ·
          refine ⟨410006816644908821032367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 17493624176849443030714325 410006816644908821032367)
          ·
            refine ⟨615010224967363231548551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410006816644908821032367 615010224967363231548551)
            ·
              refine ⟨922515337451044847322827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 615010224967363231548551 922515337451044847322827)
              ·
                refine ⟨1383773006176567270984241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922515337451044847322827 1383773006176567270984241)
                ·
                  refine ⟨1037829754632425453238181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1383773006176567270984241 1037829754632425453238181)
                  ·
                    refine ⟨194593078993579772482159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1037829754632425453238181 194593078993579772482159)
                    ·
                      rfl

theorem cell22_568453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 2, 4].length) (baseStart_568453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568453 prefixEnd_568453 := by exact prefixLift 568453
  have htrace : WordTrace (prefixWord ++ tailWord_568453) baseStart_568453 baseEnd_568453 := by
    simpa [prefixWord, tailWord_568453, baseEnd_568453] using wordTrace_append hprefix tailTrace_568453
  have hstable : (prefixWord ++ tailWord_568453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568453).length < 2 ^ (prefixWord ++ tailWord_568453).sum := by decide
  have hdescent : baseEnd_568453 < baseStart_568453 := by decide
  rcases family_descends (prefixWord ++ tailWord_568453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568492 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 2, 8]
def baseStart_568492 : Nat := 118140960795 + 568492 * 2 ^ 59
def prefixEnd_568492 : Nat := 4983230072969 + 3 ^ 40 * 568492 * 2
def baseEnd_568492 : Nat := 194606429490596670757039

theorem tailTrace_568492 : CollatzResearch.WordTrace tailWord_568492 prefixEnd_568492 194606429490596670757039 := by
  unfold tailWord_568492
  simp only [CollatzResearch.WordTrace]
  refine ⟨10367303328229024774461865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13823071104305366365949153 10367303328229024774461865)
  ·
    refine ⟨7775477496171768580846399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10367303328229024774461865 7775477496171768580846399)
    ·
      refine ⟨11663216244257652871269599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7775477496171768580846399 11663216244257652871269599)
      ·
        refine ⟨17494824366386479306904399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11663216244257652871269599 17494824366386479306904399)
        ·
          refine ⟨26242236549579718960356599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17494824366386479306904399 26242236549579718960356599)
          ·
            refine ⟨39363354824369578440534899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26242236549579718960356599 39363354824369578440534899)
            ·
              refine ⟨59045032236554367660802349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39363354824369578440534899 59045032236554367660802349)
              ·
                refine ⟨22141887088707887872800881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59045032236554367660802349 22141887088707887872800881)
                ·
                  refine ⟨16606415316530915904600661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22141887088707887872800881 16606415316530915904600661)
                  ·
                    refine ⟨194606429490596670757039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16606415316530915904600661 194606429490596670757039)
                    ·
                      rfl

theorem cell22_568492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_568492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568492 prefixEnd_568492 := by exact prefixLift 568492
  have htrace : WordTrace (prefixWord ++ tailWord_568492) baseStart_568492 baseEnd_568492 := by
    simpa [prefixWord, tailWord_568492, baseEnd_568492] using wordTrace_append hprefix tailTrace_568492
  have hstable : (prefixWord ++ tailWord_568492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568492).length < 2 ^ (prefixWord ++ tailWord_568492).sum := by decide
  have hdescent : baseEnd_568492 < baseStart_568492 := by decide
  rcases family_descends (prefixWord ++ tailWord_568492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568502 : List Nat := [5, 1, 3, 2, 2, 1, 2, 6]
def baseStart_568502 : Nat := 118140960795 + 568502 * 2 ^ 59
def prefixEnd_568502 : Nat := 4983230072969 + 3 ^ 40 * 568502 * 2
def baseEnd_568502 : Nat := 21623316966106664223001

theorem tailTrace_568502 : CollatzResearch.WordTrace tailWord_568502 prefixEnd_568502 21623316966106664223001 := by
  unfold tailWord_568502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1295935711651363828549235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13823314257614547504525173 1295935711651363828549235)
  ·
    refine ⟨1943903567477045742823853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1295935711651363828549235 1943903567477045742823853)
    ·
      refine ⟨728963837803892153558945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1943903567477045742823853 728963837803892153558945)
      ·
        refine ⟨546722878352919115169209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 728963837803892153558945 546722878352919115169209)
        ·
          refine ⟨410042158764689336376907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 546722878352919115169209 410042158764689336376907)
          ·
            refine ⟨615063238147034004565361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410042158764689336376907 615063238147034004565361)
            ·
              refine ⟨461297428610275503424021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 615063238147034004565361 461297428610275503424021)
              ·
                refine ⟨21623316966106664223001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 461297428610275503424021 21623316966106664223001)
                ·
                  rfl

theorem cell22_568502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_568502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568502 prefixEnd_568502 := by exact prefixLift 568502
  have htrace : WordTrace (prefixWord ++ tailWord_568502) baseStart_568502 baseEnd_568502 := by
    simpa [prefixWord, tailWord_568502, baseEnd_568502] using wordTrace_append hprefix tailTrace_568502
  have hstable : (prefixWord ++ tailWord_568502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568502).length < 2 ^ (prefixWord ++ tailWord_568502).sum := by decide
  have hdescent : baseEnd_568502 < baseStart_568502 := by decide
  rcases family_descends (prefixWord ++ tailWord_568502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568507 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 8]
def baseStart_568507 : Nat := 118140960795 + 568507 * 2 ^ 59
def prefixEnd_568507 : Nat := 4983230072969 + 3 ^ 40 * 568507 * 2
def baseEnd_568507 : Nat := 64870521432380543877331

theorem tailTrace_568507 : CollatzResearch.WordTrace tailWord_568507 prefixEnd_568507 64870521432380543877331 := by
  unfold tailWord_568507
  simp only [CollatzResearch.WordTrace]
  refine ⟨20735153751403707110719775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13823435834269138073813183 20735153751403707110719775)
  ·
    refine ⟨31102730627105560666079663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20735153751403707110719775 31102730627105560666079663)
    ·
      refine ⟨46654095940658340999119495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31102730627105560666079663 46654095940658340999119495)
      ·
        refine ⟨69981143910987511498679243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46654095940658340999119495 69981143910987511498679243)
        ·
          refine ⟨104971715866481267248018865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69981143910987511498679243 104971715866481267248018865)
          ·
            refine ⟨78728786899860950436014149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104971715866481267248018865 78728786899860950436014149)
            ·
              refine ⟨14761647543723928206752653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78728786899860950436014149 14761647543723928206752653)
              ·
                refine ⟨5535617828896473077532245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14761647543723928206752653 5535617828896473077532245)
                ·
                  refine ⟨64870521432380543877331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5535617828896473077532245 64870521432380543877331)
                  ·
                    rfl

theorem cell22_568507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 8].length) (baseStart_568507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568507 prefixEnd_568507 := by exact prefixLift 568507
  have htrace : WordTrace (prefixWord ++ tailWord_568507) baseStart_568507 baseEnd_568507 := by
    simpa [prefixWord, tailWord_568507, baseEnd_568507] using wordTrace_append hprefix tailTrace_568507
  have hstable : (prefixWord ++ tailWord_568507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568507).length < 2 ^ (prefixWord ++ tailWord_568507).sum := by decide
  have hdescent : baseEnd_568507 < baseStart_568507 := by decide
  rcases family_descends (prefixWord ++ tailWord_568507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568509 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_568509 : Nat := 118140960795 + 568509 * 2 ^ 59
def prefixEnd_568509 : Nat := 4983230072969 + 3 ^ 40 * 568509 * 2
def baseEnd_568509 : Nat := 194612248938014293081987

theorem tailTrace_568509 : CollatzResearch.WordTrace tailWord_568509 prefixEnd_568509 194612248938014293081987 := by
  unfold tailWord_568509
  simp only [CollatzResearch.WordTrace]
  refine ⟨20735226697396461452292581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13823484464930974301528387 20735226697396461452292581)
  ·
    refine ⟨3887855005761836522304859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20735226697396461452292581 3887855005761836522304859)
    ·
      refine ⟨5831782508642754783457289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3887855005761836522304859 5831782508642754783457289)
      ·
        refine ⟨4373836881482066087592967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5831782508642754783457289 4373836881482066087592967)
        ·
          refine ⟨6560755322223099131389451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4373836881482066087592967 6560755322223099131389451)
          ·
            refine ⟨9841132983334648697084177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6560755322223099131389451 9841132983334648697084177)
            ·
              refine ⟨7380849737500986522813133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9841132983334648697084177 7380849737500986522813133)
              ·
                refine ⟨2767818651562869946054925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7380849737500986522813133 2767818651562869946054925)
                ·
                  refine ⟨1037931994336076229770597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2767818651562869946054925 1037931994336076229770597)
                  ·
                    refine ⟨194612248938014293081987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1037931994336076229770597 194612248938014293081987)
                    ·
                      rfl

theorem cell22_568509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_568509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568509 prefixEnd_568509 := by exact prefixLift 568509
  have htrace : WordTrace (prefixWord ++ tailWord_568509) baseStart_568509 baseEnd_568509 := by
    simpa [prefixWord, tailWord_568509, baseEnd_568509] using wordTrace_append hprefix tailTrace_568509
  have hstable : (prefixWord ++ tailWord_568509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568509).length < 2 ^ (prefixWord ++ tailWord_568509).sum := by decide
  have hdescent : baseEnd_568509 < baseStart_568509 := by decide
  rcases family_descends (prefixWord ++ tailWord_568509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568534 : List Nat := [5, 2, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_568534 : Nat := 118140960795 + 568534 * 2 ^ 59
def prefixEnd_568534 : Nat := 4983230072969 + 3 ^ 40 * 568534 * 2
def baseEnd_568534 : Nat := 194620806948922561206911

theorem tailTrace_568534 : CollatzResearch.WordTrace tailWord_568534 prefixEnd_568534 194620806948922561206911 := by
  unfold tailWord_568534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1296008657644118170122041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13824092348203927147968437 1296008657644118170122041)
  ·
    refine ⟨972006493233088627591531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1296008657644118170122041 972006493233088627591531)
    ·
      refine ⟨1458009739849632941387297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 972006493233088627591531 1458009739849632941387297)
      ·
        refine ⟨1093507304887224706040473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1458009739849632941387297 1093507304887224706040473)
        ·
          refine ⟨820130478665418529530355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1093507304887224706040473 820130478665418529530355)
          ·
            refine ⟨1230195717998127794295533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 820130478665418529530355 1230195717998127794295533)
            ·
              refine ⟨461323394249297922860825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1230195717998127794295533 461323394249297922860825)
              ·
                refine ⟨345992545686973442145619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 461323394249297922860825 345992545686973442145619)
                ·
                  refine ⟨518988818530460163218429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345992545686973442145619 518988818530460163218429)
                  ·
                    refine ⟨194620806948922561206911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 518988818530460163218429 194620806948922561206911)
                    ·
                      rfl

theorem cell22_568534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_568534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568534 prefixEnd_568534 := by exact prefixLift 568534
  have htrace : WordTrace (prefixWord ++ tailWord_568534) baseStart_568534 baseEnd_568534 := by
    simpa [prefixWord, tailWord_568534, baseEnd_568534] using wordTrace_append hprefix tailTrace_568534
  have hstable : (prefixWord ++ tailWord_568534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568534).length < 2 ^ (prefixWord ++ tailWord_568534).sum := by decide
  have hdescent : baseEnd_568534 < baseStart_568534 := by decide
  rcases family_descends (prefixWord ++ tailWord_568534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568539 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 8, 3]
def baseStart_568539 : Nat := 118140960795 + 568539 * 2 ^ 59
def prefixEnd_568539 : Nat := 4983230072969 + 3 ^ 40 * 568539 * 2
def baseEnd_568539 : Nat := 194622518551104214831895

theorem tailTrace_568539 : CollatzResearch.WordTrace tailWord_568539 prefixEnd_568539 194622518551104214831895 := by
  unfold tailWord_568539
  simp only [CollatzResearch.WordTrace]
  refine ⟨20736320887287776575884671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13824213924858517717256447 20736320887287776575884671)
  ·
    refine ⟨31104481330931664863827007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20736320887287776575884671 31104481330931664863827007)
    ·
      refine ⟨46656721996397497295740511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31104481330931664863827007 46656721996397497295740511)
      ·
        refine ⟨69985082994596245943610767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46656721996397497295740511 69985082994596245943610767)
        ·
          refine ⟨104977624491894368915416151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69985082994596245943610767 104977624491894368915416151)
          ·
            refine ⟨157466436737841553373124227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104977624491894368915416151 157466436737841553373124227)
            ·
              refine ⟨236199655106762330059686341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157466436737841553373124227 236199655106762330059686341)
              ·
                refine ⟨44287435332517936886191189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 236199655106762330059686341 44287435332517936886191189)
                ·
                  refine ⟨518993382802944572885053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 44287435332517936886191189 518993382802944572885053)
                  ·
                    refine ⟨194622518551104214831895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 518993382802944572885053 194622518551104214831895)
                    ·
                      rfl

theorem cell22_568539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 3].length) (baseStart_568539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568539 prefixEnd_568539 := by exact prefixLift 568539
  have htrace : WordTrace (prefixWord ++ tailWord_568539) baseStart_568539 baseEnd_568539 := by
    simpa [prefixWord, tailWord_568539, baseEnd_568539] using wordTrace_append hprefix tailTrace_568539
  have hstable : (prefixWord ++ tailWord_568539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568539).length < 2 ^ (prefixWord ++ tailWord_568539).sum := by decide
  have hdescent : baseEnd_568539 < baseStart_568539 := by decide
  rcases family_descends (prefixWord ++ tailWord_568539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568599 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 1, 8]
def baseStart_568599 : Nat := 118140960795 + 568599 * 2 ^ 59
def prefixEnd_568599 : Nat := 4983230072969 + 3 ^ 40 * 568599 * 2
def baseEnd_568599 : Nat := 194643057777284058331711

theorem tailTrace_568599 : CollatzResearch.WordTrace tailWord_568599 prefixEnd_568599 194643057777284058331711 := by
  unfold tailWord_568599
  simp only [CollatzResearch.WordTrace]
  refine ⟨20738509267070406823068851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13825672844713604548712567 20738509267070406823068851)
  ·
    refine ⟨31107763900605610234603277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20738509267070406823068851 31107763900605610234603277)
    ·
      refine ⟨11665411462727103837976229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31107763900605610234603277 11665411462727103837976229)
      ·
        refine ⟨2187264649261331969620543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11665411462727103837976229 2187264649261331969620543)
        ·
          refine ⟨3280896973891997954430815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2187264649261331969620543 3280896973891997954430815)
          ·
            refine ⟨4921345460837996931646223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3280896973891997954430815 4921345460837996931646223)
            ·
              refine ⟨7382018191256995397469335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4921345460837996931646223 7382018191256995397469335)
              ·
                refine ⟨11073027286885493096204003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7382018191256995397469335 11073027286885493096204003)
                ·
                  refine ⟨16609540930328239644306005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11073027286885493096204003 16609540930328239644306005)
                  ·
                    refine ⟨194643057777284058331711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16609540930328239644306005 194643057777284058331711)
                    ·
                      rfl

theorem cell22_568599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_568599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568599 prefixEnd_568599 := by exact prefixLift 568599
  have htrace : WordTrace (prefixWord ++ tailWord_568599) baseStart_568599 baseEnd_568599 := by
    simpa [prefixWord, tailWord_568599, baseEnd_568599] using wordTrace_append hprefix tailTrace_568599
  have hstable : (prefixWord ++ tailWord_568599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568599).length < 2 ^ (prefixWord ++ tailWord_568599).sum := by decide
  have hdescent : baseEnd_568599 < baseStart_568599 := by decide
  rcases family_descends (prefixWord ++ tailWord_568599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568618 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 5, 3]
def baseStart_568618 : Nat := 118140960795 + 568618 * 2 ^ 59
def prefixEnd_568618 : Nat := 4983230072969 + 3 ^ 40 * 568618 * 2
def baseEnd_568618 : Nat := 194649561865574342106653

theorem tailTrace_568618 : CollatzResearch.WordTrace tailWord_568618 prefixEnd_568618 194649561865574342106653 := by
  unfold tailWord_568618
  simp only [CollatzResearch.WordTrace]
  refine ⟨5184800563500393267002627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13826134836001048712007005 5184800563500393267002627)
  ·
    refine ⟨7777200845250589900503941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5184800563500393267002627 7777200845250589900503941)
    ·
      refine ⟨1458225158484485606344489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7777200845250589900503941 1458225158484485606344489)
      ·
        refine ⟨1093668868863364204758367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1458225158484485606344489 1093668868863364204758367)
        ·
          refine ⟨1640503303295046307137551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1093668868863364204758367 1640503303295046307137551)
          ·
            refine ⟨2460754954942569460706327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1640503303295046307137551 2460754954942569460706327)
            ·
              refine ⟨3691132432413854191059491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2460754954942569460706327 3691132432413854191059491)
              ·
                refine ⟨5536698648620781286589237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3691132432413854191059491 5536698648620781286589237)
                ·
                  refine ⟨519065498308198245617741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5536698648620781286589237 519065498308198245617741)
                  ·
                    refine ⟨194649561865574342106653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 519065498308198245617741 194649561865574342106653)
                    ·
                      rfl

theorem cell22_568618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_568618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568618 prefixEnd_568618 := by exact prefixLift 568618
  have htrace : WordTrace (prefixWord ++ tailWord_568618) baseStart_568618 baseEnd_568618 := by
    simpa [prefixWord, tailWord_568618, baseEnd_568618] using wordTrace_append hprefix tailTrace_568618
  have hstable : (prefixWord ++ tailWord_568618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568618).length < 2 ^ (prefixWord ++ tailWord_568618).sum := by decide
  have hdescent : baseEnd_568618 < baseStart_568618 := by decide
  rcases family_descends (prefixWord ++ tailWord_568618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568676 : List Nat := [2, 3, 1, 1, 3, 2, 2, 2, 6]
def baseStart_568676 : Nat := 118140960795 + 568676 * 2 ^ 59
def prefixEnd_568676 : Nat := 4983230072969 + 3 ^ 40 * 568676 * 2
def baseEnd_568676 : Nat := 64889805483627174718825

theorem tailTrace_568676 : CollatzResearch.WordTrace tailWord_568676 prefixEnd_568676 64889805483627174718825 := by
  unfold tailWord_568676
  simp only [CollatzResearch.WordTrace]
  refine ⟨10370658843895724486810941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13827545125194299315747921 10370658843895724486810941)
  ·
    refine ⟨3888997066460896682554103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10370658843895724486810941 3888997066460896682554103)
    ·
      refine ⟨5833495599691345023831155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3888997066460896682554103 5833495599691345023831155)
      ·
        refine ⟨8750243399537017535746733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5833495599691345023831155 8750243399537017535746733)
        ·
          refine ⟨3281341274826381575905025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8750243399537017535746733 3281341274826381575905025)
          ·
            refine ⟨2461005956119786181928769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3281341274826381575905025 2461005956119786181928769)
            ·
              refine ⟨1845754467089839636446577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2461005956119786181928769 1845754467089839636446577)
              ·
                refine ⟨1384315850317379727334933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1845754467089839636446577 1384315850317379727334933)
                ·
                  refine ⟨64889805483627174718825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1384315850317379727334933 64889805483627174718825)
                  ·
                    rfl

theorem cell22_568676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_568676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568676 prefixEnd_568676 := by exact prefixLift 568676
  have htrace : WordTrace (prefixWord ++ tailWord_568676) baseStart_568676 baseEnd_568676 := by
    simpa [prefixWord, tailWord_568676, baseEnd_568676] using wordTrace_append hprefix tailTrace_568676
  have hstable : (prefixWord ++ tailWord_568676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568676).length < 2 ^ (prefixWord ++ tailWord_568676).sum := by decide
  have hdescent : baseEnd_568676 < baseStart_568676 := by decide
  rcases family_descends (prefixWord ++ tailWord_568676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568686 : List Nat := [4, 1, 2, 4, 2, 1, 1, 3, 1, 3]
def baseStart_568686 : Nat := 118140960795 + 568686 * 2 ^ 59
def prefixEnd_568686 : Nat := 4983230072969 + 3 ^ 40 * 568686 * 2
def baseEnd_568686 : Nat := 194672839655244831406445

theorem tailTrace_568686 : CollatzResearch.WordTrace tailWord_568686 prefixEnd_568686 194672839655244831406445 := by
  unfold tailWord_568686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2592710302219402585185739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13827788278503480454323941 2592710302219402585185739)
  ·
    refine ⟨3889065453329103877778609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2592710302219402585185739 3889065453329103877778609)
    ·
      refine ⟨2916799089996827908333957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3889065453329103877778609 2916799089996827908333957)
      ·
        refine ⟨546899829374405232812617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2916799089996827908333957 546899829374405232812617)
        ·
          refine ⟨410174872030803924609463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 546899829374405232812617 410174872030803924609463)
          ·
            refine ⟨615262308046205886914195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410174872030803924609463 615262308046205886914195)
            ·
              refine ⟨922893462069308830371293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 615262308046205886914195 922893462069308830371293)
              ·
                refine ⟨346085048275990811389235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 922893462069308830371293 346085048275990811389235)
                ·
                  refine ⟨519127572413986217083853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 346085048275990811389235 519127572413986217083853)
                  ·
                    refine ⟨194672839655244831406445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 519127572413986217083853 194672839655244831406445)
                    ·
                      rfl

theorem cell22_568686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_568686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568686 prefixEnd_568686 := by exact prefixLift 568686
  have htrace : WordTrace (prefixWord ++ tailWord_568686) baseStart_568686 baseEnd_568686 := by
    simpa [prefixWord, tailWord_568686, baseEnd_568686] using wordTrace_append hprefix tailTrace_568686
  have hstable : (prefixWord ++ tailWord_568686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568686).length < 2 ^ (prefixWord ++ tailWord_568686).sum := by decide
  have hdescent : baseEnd_568686 < baseStart_568686 := by decide
  rcases family_descends (prefixWord ++ tailWord_568686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568708 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 4, 3]
def baseStart_568708 : Nat := 118140960795 + 568708 * 2 ^ 59
def prefixEnd_568708 : Nat := 4983230072969 + 3 ^ 40 * 568708 * 2
def baseEnd_568708 : Nat := 194680370704844107356377

theorem tailTrace_568708 : CollatzResearch.WordTrace tailWord_568708 prefixEnd_568708 194680370704844107356377 := by
  unfold tailWord_568708
  simp only [CollatzResearch.WordTrace]
  refine ⟨10371242411837759219393389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13828323215783678959191185 10371242411837759219393389)
  ·
    refine ⟨3889215904439159707272521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10371242411837759219393389 3889215904439159707272521)
    ·
      refine ⟨2916911928329369780454391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3889215904439159707272521 2916911928329369780454391)
      ·
        refine ⟨4375367892494054670681587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2916911928329369780454391 4375367892494054670681587)
        ·
          refine ⟨6563051838741082006022381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4375367892494054670681587 6563051838741082006022381)
          ·
            refine ⟨2461144439527905752258393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6563051838741082006022381 2461144439527905752258393)
            ·
              refine ⟨1845858329645929314193795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2461144439527905752258393 1845858329645929314193795)
              ·
                refine ⟨2768787494468893971290693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1845858329645929314193795 2768787494468893971290693)
                ·
                  refine ⟨519147655212917619617005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2768787494468893971290693 519147655212917619617005)
                  ·
                    refine ⟨194680370704844107356377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 519147655212917619617005 194680370704844107356377)
                    ·
                      rfl

theorem cell22_568708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_568708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568708 prefixEnd_568708 := by exact prefixLift 568708
  have htrace : WordTrace (prefixWord ++ tailWord_568708) baseStart_568708 baseEnd_568708 := by
    simpa [prefixWord, tailWord_568708, baseEnd_568708] using wordTrace_append hprefix tailTrace_568708
  have hstable : (prefixWord ++ tailWord_568708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568708).length < 2 ^ (prefixWord ++ tailWord_568708).sum := by decide
  have hdescent : baseEnd_568708 < baseStart_568708 := by decide
  rcases family_descends (prefixWord ++ tailWord_568708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568725 : List Nat := [1, 3, 2, 1, 1, 2, 6, 1, 2, 3]
def baseStart_568725 : Nat := 118140960795 + 568725 * 2 ^ 59
def prefixEnd_568725 : Nat := 4983230072969 + 3 ^ 40 * 568725 * 2
def baseEnd_568725 : Nat := 194686190152261729681325

theorem tailTrace_568725 : CollatzResearch.WordTrace tailWord_568725 prefixEnd_568725 194686190152261729681325 := by
  unfold tailWord_568725
  simp only [CollatzResearch.WordTrace]
  refine ⟨20743104864613930342155629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13828736576409286894770419 20743104864613930342155629)
  ·
    refine ⟨7778664324230223878308361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20743104864613930342155629 7778664324230223878308361)
    ·
      refine ⟨5833998243172667908731271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7778664324230223878308361 5833998243172667908731271)
      ·
        refine ⟨8750997364759001863096907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5833998243172667908731271 8750997364759001863096907)
        ·
          refine ⟨13126496047138502794645361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8750997364759001863096907 13126496047138502794645361)
          ·
            refine ⟨9844872035353877095984021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13126496047138502794645361 9844872035353877095984021)
            ·
              refine ⟨461478376657212988874251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9844872035353877095984021 461478376657212988874251)
              ·
                refine ⟨692217564985819483311377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461478376657212988874251 692217564985819483311377)
                ·
                  refine ⟨519163173739364612483533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 692217564985819483311377 519163173739364612483533)
                  ·
                    refine ⟨194686190152261729681325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 519163173739364612483533 194686190152261729681325)
                    ·
                      rfl

theorem cell22_568725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_568725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568725 prefixEnd_568725 := by exact prefixLift 568725
  have htrace : WordTrace (prefixWord ++ tailWord_568725) baseStart_568725 baseEnd_568725 := by
    simpa [prefixWord, tailWord_568725, baseEnd_568725] using wordTrace_append hprefix tailTrace_568725
  have hstable : (prefixWord ++ tailWord_568725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568725).length < 2 ^ (prefixWord ++ tailWord_568725).sum := by decide
  have hdescent : baseEnd_568725 < baseStart_568725 := by decide
  rcases family_descends (prefixWord ++ tailWord_568725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568841 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 3, 6]
def baseStart_568841 : Nat := 118140960795 + 568841 * 2 ^ 59
def prefixEnd_568841 : Nat := 4983230072969 + 3 ^ 40 * 568841 * 2
def baseEnd_568841 : Nat := 194725899322876093780969

theorem tailTrace_568841 : CollatzResearch.WordTrace tailWord_568841 prefixEnd_568841 194725899322876093780969 := by
  unfold tailWord_568841
  simp only [CollatzResearch.WordTrace]
  refine ⟨20747335732193682153378377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13831557154795788102252251 20747335732193682153378377)
  ·
    refine ⟨15560501799145261615033783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20747335732193682153378377 15560501799145261615033783)
    ·
      refine ⟨23340752698717892422550675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15560501799145261615033783 23340752698717892422550675)
      ·
        refine ⟨35011129048076838633826013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23340752698717892422550675 35011129048076838633826013)
        ·
          refine ⟨13129173393028814487684755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35011129048076838633826013 13129173393028814487684755)
          ·
            refine ⟨19693760089543221731527133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13129173393028814487684755 19693760089543221731527133)
            ·
              refine ⟨7385160033578708149322675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19693760089543221731527133 7385160033578708149322675)
              ·
                refine ⟨11077740050368062223984013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7385160033578708149322675 11077740050368062223984013)
                ·
                  refine ⟨4154152518888023333994005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11077740050368062223984013 4154152518888023333994005)
                  ·
                    refine ⟨194725899322876093780969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4154152518888023333994005 194725899322876093780969)
                    ·
                      rfl

theorem cell22_568841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_568841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568841 prefixEnd_568841 := by exact prefixLift 568841
  have htrace : WordTrace (prefixWord ++ tailWord_568841) baseStart_568841 baseEnd_568841 := by
    simpa [prefixWord, tailWord_568841, baseEnd_568841] using wordTrace_append hprefix tailTrace_568841
  have hstable : (prefixWord ++ tailWord_568841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568841).length < 2 ^ (prefixWord ++ tailWord_568841).sum := by decide
  have hdescent : baseEnd_568841 < baseStart_568841 := by decide
  rcases family_descends (prefixWord ++ tailWord_568841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568858 : List Nat := [3, 1, 1, 3, 1, 1, 1, 5, 2, 4]
def baseStart_568858 : Nat := 118140960795 + 568858 * 2 ^ 59
def prefixEnd_568858 : Nat := 4983230072969 + 3 ^ 40 * 568858 * 2
def baseEnd_568858 : Nat := 194731718770293716105917

theorem tailTrace_568858 : CollatzResearch.WordTrace tailWord_568858 prefixEnd_568858 194731718770293716105917 := by
  unfold tailWord_568858
  simp only [CollatzResearch.WordTrace]
  refine ⟨5186988943283023514186807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13831970515421396037831485 5186988943283023514186807)
  ·
    refine ⟨7780483414924535271280211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5186988943283023514186807 7780483414924535271280211)
    ·
      refine ⟨11670725122386802906920317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7780483414924535271280211 11670725122386802906920317)
      ·
        refine ⟨4376521920895051090095119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11670725122386802906920317 4376521920895051090095119)
        ·
          refine ⟨6564782881342576635142679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4376521920895051090095119 6564782881342576635142679)
          ·
            refine ⟨9847174322013864952714019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6564782881342576635142679 9847174322013864952714019)
            ·
              refine ⟨14770761483020797429071029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9847174322013864952714019 14770761483020797429071029)
              ·
                refine ⟨1384758889033199758975409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14770761483020797429071029 1384758889033199758975409)
                ·
                  refine ⟨1038569166774899819231557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1384758889033199758975409 1038569166774899819231557)
                  ·
                    refine ⟨194731718770293716105917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1038569166774899819231557 194731718770293716105917)
                    ·
                      rfl

theorem cell22_568858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_568858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568858 prefixEnd_568858 := by exact prefixLift 568858
  have htrace : WordTrace (prefixWord ++ tailWord_568858) baseStart_568858 baseEnd_568858 := by
    simpa [prefixWord, tailWord_568858, baseEnd_568858] using wordTrace_append hprefix tailTrace_568858
  have hstable : (prefixWord ++ tailWord_568858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568858).length < 2 ^ (prefixWord ++ tailWord_568858).sum := by decide
  have hdescent : baseEnd_568858 < baseStart_568858 := by decide
  rcases family_descends (prefixWord ++ tailWord_568858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568950 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_568950 : Nat := 118140960795 + 568950 * 2 ^ 59
def prefixEnd_568950 : Nat := 4983230072969 + 3 ^ 40 * 568950 * 2
def baseEnd_568950 : Nat := 194763212250436142805635

theorem tailTrace_568950 : CollatzResearch.WordTrace tailWord_568950 prefixEnd_568950 194763212250436142805635 := by
  unfold tailWord_568950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1296956955549924610568519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13834207525865862512730869 1296956955549924610568519)
  ·
    refine ⟨1945435433324886915852779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1296956955549924610568519 1945435433324886915852779)
    ·
      refine ⟨2918153149987330373779169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1945435433324886915852779 2918153149987330373779169)
      ·
        refine ⟨2188614862490497780334377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2918153149987330373779169 2188614862490497780334377)
        ·
          refine ⟨1641461146867873335250783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2188614862490497780334377 1641461146867873335250783)
          ·
            refine ⟨2462191720301810002876175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1641461146867873335250783 2462191720301810002876175)
            ·
              refine ⟨3693287580452715004314263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2462191720301810002876175 3693287580452715004314263)
              ·
                refine ⟨5539931370679072506471395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3693287580452715004314263 5539931370679072506471395)
                ·
                  refine ⟨8309897056018608759707093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5539931370679072506471395 8309897056018608759707093)
                  ·
                    refine ⟨194763212250436142805635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8309897056018608759707093 194763212250436142805635)
                    ·
                      rfl

theorem cell22_568950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_568950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568950 prefixEnd_568950 := by exact prefixLift 568950
  have htrace : WordTrace (prefixWord ++ tailWord_568950) baseStart_568950 baseEnd_568950 := by
    simpa [prefixWord, tailWord_568950, baseEnd_568950] using wordTrace_append hprefix tailTrace_568950
  have hstable : (prefixWord ++ tailWord_568950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568950).length < 2 ^ (prefixWord ++ tailWord_568950).sum := by decide
  have hdescent : baseEnd_568950 < baseStart_568950 := by decide
  rcases family_descends (prefixWord ++ tailWord_568950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568965 : List Nat := [1, 3, 1, 1, 4, 1, 2, 4, 1, 4]
def baseStart_568965 : Nat := 118140960795 + 568965 * 2 ^ 59
def prefixEnd_568965 : Nat := 4983230072969 + 3 ^ 40 * 568965 * 2
def baseEnd_568965 : Nat := 194768347056981103680589

theorem tailTrace_568965 : CollatzResearch.WordTrace tailWord_568965 prefixEnd_568965 194768347056981103680589 := by
  unfold tailWord_568965
  simp only [CollatzResearch.WordTrace]
  refine ⟨20751858383744451330892349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13834572255829634220594899 20751858383744451330892349)
  ·
    refine ⟨7781946893904169249084631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20751858383744451330892349 7781946893904169249084631)
    ·
      refine ⟨11672920340856253873626947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7781946893904169249084631 11672920340856253873626947)
      ·
        refine ⟨17509380511284380810440421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11672920340856253873626947 17509380511284380810440421)
        ·
          refine ⟨3283008845865821401957579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17509380511284380810440421 3283008845865821401957579)
          ·
            refine ⟨4924513268798732102936369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3283008845865821401957579 4924513268798732102936369)
            ·
              refine ⟨3693384951599049077202277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4924513268798732102936369 3693384951599049077202277)
              ·
                refine ⟨692509678424821701975427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3693384951599049077202277 692509678424821701975427)
                ·
                  refine ⟨1038764517637232552963141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692509678424821701975427 1038764517637232552963141)
                  ·
                    refine ⟨194768347056981103680589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1038764517637232552963141 194768347056981103680589)
                    ·
                      rfl

theorem cell22_568965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_568965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568965 prefixEnd_568965 := by exact prefixLift 568965
  have htrace : WordTrace (prefixWord ++ tailWord_568965) baseStart_568965 baseEnd_568965 := by
    simpa [prefixWord, tailWord_568965, baseEnd_568965] using wordTrace_append hprefix tailTrace_568965
  have hstable : (prefixWord ++ tailWord_568965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568965).length < 2 ^ (prefixWord ++ tailWord_568965).sum := by decide
  have hdescent : baseEnd_568965 < baseStart_568965 := by decide
  rcases family_descends (prefixWord ++ tailWord_568965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568995 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 4, 3]
def baseStart_568995 : Nat := 118140960795 + 568995 * 2 ^ 59
def prefixEnd_568995 : Nat := 4983230072969 + 3 ^ 40 * 568995 * 2
def baseEnd_568995 : Nat := 194778616670071025430497

theorem tailTrace_568995 : CollatzResearch.WordTrace tailWord_568995 prefixEnd_568995 194778616670071025430497 := by
  unfold tailWord_568995
  simp only [CollatzResearch.WordTrace]
  refine ⟨20752952573635766454484439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13835301715757177636322959 20752952573635766454484439)
  ·
    refine ⟨31129428860453649681726659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20752952573635766454484439 31129428860453649681726659)
    ·
      refine ⟨46694143290680474522589989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31129428860453649681726659 46694143290680474522589989)
      ·
        refine ⟨8755151867002588972985623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46694143290680474522589989 8755151867002588972985623)
        ·
          refine ⟨13132727800503883459478435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8755151867002588972985623 13132727800503883459478435)
          ·
            refine ⟨19699091700755825189217653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13132727800503883459478435 19699091700755825189217653)
            ·
              refine ⟨1846789846945858611489155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19699091700755825189217653 1846789846945858611489155)
              ·
                refine ⟨2770184770418787917233733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1846789846945858611489155 2770184770418787917233733)
                ·
                  refine ⟨519409644453522734481325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2770184770418787917233733 519409644453522734481325)
                  ·
                    refine ⟨194778616670071025430497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 519409644453522734481325 194778616670071025430497)
                    ·
                      rfl

theorem cell22_568995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 3].length) (baseStart_568995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_568995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_568995 prefixEnd_568995 := by exact prefixLift 568995
  have htrace : WordTrace (prefixWord ++ tailWord_568995) baseStart_568995 baseEnd_568995 := by
    simpa [prefixWord, tailWord_568995, baseEnd_568995] using wordTrace_append hprefix tailTrace_568995
  have hstable : (prefixWord ++ tailWord_568995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568995).length < 2 ^ (prefixWord ++ tailWord_568995).sum := by decide
  have hdescent : baseEnd_568995 < baseStart_568995 := by decide
  rcases family_descends (prefixWord ++ tailWord_568995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569023 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 2, 7]
def baseStart_569023 : Nat := 118140960795 + 569023 * 2 ^ 59
def prefixEnd_569023 : Nat := 4983230072969 + 3 ^ 40 * 569023 * 2
def baseEnd_569023 : Nat := 194788201642288285730411

theorem tailTrace_569023 : CollatzResearch.WordTrace tailWord_569023 prefixEnd_569023 194788201642288285730411 := by
  unfold tailWord_569023
  simp only [CollatzResearch.WordTrace]
  refine ⟨20753973817534327236503723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13835982545022884824335815 20753973817534327236503723)
  ·
    refine ⟨31130960726301490854755585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20753973817534327236503723 31130960726301490854755585)
    ·
      refine ⟨23348220544726118141066689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31130960726301490854755585 23348220544726118141066689)
      ·
        refine ⟨17511165408544588605800017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23348220544726118141066689 17511165408544588605800017)
        ·
          refine ⟨13133374056408441454350013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17511165408544588605800017 13133374056408441454350013)
          ·
            refine ⟨4925015271153165545381255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13133374056408441454350013 4925015271153165545381255)
            ·
              refine ⟨7387522906729748318071883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4925015271153165545381255 7387522906729748318071883)
              ·
                refine ⟨11081284360094622477107825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7387522906729748318071883 11081284360094622477107825)
                ·
                  refine ⟨8310963270070966857830869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11081284360094622477107825 8310963270070966857830869)
                  ·
                    refine ⟨194788201642288285730411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8310963270070966857830869 194788201642288285730411)
                    ·
                      rfl

theorem cell22_569023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_569023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569023 prefixEnd_569023 := by exact prefixLift 569023
  have htrace : WordTrace (prefixWord ++ tailWord_569023) baseStart_569023 baseEnd_569023 := by
    simpa [prefixWord, tailWord_569023, baseEnd_569023] using wordTrace_append hprefix tailTrace_569023
  have hstable : (prefixWord ++ tailWord_569023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569023).length < 2 ^ (prefixWord ++ tailWord_569023).sum := by decide
  have hdescent : baseEnd_569023 < baseStart_569023 := by decide
  rcases family_descends (prefixWord ++ tailWord_569023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569063 : List Nat := [1, 1, 5, 4, 1, 2, 2, 1, 2, 3]
def baseStart_569063 : Nat := 118140960795 + 569063 * 2 ^ 59
def prefixEnd_569063 : Nat := 4983230072969 + 3 ^ 40 * 569063 * 2
def baseEnd_569063 : Nat := 194801894459741514730289

theorem tailTrace_569063 : CollatzResearch.WordTrace tailWord_569063 prefixEnd_569063 194801894459741514730289 := by
  unfold tailWord_569063
  simp only [CollatzResearch.WordTrace]
  refine ⟨20755432737389414067959843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13836955158259609378639895 20755432737389414067959843)
  ·
    refine ⟨31133149106084121101939765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20755432737389414067959843 31133149106084121101939765)
    ·
      refine ⟨2918732728695386353306853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31133149106084121101939765 2918732728695386353306853)
      ·
        refine ⟨547262386630384941245035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2918732728695386353306853 547262386630384941245035)
        ·
          refine ⟨820893579945577411867553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547262386630384941245035 820893579945577411867553)
          ·
            refine ⟨615670184959183058900665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 820893579945577411867553 615670184959183058900665)
            ·
              refine ⟨461752638719387294175499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 615670184959183058900665 461752638719387294175499)
              ·
                refine ⟨692628958079080941263249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461752638719387294175499 692628958079080941263249)
                ·
                  refine ⟨519471718559310705947437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 692628958079080941263249 519471718559310705947437)
                  ·
                    refine ⟨194801894459741514730289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 519471718559310705947437 194801894459741514730289)
                    ·
                      rfl

theorem cell22_569063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_569063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569063 prefixEnd_569063 := by exact prefixLift 569063
  have htrace : WordTrace (prefixWord ++ tailWord_569063) baseStart_569063 baseEnd_569063 := by
    simpa [prefixWord, tailWord_569063, baseEnd_569063] using wordTrace_append hprefix tailTrace_569063
  have hstable : (prefixWord ++ tailWord_569063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569063).length < 2 ^ (prefixWord ++ tailWord_569063).sum := by decide
  have hdescent : baseEnd_569063 < baseStart_569063 := by decide
  rcases family_descends (prefixWord ++ tailWord_569063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569149 : List Nat := [1, 4, 1, 4, 1, 1, 1, 5, 4]
def baseStart_569149 : Nat := 118140960795 + 569149 * 2 ^ 59
def prefixEnd_569149 : Nat := 4983230072969 + 3 ^ 40 * 569149 * 2
def baseEnd_569149 : Nat := 64943778005755319026675

theorem tailTrace_569149 : CollatzResearch.WordTrace tailWord_569149 prefixEnd_569149 64943778005755319026675 := by
  unfold tailWord_569149
  simp only [CollatzResearch.WordTrace]
  refine ⟨20758569415077850755590501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13839046276718567170393667 20758569415077850755590501)
  ·
    refine ⟨3892231765327097016673219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20758569415077850755590501 3892231765327097016673219)
    ·
      refine ⟨5838347647990645525009829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3892231765327097016673219 5838347647990645525009829)
      ·
        refine ⟨1094690183998246035939343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5838347647990645525009829 1094690183998246035939343)
        ·
          refine ⟨1642035275997369053909015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1094690183998246035939343 1642035275997369053909015)
          ·
            refine ⟨2463052913996053580863523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1642035275997369053909015 2463052913996053580863523)
            ·
              refine ⟨3694579370994080371295285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2463052913996053580863523 3694579370994080371295285)
              ·
                refine ⟨346366816030695034808933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3694579370994080371295285 346366816030695034808933)
                ·
                  refine ⟨64943778005755319026675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 346366816030695034808933 64943778005755319026675)
                  ·
                    rfl

theorem cell22_569149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_569149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569149 prefixEnd_569149 := by exact prefixLift 569149
  have htrace : WordTrace (prefixWord ++ tailWord_569149) baseStart_569149 baseEnd_569149 := by
    simpa [prefixWord, tailWord_569149, baseEnd_569149] using wordTrace_append hprefix tailTrace_569149
  have hstable : (prefixWord ++ tailWord_569149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569149).length < 2 ^ (prefixWord ++ tailWord_569149).sum := by decide
  have hdescent : baseEnd_569149 < baseStart_569149 := by decide
  rcases family_descends (prefixWord ++ tailWord_569149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569151 : List Nat := [1, 1, 2, 2, 6, 2, 2, 1, 1, 4]
def baseStart_569151 : Nat := 118140960795 + 569151 * 2 ^ 59
def prefixEnd_569151 : Nat := 4983230072969 + 3 ^ 40 * 569151 * 2
def baseEnd_569151 : Nat := 194832018658138618530019

theorem tailTrace_569151 : CollatzResearch.WordTrace tailWord_569151 prefixEnd_569151 194832018658138618530019 := by
  unfold tailWord_569151
  simp only [CollatzResearch.WordTrace]
  refine ⟨20758642361070605097163307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13839094907380403398108871 20758642361070605097163307)
  ·
    refine ⟨31137963541605907645744961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20758642361070605097163307 31137963541605907645744961)
    ·
      refine ⟨23353472656204430734308721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31137963541605907645744961 23353472656204430734308721)
      ·
        refine ⟨17515104492153323050731541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23353472656204430734308721 17515104492153323050731541)
        ·
          refine ⟨821020523069687018003041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17515104492153323050731541 821020523069687018003041)
          ·
            refine ⟨615765392302265263502281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 821020523069687018003041 615765392302265263502281)
            ·
              refine ⟨461824044226698947626711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 615765392302265263502281 461824044226698947626711)
              ·
                refine ⟨692736066340048421440067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461824044226698947626711 692736066340048421440067)
                ·
                  refine ⟨1039104099510072632160101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692736066340048421440067 1039104099510072632160101)
                  ·
                    refine ⟨194832018658138618530019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1039104099510072632160101 194832018658138618530019)
                    ·
                      rfl

theorem cell22_569151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 1, 4].length) (baseStart_569151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569151 prefixEnd_569151 := by exact prefixLift 569151
  have htrace : WordTrace (prefixWord ++ tailWord_569151) baseStart_569151 baseEnd_569151 := by
    simpa [prefixWord, tailWord_569151, baseEnd_569151] using wordTrace_append hprefix tailTrace_569151
  have hstable : (prefixWord ++ tailWord_569151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569151).length < 2 ^ (prefixWord ++ tailWord_569151).sum := by decide
  have hdescent : baseEnd_569151 < baseStart_569151 := by decide
  rcases family_descends (prefixWord ++ tailWord_569151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569160 : List Nat := [2, 1, 3, 1, 1, 5, 9]
def baseStart_569160 : Nat := 118140960795 + 569160 * 2 ^ 59
def prefixEnd_569160 : Nat := 4983230072969 + 3 ^ 40 * 569160 * 2
def baseEnd_569160 : Nat := 7216114797854281298333

theorem tailTrace_569160 : CollatzResearch.WordTrace tailWord_569160 prefixEnd_569160 7216114797854281298333 := by
  unfold tailWord_569160
  simp only [CollatzResearch.WordTrace]
  refine ⟨10379485309018999817120467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13839313745358666422827289 10379485309018999817120467)
  ·
    refine ⟨15569227963528499725680701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10379485309018999817120467 15569227963528499725680701)
    ·
      refine ⟨5838460486323187397130263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15569227963528499725680701 5838460486323187397130263)
      ·
        refine ⟨8757690729484781095695395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5838460486323187397130263 8757690729484781095695395)
        ·
          refine ⟨13136536094227171643543093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8757690729484781095695395 13136536094227171643543093)
          ·
            refine ⟨1231550258833797341582165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13136536094227171643543093 1231550258833797341582165)
            ·
              refine ⟨7216114797854281298333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1231550258833797341582165 7216114797854281298333)
              ·
                rfl

theorem cell22_569160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 9].length) (baseStart_569160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569160 prefixEnd_569160 := by exact prefixLift 569160
  have htrace : WordTrace (prefixWord ++ tailWord_569160) baseStart_569160 baseEnd_569160 := by
    simpa [prefixWord, tailWord_569160, baseEnd_569160] using wordTrace_append hprefix tailTrace_569160
  have hstable : (prefixWord ++ tailWord_569160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569160).length < 2 ^ (prefixWord ++ tailWord_569160).sum := by decide
  have hdescent : baseEnd_569160 < baseStart_569160 := by decide
  rcases family_descends (prefixWord ++ tailWord_569160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569164 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 4, 3]
def baseStart_569164 : Nat := 118140960795 + 569164 * 2 ^ 59
def prefixEnd_569164 : Nat := 4983230072969 + 3 ^ 40 * 569164 * 2
def baseEnd_569164 : Nat := 194836468823810917954979

theorem tailTrace_569164 : CollatzResearch.WordTrace tailWord_569164 prefixEnd_569164 194836468823810917954979 := by
  unfold tailWord_569164
  simp only [CollatzResearch.WordTrace]
  refine ⟨10379558255011754158693273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13839411006682338878257697 10379558255011754158693273)
  ·
    refine ⟨7784668691258815619019955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10379558255011754158693273 7784668691258815619019955)
    ·
      refine ⟨11677003036888223428529933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7784668691258815619019955 11677003036888223428529933)
      ·
        refine ⟨4378876138833083785698725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11677003036888223428529933 4378876138833083785698725)
        ·
          refine ⟨821039276031203209818511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4378876138833083785698725 821039276031203209818511)
          ·
            refine ⟨1231558914046804814727767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821039276031203209818511 1231558914046804814727767)
            ·
              refine ⟨1847338371070207222091651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1231558914046804814727767 1847338371070207222091651)
              ·
                refine ⟨2771007556605310833137477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1847338371070207222091651 2771007556605310833137477)
                ·
                  refine ⟨519563916863495781213277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2771007556605310833137477 519563916863495781213277)
                  ·
                    refine ⟨194836468823810917954979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 519563916863495781213277 194836468823810917954979)
                    ·
                      rfl

theorem cell22_569164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_569164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569164 prefixEnd_569164 := by exact prefixLift 569164
  have htrace : WordTrace (prefixWord ++ tailWord_569164) baseStart_569164 baseEnd_569164 := by
    simpa [prefixWord, tailWord_569164, baseEnd_569164] using wordTrace_append hprefix tailTrace_569164
  have hstable : (prefixWord ++ tailWord_569164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569164).length < 2 ^ (prefixWord ++ tailWord_569164).sum := by decide
  have hdescent : baseEnd_569164 < baseStart_569164 := by decide
  rcases family_descends (prefixWord ++ tailWord_569164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569194 : List Nat := [3, 1, 3, 4, 1, 1, 1, 8]
def baseStart_569194 : Nat := 118140960795 + 569194 * 2 ^ 59
def prefixEnd_569194 : Nat := 4983230072969 + 3 ^ 40 * 569194 * 2
def baseEnd_569194 : Nat := 21649637604100093300543

theorem tailTrace_569194 : CollatzResearch.WordTrace tailWord_569194 prefixEnd_569194 21649637604100093300543 := by
  unfold tailWord_569194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5190052674978705860244659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13840140466609882293985757 5190052674978705860244659)
  ·
    refine ⟨7785079012468058790366989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5190052674978705860244659 7785079012468058790366989)
    ·
      refine ⟨2919404629675522046387621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7785079012468058790366989 2919404629675522046387621)
      ·
        refine ⟨547388368064160383697679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2919404629675522046387621 547388368064160383697679)
        ·
          refine ⟨821082552096240575546519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547388368064160383697679 821082552096240575546519)
          ·
            refine ⟨1231623828144360863319779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821082552096240575546519 1231623828144360863319779)
            ·
              refine ⟨1847435742216541294979669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1231623828144360863319779 1847435742216541294979669)
              ·
                refine ⟨21649637604100093300543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1847435742216541294979669 21649637604100093300543)
                ·
                  rfl

theorem cell22_569194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 8].length) (baseStart_569194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569194 prefixEnd_569194 := by exact prefixLift 569194
  have htrace : WordTrace (prefixWord ++ tailWord_569194) baseStart_569194 baseEnd_569194 := by
    simpa [prefixWord, tailWord_569194, baseEnd_569194] using wordTrace_append hprefix tailTrace_569194
  have hstable : (prefixWord ++ tailWord_569194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569194).length < 2 ^ (prefixWord ++ tailWord_569194).sum := by decide
  have hdescent : baseEnd_569194 < baseStart_569194 := by decide
  rcases family_descends (prefixWord ++ tailWord_569194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569239 : List Nat := [1, 1, 3, 3, 1, 3, 4, 1, 5]
def baseStart_569239 : Nat := 118140960795 + 569239 * 2 ^ 59
def prefixEnd_569239 : Nat := 4983230072969 + 3 ^ 40 * 569239 * 2
def baseEnd_569239 : Nat := 64954047618845240776583

theorem tailTrace_569239 : CollatzResearch.WordTrace tailWord_569239 prefixEnd_569239 64954047618845240776583 := by
  unfold tailWord_569239
  simp only [CollatzResearch.WordTrace]
  refine ⟨20761851984751796126366771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13841234656501197417577847 20761851984751796126366771)
  ·
    refine ⟨31142777977127694189550157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20761851984751796126366771 31142777977127694189550157)
    ·
      refine ⟨11678541741422885321081309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31142777977127694189550157 11678541741422885321081309)
      ·
        refine ⟨4379453153033581995405491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11678541741422885321081309 4379453153033581995405491)
        ·
          refine ⟨6569179729550372993108237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4379453153033581995405491 6569179729550372993108237)
          ·
            refine ⟨2463442398581389872415589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6569179729550372993108237 2463442398581389872415589)
            ·
              refine ⟨461895449734010601077923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2463442398581389872415589 461895449734010601077923)
              ·
                refine ⟨692843174601015901616885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461895449734010601077923 692843174601015901616885)
                ·
                  refine ⟨64954047618845240776583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 692843174601015901616885 64954047618845240776583)
                  ·
                    rfl

theorem cell22_569239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 5].length) (baseStart_569239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569239 prefixEnd_569239 := by exact prefixLift 569239
  have htrace : WordTrace (prefixWord ++ tailWord_569239) baseStart_569239 baseEnd_569239 := by
    simpa [prefixWord, tailWord_569239, baseEnd_569239] using wordTrace_append hprefix tailTrace_569239
  have hstable : (prefixWord ++ tailWord_569239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569239).length < 2 ^ (prefixWord ++ tailWord_569239).sum := by decide
  have hdescent : baseEnd_569239 < baseStart_569239 := by decide
  rcases family_descends (prefixWord ++ tailWord_569239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569404 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 3, 4]
def baseStart_569404 : Nat := 118140960795 + 569404 * 2 ^ 59
def prefixEnd_569404 : Nat := 4983230072969 + 3 ^ 40 * 569404 * 2
def baseEnd_569404 : Nat := 194918625728530291954243

theorem tailTrace_569404 : CollatzResearch.WordTrace tailWord_569404 prefixEnd_569404 194918625728530291954243 := by
  unfold tailWord_569404
  simp only [CollatzResearch.WordTrace]
  refine ⟨10383935014577014653061633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13845246686102686204082177 10383935014577014653061633)
  ·
    refine ⟨7787951260932760989796225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10383935014577014653061633 7787951260932760989796225)
    ·
      refine ⟨5840963445699570742347169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7787951260932760989796225 5840963445699570742347169)
      ·
        refine ⟨4380722584274678056760377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5840963445699570742347169 4380722584274678056760377)
        ·
          refine ⟨3285541938206008542570283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4380722584274678056760377 3285541938206008542570283)
          ·
            refine ⟨4928312907309012813855425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3285541938206008542570283 4928312907309012813855425)
            ·
              refine ⟨3696234680481759610391569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4928312907309012813855425 3696234680481759610391569)
              ·
                refine ⟨2772176010361319707793677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3696234680481759610391569 2772176010361319707793677)
                ·
                  refine ⟨1039566003885494890422629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2772176010361319707793677 1039566003885494890422629)
                  ·
                    refine ⟨194918625728530291954243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1039566003885494890422629 194918625728530291954243)
                    ·
                      rfl

theorem cell22_569404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_569404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569404 prefixEnd_569404 := by exact prefixLift 569404
  have htrace : WordTrace (prefixWord ++ tailWord_569404) baseStart_569404 baseEnd_569404 := by
    simpa [prefixWord, tailWord_569404, baseEnd_569404] using wordTrace_append hprefix tailTrace_569404
  have hstable : (prefixWord ++ tailWord_569404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569404).length < 2 ^ (prefixWord ++ tailWord_569404).sum := by decide
  have hdescent : baseEnd_569404 < baseStart_569404 := by decide
  rcases family_descends (prefixWord ++ tailWord_569404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569421 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_569421 : Nat := 118140960795 + 569421 * 2 ^ 59
def prefixEnd_569421 : Nat := 4983230072969 + 3 ^ 40 * 569421 * 2
def baseEnd_569421 : Nat := 194924445175947914279191

theorem tailTrace_569421 : CollatzResearch.WordTrace tailWord_569421 prefixEnd_569421 194924445175947914279191 := by
  unfold tailWord_569421
  simp only [CollatzResearch.WordTrace]
  refine ⟨20768490070092441209492117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13845660046728294139661411 20768490070092441209492117)
  ·
    refine ⟨973522972035583181694943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20768490070092441209492117 973522972035583181694943)
    ·
      refine ⟨1460284458053374772542415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 973522972035583181694943 1460284458053374772542415)
      ·
        refine ⟨2190426687080062158813623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1460284458053374772542415 2190426687080062158813623)
        ·
          refine ⟨3285640030620093238220435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2190426687080062158813623 3285640030620093238220435)
          ·
            refine ⟨4928460045930139857330653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3285640030620093238220435 4928460045930139857330653)
            ·
              refine ⟨1848172517223802446498995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4928460045930139857330653 1848172517223802446498995)
              ·
                refine ⟨2772258775835703669748493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848172517223802446498995 2772258775835703669748493)
                ·
                  refine ⟨1039597040938388876155685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2772258775835703669748493 1039597040938388876155685)
                  ·
                    refine ⟨194924445175947914279191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1039597040938388876155685 194924445175947914279191)
                    ·
                      rfl

theorem cell22_569421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_569421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569421 prefixEnd_569421 := by exact prefixLift 569421
  have htrace : WordTrace (prefixWord ++ tailWord_569421) baseStart_569421 baseEnd_569421 := by
    simpa [prefixWord, tailWord_569421, baseEnd_569421] using wordTrace_append hprefix tailTrace_569421
  have hstable : (prefixWord ++ tailWord_569421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569421).length < 2 ^ (prefixWord ++ tailWord_569421).sum := by decide
  have hdescent : baseEnd_569421 < baseStart_569421 := by decide
  rcases family_descends (prefixWord ++ tailWord_569421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569434 : List Nat := [3, 1, 1, 2, 1, 1, 5, 2, 1, 5]
def baseStart_569434 : Nat := 118140960795 + 569434 * 2 ^ 59
def prefixEnd_569434 : Nat := 4983230072969 + 3 ^ 40 * 569434 * 2
def baseEnd_569434 : Nat := 194928895341620213704151

theorem tailTrace_569434 : CollatzResearch.WordTrace tailWord_569434 prefixEnd_569434 194928895341620213704151 := by
  unfold tailWord_569434
  simp only [CollatzResearch.WordTrace]
  refine ⟨5192241054761336107428839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13845976146030229619810237 5192241054761336107428839)
  ·
    refine ⟨7788361582142004161143259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5192241054761336107428839 7788361582142004161143259)
    ·
      refine ⟨11682542373213006241714889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7788361582142004161143259 11682542373213006241714889)
      ·
        refine ⟨8761906779909754681286167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11682542373213006241714889 8761906779909754681286167)
        ·
          refine ⟨13142860169864632021929251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8761906779909754681286167 13142860169864632021929251)
          ·
            refine ⟨19714290254796948032893877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13142860169864632021929251 19714290254796948032893877)
            ·
              refine ⟨1848214711387213878083801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19714290254796948032893877 1848214711387213878083801)
              ·
                refine ⟨1386161033540410408562851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1848214711387213878083801 1386161033540410408562851)
                ·
                  refine ⟨2079241550310615612844277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1386161033540410408562851 2079241550310615612844277)
                  ·
                    refine ⟨194928895341620213704151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2079241550310615612844277 194928895341620213704151)
                    ·
                      rfl

theorem cell22_569434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_569434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569434 prefixEnd_569434 := by exact prefixLift 569434
  have htrace : WordTrace (prefixWord ++ tailWord_569434) baseStart_569434 baseEnd_569434 := by
    simpa [prefixWord, tailWord_569434, baseEnd_569434] using wordTrace_append hprefix tailTrace_569434
  have hstable : (prefixWord ++ tailWord_569434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569434).length < 2 ^ (prefixWord ++ tailWord_569434).sum := by decide
  have hdescent : baseEnd_569434 < baseStart_569434 := by decide
  rcases family_descends (prefixWord ++ tailWord_569434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569449 : List Nat := [1, 2, 1, 1, 1, 5, 1, 4, 2, 4]
def baseStart_569449 : Nat := 118140960795 + 569449 * 2 ^ 59
def prefixEnd_569449 : Nat := 4983230072969 + 3 ^ 40 * 569449 * 2
def baseEnd_569449 : Nat := 194934030148165174579105

theorem tailTrace_569449 : CollatzResearch.WordTrace tailWord_569449 prefixEnd_569449 194934030148165174579105 := by
  unfold tailWord_569449
  simp only [CollatzResearch.WordTrace]
  refine ⟨20769511313991001991511401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13846340875994001327674267 20769511313991001991511401)
  ·
    refine ⟨15577133485493251493633551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20769511313991001991511401 15577133485493251493633551)
    ·
      refine ⟨23365700228239877240450327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15577133485493251493633551 23365700228239877240450327)
      ·
        refine ⟨35048550342359815860675491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23365700228239877240450327 35048550342359815860675491)
        ·
          refine ⟨52572825513539723791013237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35048550342359815860675491 52572825513539723791013237)
          ·
            refine ⟨4928702391894349105407491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52572825513539723791013237 4928702391894349105407491)
            ·
              refine ⟨7393053587841523658111237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4928702391894349105407491 7393053587841523658111237)
              ·
                refine ⟨1386197547720285685895857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7393053587841523658111237 1386197547720285685895857)
                ·
                  refine ⟨1039648160790214264421893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1386197547720285685895857 1039648160790214264421893)
                  ·
                    refine ⟨194934030148165174579105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1039648160790214264421893 194934030148165174579105)
                    ·
                      rfl

theorem cell22_569449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_569449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569449 prefixEnd_569449 := by exact prefixLift 569449
  have htrace : WordTrace (prefixWord ++ tailWord_569449) baseStart_569449 baseEnd_569449 := by
    simpa [prefixWord, tailWord_569449, baseEnd_569449] using wordTrace_append hprefix tailTrace_569449
  have hstable : (prefixWord ++ tailWord_569449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569449).length < 2 ^ (prefixWord ++ tailWord_569449).sum := by decide
  have hdescent : baseEnd_569449 < baseStart_569449 := by decide
  rcases family_descends (prefixWord ++ tailWord_569449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569502 : List Nat := [4, 3, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_569502 : Nat := 118140960795 + 569502 * 2 ^ 59
def prefixEnd_569502 : Nat := 4983230072969 + 3 ^ 40 * 569502 * 2
def baseEnd_569502 : Nat := 194952173131290703003943

theorem tailTrace_569502 : CollatzResearch.WordTrace tailWord_569502 prefixEnd_569502 194952173131290703003943 := by
  unfold tailWord_569502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2596430547849874005398845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13847629588532661362127173 2596430547849874005398845)
  ·
    refine ⟨973661455443702752024567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2596430547849874005398845 973661455443702752024567)
    ·
      refine ⟨1460492183165554128036851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 973661455443702752024567 1460492183165554128036851)
      ·
        refine ⟨2190738274748331192055277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1460492183165554128036851 2190738274748331192055277)
        ·
          refine ⟨821526853030624197020729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2190738274748331192055277 821526853030624197020729)
          ·
            refine ⟨616145139772968147765547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 821526853030624197020729 616145139772968147765547)
            ·
              refine ⟨924217709659452221648321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616145139772968147765547 924217709659452221648321)
              ·
                refine ⟨693163282244589166236241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 924217709659452221648321 693163282244589166236241)
                ·
                  refine ⟨519872461683441874677181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 693163282244589166236241 519872461683441874677181)
                  ·
                    refine ⟨194952173131290703003943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 519872461683441874677181 194952173131290703003943)
                    ·
                      rfl

theorem cell22_569502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_569502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569502 prefixEnd_569502 := by exact prefixLift 569502
  have htrace : WordTrace (prefixWord ++ tailWord_569502) baseStart_569502 baseEnd_569502 := by
    simpa [prefixWord, tailWord_569502, baseEnd_569502] using wordTrace_append hprefix tailTrace_569502
  have hstable : (prefixWord ++ tailWord_569502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569502).length < 2 ^ (prefixWord ++ tailWord_569502).sum := by decide
  have hdescent : baseEnd_569502 < baseStart_569502 := by decide
  rcases family_descends (prefixWord ++ tailWord_569502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569509 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 7]
def baseStart_569509 : Nat := 118140960795 + 569509 * 2 ^ 59
def prefixEnd_569509 : Nat := 4983230072969 + 3 ^ 40 * 569509 * 2
def baseEnd_569509 : Nat := 64984856458115006026307

theorem tailTrace_569509 : CollatzResearch.WordTrace tailWord_569509 prefixEnd_569509 64984856458115006026307 := by
  unfold tailWord_569509
  simp only [CollatzResearch.WordTrace]
  refine ⟨20771699693773632238695581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13847799795849088159130387 20771699693773632238695581)
  ·
    refine ⟨7789387385165112089510843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20771699693773632238695581 7789387385165112089510843)
    ·
      refine ⟨11684081077747668134266265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7789387385165112089510843 11684081077747668134266265)
      ·
        refine ⟨8763060808310751100699699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11684081077747668134266265 8763060808310751100699699)
        ·
          refine ⟨13144591212466126651049549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8763060808310751100699699 13144591212466126651049549)
          ·
            refine ⟨4929221704674797494143581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13144591212466126651049549 4929221704674797494143581)
            ·
              refine ⟨1848458139253049060303843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4929221704674797494143581 1848458139253049060303843)
              ·
                refine ⟨2772687208879573590455765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848458139253049060303843 2772687208879573590455765)
                ·
                  refine ⟨64984856458115006026307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2772687208879573590455765 64984856458115006026307)
                  ·
                    rfl

theorem cell22_569509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_569509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569509 prefixEnd_569509 := by exact prefixLift 569509
  have htrace : WordTrace (prefixWord ++ tailWord_569509) baseStart_569509 baseEnd_569509 := by
    simpa [prefixWord, tailWord_569509, baseEnd_569509] using wordTrace_append hprefix tailTrace_569509
  have hstable : (prefixWord ++ tailWord_569509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569509).length < 2 ^ (prefixWord ++ tailWord_569509).sum := by decide
  have hdescent : baseEnd_569509 < baseStart_569509 := by decide
  rcases family_descends (prefixWord ++ tailWord_569509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569539 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 7, 4]
def baseStart_569539 : Nat := 118140960795 + 569539 * 2 ^ 59
def prefixEnd_569539 : Nat := 4983230072969 + 3 ^ 40 * 569539 * 2
def baseEnd_569539 : Nat := 194964838987434939828829

theorem tailTrace_569539 : CollatzResearch.WordTrace tailWord_569539 prefixEnd_569539 194964838987434939828829 := by
  unfold tailWord_569539
  simp only [CollatzResearch.WordTrace]
  refine ⟨20772793883664947362287671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13848529255776631574858447 20772793883664947362287671)
  ·
    refine ⟨31159190825497421043431507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20772793883664947362287671 31159190825497421043431507)
    ·
      refine ⟨46738786238246131565147261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31159190825497421043431507 46738786238246131565147261)
      ·
        refine ⟨17527044839342299336930223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46738786238246131565147261 17527044839342299336930223)
        ·
          refine ⟨26290567259013449005395335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17527044839342299336930223 26290567259013449005395335)
          ·
            refine ⟨39435850888520173508093003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26290567259013449005395335 39435850888520173508093003)
            ·
              refine ⟨59153776332780260262139505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39435850888520173508093003 59153776332780260262139505)
              ·
                refine ⟨44365332249585195196604629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59153776332780260262139505 44365332249585195196604629)
                ·
                  refine ⟨1039812474599653012420421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 44365332249585195196604629 1039812474599653012420421)
                  ·
                    refine ⟨194964838987434939828829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1039812474599653012420421 194964838987434939828829)
                    ·
                      rfl

theorem cell22_569539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 4].length) (baseStart_569539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569539 prefixEnd_569539 := by exact prefixLift 569539
  have htrace : WordTrace (prefixWord ++ tailWord_569539) baseStart_569539 baseEnd_569539 := by
    simpa [prefixWord, tailWord_569539, baseEnd_569539] using wordTrace_append hprefix tailTrace_569539
  have hstable : (prefixWord ++ tailWord_569539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569539).length < 2 ^ (prefixWord ++ tailWord_569539).sum := by decide
  have hdescent : baseEnd_569539 < baseStart_569539 := by decide
  rcases family_descends (prefixWord ++ tailWord_569539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569564 : List Nat := [2, 2, 5, 2, 2, 1, 1, 1, 3, 3]
def baseStart_569564 : Nat := 118140960795 + 569564 * 2 ^ 59
def prefixEnd_569564 : Nat := 4983230072969 + 3 ^ 40 * 569564 * 2
def baseEnd_569564 : Nat := 194973396998343207953753

theorem tailTrace_569564 : CollatzResearch.WordTrace tailWord_569564 prefixEnd_569564 194973396998343207953753 := by
  unfold tailWord_569564
  simp only [CollatzResearch.WordTrace]
  refine ⟨10386852854287188315973873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13849137139049584421298497 10386852854287188315973873)
  ·
    refine ⟨7790139640715391236980405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10386852854287188315973873 7790139640715391236980405)
    ·
      refine ⟨730325591317067928466913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7790139640715391236980405 730325591317067928466913)
      ·
        refine ⟨547744193487800946350185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 730325591317067928466913 547744193487800946350185)
        ·
          refine ⟨410808145115850709762639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 547744193487800946350185 410808145115850709762639)
          ·
            refine ⟨616212217673776064643959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410808145115850709762639 616212217673776064643959)
            ·
              refine ⟨924318326510664096965939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616212217673776064643959 924318326510664096965939)
              ·
                refine ⟨1386477489765996145448909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 924318326510664096965939 1386477489765996145448909)
                ·
                  refine ⟨519929058662248554543341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1386477489765996145448909 519929058662248554543341)
                  ·
                    refine ⟨194973396998343207953753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 519929058662248554543341 194973396998343207953753)
                    ·
                      rfl

theorem cell22_569564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_569564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569564 prefixEnd_569564 := by exact prefixLift 569564
  have htrace : WordTrace (prefixWord ++ tailWord_569564) baseStart_569564 baseEnd_569564 := by
    simpa [prefixWord, tailWord_569564, baseEnd_569564] using wordTrace_append hprefix tailTrace_569564
  have hstable : (prefixWord ++ tailWord_569564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569564).length < 2 ^ (prefixWord ++ tailWord_569564).sum := by decide
  have hdescent : baseEnd_569564 < baseStart_569564 := by decide
  rcases family_descends (prefixWord ++ tailWord_569564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569584 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 3, 6]
def baseStart_569584 : Nat := 118140960795 + 569584 * 2 ^ 59
def prefixEnd_569584 : Nat := 4983230072969 + 3 ^ 40 * 569584 * 2
def baseEnd_569584 : Nat := 194980243407069822453691

theorem tailTrace_569584 : CollatzResearch.WordTrace tailWord_569584 prefixEnd_569584 194980243407069822453691 := by
  unfold tailWord_569584
  simp only [CollatzResearch.WordTrace]
  refine ⟨10387217584250960023837903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13849623445667946698450537 10387217584250960023837903)
  ·
    refine ⟨15580826376376440035756855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10387217584250960023837903 15580826376376440035756855)
    ·
      refine ⟨23371239564564660053635283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15580826376376440035756855 23371239564564660053635283)
      ·
        refine ⟨35056859346846990080452925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23371239564564660053635283 35056859346846990080452925)
        ·
          refine ⟨13146322255067621280169847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35056859346846990080452925 13146322255067621280169847)
          ·
            refine ⟨19719483382601431920254771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13146322255067621280169847 19719483382601431920254771)
            ·
              refine ⟨29579225073902147880382157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19719483382601431920254771 29579225073902147880382157)
              ·
                refine ⟨11092209402713305455143309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29579225073902147880382157 11092209402713305455143309)
                ·
                  refine ⟨4159578526017489545678741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11092209402713305455143309 4159578526017489545678741)
                  ·
                    refine ⟨194980243407069822453691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4159578526017489545678741 194980243407069822453691)
                    ·
                      rfl

theorem cell22_569584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_569584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569584 prefixEnd_569584 := by exact prefixLift 569584
  have htrace : WordTrace (prefixWord ++ tailWord_569584) baseStart_569584 baseEnd_569584 := by
    simpa [prefixWord, tailWord_569584, baseEnd_569584] using wordTrace_append hprefix tailTrace_569584
  have hstable : (prefixWord ++ tailWord_569584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569584).length < 2 ^ (prefixWord ++ tailWord_569584).sum := by decide
  have hdescent : baseEnd_569584 < baseStart_569584 := by decide
  rcases family_descends (prefixWord ++ tailWord_569584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569599 : List Nat := [1, 1, 2, 2, 1, 4, 1, 10]
def baseStart_569599 : Nat := 118140960795 + 569599 * 2 ^ 59
def prefixEnd_569599 : Nat := 4983230072969 + 3 ^ 40 * 569599 * 2
def baseEnd_569599 : Nat := 21665042023734975925405

theorem tailTrace_569599 : CollatzResearch.WordTrace tailWord_569599 prefixEnd_569599 21665042023734975925405 := by
  unfold tailWord_569599
  simp only [CollatzResearch.WordTrace]
  refine ⟨20774982263447577609471851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13849988175631718406314567 20774982263447577609471851)
  ·
    refine ⟨31162473395171366414207777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20774982263447577609471851 31162473395171366414207777)
    ·
      refine ⟨23371855046378524810655833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31162473395171366414207777 23371855046378524810655833)
      ·
        refine ⟨17528891284783893607991875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23371855046378524810655833 17528891284783893607991875)
        ·
          refine ⟨26293336927175840411987813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17528891284783893607991875 26293336927175840411987813)
          ·
            refine ⟨4930000673845470077247715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26293336927175840411987813 4930000673845470077247715)
            ·
              refine ⟨7395001010768205115871573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4930000673845470077247715 7395001010768205115871573)
              ·
                refine ⟨21665042023734975925405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7395001010768205115871573 21665042023734975925405)
                ·
                  rfl

theorem cell22_569599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 10].length) (baseStart_569599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569599 prefixEnd_569599 := by exact prefixLift 569599
  have htrace : WordTrace (prefixWord ++ tailWord_569599) baseStart_569599 baseEnd_569599 := by
    simpa [prefixWord, tailWord_569599, baseEnd_569599] using wordTrace_append hprefix tailTrace_569599
  have hstable : (prefixWord ++ tailWord_569599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569599).length < 2 ^ (prefixWord ++ tailWord_569599).sum := by decide
  have hdescent : baseEnd_569599 < baseStart_569599 := by decide
  rcases family_descends (prefixWord ++ tailWord_569599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569607 : List Nat := [1, 1, 4, 5, 1, 1, 3, 1, 1, 4]
def baseStart_569607 : Nat := 118140960795 + 569607 * 2 ^ 59
def prefixEnd_569607 : Nat := 4983230072969 + 3 ^ 40 * 569607 * 2
def baseEnd_569607 : Nat := 194988116777105429128621

theorem tailTrace_569607 : CollatzResearch.WordTrace tailWord_569607 prefixEnd_569607 194988116777105429128621 := by
  unfold tailWord_569607
  simp only [CollatzResearch.WordTrace]
  refine ⟨20775274047418594975763075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13850182698279063317175383 20775274047418594975763075)
  ·
    refine ⟨31162911071127892463644613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20775274047418594975763075 31162911071127892463644613)
    ·
      refine ⟨5843045825836479836933365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31162911071127892463644613 5843045825836479836933365)
      ·
        refine ⟨547785546172169984712503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5843045825836479836933365 547785546172169984712503)
        ·
          refine ⟨821678319258254977068755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547785546172169984712503 821678319258254977068755)
          ·
            refine ⟨1232517478887382465603133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821678319258254977068755 1232517478887382465603133)
            ·
              refine ⟨462194054582768424601175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1232517478887382465603133 462194054582768424601175)
              ·
                refine ⟨693291081874152636901763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462194054582768424601175 693291081874152636901763)
                ·
                  refine ⟨1039936622811228955352645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 693291081874152636901763 1039936622811228955352645)
                  ·
                    refine ⟨194988116777105429128621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1039936622811228955352645 194988116777105429128621)
                    ·
                      rfl

theorem cell22_569607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_569607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569607 prefixEnd_569607 := by exact prefixLift 569607
  have htrace : WordTrace (prefixWord ++ tailWord_569607) baseStart_569607 baseEnd_569607 := by
    simpa [prefixWord, tailWord_569607, baseEnd_569607] using wordTrace_append hprefix tailTrace_569607
  have hstable : (prefixWord ++ tailWord_569607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569607).length < 2 ^ (prefixWord ++ tailWord_569607).sum := by decide
  have hdescent : baseEnd_569607 < baseStart_569607 := by decide
  rcases family_descends (prefixWord ++ tailWord_569607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569676 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 4, 5]
def baseStart_569676 : Nat := 118140960795 + 569676 * 2 ^ 59
def prefixEnd_569676 : Nat := 4983230072969 + 3 ^ 40 * 569676 * 2
def baseEnd_569676 : Nat := 195011736887212249153409

theorem tailTrace_569676 : CollatzResearch.WordTrace tailWord_569676 prefixEnd_569676 195011736887212249153409 := by
  unfold tailWord_569676
  simp only [CollatzResearch.WordTrace]
  refine ⟨10388895342084309880012441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13851860456112413173349921 10388895342084309880012441)
  ·
    refine ⟨7791671506563232410009331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10388895342084309880012441 7791671506563232410009331)
    ·
      refine ⟨11687507259844848615013997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7791671506563232410009331 11687507259844848615013997)
      ·
        refine ⟨4382815222441818230630249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11687507259844848615013997 4382815222441818230630249)
        ·
          refine ⟨3287111416831363672972687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4382815222441818230630249 3287111416831363672972687)
          ·
            refine ⟨4930667125247045509459031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3287111416831363672972687 4930667125247045509459031)
            ·
              refine ⟨7396000687870568264188547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4930667125247045509459031 7396000687870568264188547)
              ·
                refine ⟨11094001031805852396282821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7396000687870568264188547 11094001031805852396282821)
                ·
                  refine ⟨2080125193463597324303029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11094001031805852396282821 2080125193463597324303029)
                  ·
                    refine ⟨195011736887212249153409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2080125193463597324303029 195011736887212249153409)
                    ·
                      rfl

theorem cell22_569676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_569676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569676 prefixEnd_569676 := by exact prefixLift 569676
  have htrace : WordTrace (prefixWord ++ tailWord_569676) baseStart_569676 baseEnd_569676 := by
    simpa [prefixWord, tailWord_569676, baseEnd_569676] using wordTrace_append hprefix tailTrace_569676
  have hstable : (prefixWord ++ tailWord_569676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569676).length < 2 ^ (prefixWord ++ tailWord_569676).sum := by decide
  have hdescent : baseEnd_569676 < baseStart_569676 := by decide
  rcases family_descends (prefixWord ++ tailWord_569676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569721 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 3, 5]
def baseStart_569721 : Nat := 118140960795 + 569721 * 2 ^ 59
def prefixEnd_569721 : Nat := 4983230072969 + 3 ^ 40 * 569721 * 2
def baseEnd_569721 : Nat := 195027141306847131778271

theorem tailTrace_569721 : CollatzResearch.WordTrace tailWord_569721 prefixEnd_569721 195027141306847131778271 := by
  unfold tailWord_569721
  simp only [CollatzResearch.WordTrace]
  refine ⟨20779431969005592445413017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13852954646003728296942011 20779431969005592445413017)
  ·
    refine ⟨15584573976754194334059763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20779431969005592445413017 15584573976754194334059763)
    ·
      refine ⟨23376860965131291501089645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15584573976754194334059763 23376860965131291501089645)
      ·
        refine ⟨8766322861924234312908617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23376860965131291501089645 8766322861924234312908617)
        ·
          refine ⟨6574742146443175734681463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8766322861924234312908617 6574742146443175734681463)
          ·
            refine ⟨9862113219664763602022195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6574742146443175734681463 9862113219664763602022195)
            ·
              refine ⟨14793169829497145403033293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9862113219664763602022195 14793169829497145403033293)
              ·
                refine ⟨5547438686061429526137485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14793169829497145403033293 5547438686061429526137485)
                ·
                  refine ⟨2080289507273036072301557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5547438686061429526137485 2080289507273036072301557)
                  ·
                    refine ⟨195027141306847131778271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2080289507273036072301557 195027141306847131778271)
                    ·
                      rfl

theorem cell22_569721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_569721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569721 prefixEnd_569721 := by exact prefixLift 569721
  have htrace : WordTrace (prefixWord ++ tailWord_569721) baseStart_569721 baseEnd_569721 := by
    simpa [prefixWord, tailWord_569721, baseEnd_569721] using wordTrace_append hprefix tailTrace_569721
  have hstable : (prefixWord ++ tailWord_569721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569721).length < 2 ^ (prefixWord ++ tailWord_569721).sum := by decide
  have hdescent : baseEnd_569721 < baseStart_569721 := by decide
  rcases family_descends (prefixWord ++ tailWord_569721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569751 : List Nat := [1, 1, 3, 3, 1, 1, 3, 9]
def baseStart_569751 : Nat := 118140960795 + 569751 * 2 ^ 59
def prefixEnd_569751 : Nat := 4983230072969 + 3 ^ 40 * 569751 * 2
def baseEnd_569751 : Nat := 21670823435548561503131

theorem tailTrace_569751 : CollatzResearch.WordTrace tailWord_569751 prefixEnd_569751 21670823435548561503131 := by
  unfold tailWord_569751
  simp only [CollatzResearch.WordTrace]
  refine ⟨20780526158896907569005107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13853684105931271712670071 20780526158896907569005107)
  ·
    refine ⟨31170789238345361353507661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20780526158896907569005107 31170789238345361353507661)
    ·
      refine ⟨11689045964379510507565373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31170789238345361353507661 11689045964379510507565373)
      ·
        refine ⟨4383392236642316440337015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11689045964379510507565373 4383392236642316440337015)
        ·
          refine ⟨6575088354963474660505523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4383392236642316440337015 6575088354963474660505523)
          ·
            refine ⟨9862632532445211990758285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6575088354963474660505523 9862632532445211990758285)
            ·
              refine ⟨3698487199666954496534357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9862632532445211990758285 3698487199666954496534357)
              ·
                refine ⟨21670823435548561503131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3698487199666954496534357 21670823435548561503131)
                ·
                  rfl

theorem cell22_569751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 9].length) (baseStart_569751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569751 prefixEnd_569751 := by exact prefixLift 569751
  have htrace : WordTrace (prefixWord ++ tailWord_569751) baseStart_569751 baseEnd_569751 := by
    simpa [prefixWord, tailWord_569751, baseEnd_569751] using wordTrace_append hprefix tailTrace_569751
  have hstable : (prefixWord ++ tailWord_569751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569751).length < 2 ^ (prefixWord ++ tailWord_569751).sum := by decide
  have hdescent : baseEnd_569751 < baseStart_569751 := by decide
  rcases family_descends (prefixWord ++ tailWord_569751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569834 : List Nat := [3, 1, 3, 1, 3, 2, 2, 3, 1, 3]
def baseStart_569834 : Nat := 118140960795 + 569834 * 2 ^ 59
def prefixEnd_569834 : Nat := 4983230072969 + 3 ^ 40 * 569834 * 2
def baseEnd_569834 : Nat := 195065823516152503702925

theorem tailTrace_569834 : CollatzResearch.WordTrace tailWord_569834 prefixEnd_569834 195065823516152503702925 := by
  unfold tailWord_569834
  simp only [CollatzResearch.WordTrace]
  refine ⟨5195888354399053186069139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13855702278397475162851037 5195888354399053186069139)
  ·
    refine ⟨7793832531598579779103709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5195888354399053186069139 7793832531598579779103709)
    ·
      refine ⟨2922687199349467417163891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7793832531598579779103709 2922687199349467417163891)
      ·
        refine ⟨4384030799024201125745837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2922687199349467417163891 4384030799024201125745837)
        ·
          refine ⟨1644011549634075422154689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4384030799024201125745837 1644011549634075422154689)
          ·
            refine ⟨1233008662225556566616017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1644011549634075422154689 1233008662225556566616017)
            ·
              refine ⟨924756496669167424962013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1233008662225556566616017 924756496669167424962013)
              ·
                refine ⟨346783686250937784360755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 924756496669167424962013 346783686250937784360755)
                ·
                  refine ⟨520175529376406676541133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 346783686250937784360755 520175529376406676541133)
                  ·
                    refine ⟨195065823516152503702925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 520175529376406676541133 195065823516152503702925)
                    ·
                      rfl

theorem cell22_569834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_569834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569834 prefixEnd_569834 := by exact prefixLift 569834
  have htrace : WordTrace (prefixWord ++ tailWord_569834) baseStart_569834 baseEnd_569834 := by
    simpa [prefixWord, tailWord_569834, baseEnd_569834] using wordTrace_append hprefix tailTrace_569834
  have hstable : (prefixWord ++ tailWord_569834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569834).length < 2 ^ (prefixWord ++ tailWord_569834).sum := by decide
  have hdescent : baseEnd_569834 < baseStart_569834 := by decide
  rcases family_descends (prefixWord ++ tailWord_569834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569873 : List Nat := [1, 2, 2, 1, 1, 2, 2, 5, 1, 5]
def baseStart_569873 : Nat := 118140960795 + 569873 * 2 ^ 59
def prefixEnd_569873 : Nat := 4983230072969 + 3 ^ 40 * 569873 * 2
def baseEnd_569873 : Nat := 195079174013169401977805

theorem tailTrace_569873 : CollatzResearch.WordTrace tailWord_569873 prefixEnd_569873 195079174013169401977805 := by
  unfold tailWord_569873
  simp only [CollatzResearch.WordTrace]
  refine ⟨20784975864454922404946273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13856650576303281603297515 20784975864454922404946273)
  ·
    refine ⟨15588731898341191803709705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20784975864454922404946273 15588731898341191803709705)
    ·
      refine ⟨11691548923755893852782279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15588731898341191803709705 11691548923755893852782279)
      ·
        refine ⟨17537323385633840779173419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11691548923755893852782279 17537323385633840779173419)
        ·
          refine ⟨26305985078450761168760129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17537323385633840779173419 26305985078450761168760129)
          ·
            refine ⟨19729488808838070876570097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26305985078450761168760129 19729488808838070876570097)
            ·
              refine ⟨14797116606628553157427573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19729488808838070876570097 14797116606628553157427573)
              ·
                refine ⟨1387229681871426858508835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14797116606628553157427573 1387229681871426858508835)
                ·
                  refine ⟨2080844522807140287763253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387229681871426858508835 2080844522807140287763253)
                  ·
                    refine ⟨195079174013169401977805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2080844522807140287763253 195079174013169401977805)
                    ·
                      rfl

theorem cell22_569873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_569873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569873 prefixEnd_569873 := by exact prefixLift 569873
  have htrace : WordTrace (prefixWord ++ tailWord_569873) baseStart_569873 baseEnd_569873 := by
    simpa [prefixWord, tailWord_569873, baseEnd_569873] using wordTrace_append hprefix tailTrace_569873
  have hstable : (prefixWord ++ tailWord_569873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569873).length < 2 ^ (prefixWord ++ tailWord_569873).sum := by decide
  have hdescent : baseEnd_569873 < baseStart_569873 := by decide
  rcases family_descends (prefixWord ++ tailWord_569873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569935 : List Nat := [1, 1, 2, 1, 1, 2, 4, 4, 3, 3]
def baseStart_569935 : Nat := 118140960795 + 569935 * 2 ^ 59
def prefixEnd_569935 : Nat := 4983230072969 + 3 ^ 40 * 569935 * 2
def baseEnd_569935 : Nat := 195100397880221906927615

theorem tailTrace_569935 : CollatzResearch.WordTrace tailWord_569935 prefixEnd_569935 195100397880221906927615 := by
  unfold tailWord_569935
  simp only [CollatzResearch.WordTrace]
  refine ⟨20787237190230306993703259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13858158126820204662468839 20787237190230306993703259)
  ·
    refine ⟨31180855785345460490554889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20787237190230306993703259 31180855785345460490554889)
    ·
      refine ⟨23385641839009095367916167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31180855785345460490554889 23385641839009095367916167)
      ·
        refine ⟨35078462758513643051874251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23385641839009095367916167 35078462758513643051874251)
        ·
          refine ⟨52617694137770464577811377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35078462758513643051874251 52617694137770464577811377)
          ·
            refine ⟨39463270603327848433358533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52617694137770464577811377 39463270603327848433358533)
            ·
              refine ⟨7399363238123971581254725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39463270603327848433358533 7399363238123971581254725)
              ·
                refine ⟨1387380607148244671485261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7399363238123971581254725 1387380607148244671485261)
                ·
                  refine ⟨520267727680591751806973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1387380607148244671485261 520267727680591751806973)
                  ·
                    refine ⟨195100397880221906927615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 520267727680591751806973 195100397880221906927615)
                    ·
                      rfl

theorem cell22_569935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 3].length) (baseStart_569935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_569935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_569935 prefixEnd_569935 := by exact prefixLift 569935
  have htrace : WordTrace (prefixWord ++ tailWord_569935) baseStart_569935 baseEnd_569935 := by
    simpa [prefixWord, tailWord_569935, baseEnd_569935] using wordTrace_append hprefix tailTrace_569935
  have hstable : (prefixWord ++ tailWord_569935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569935).length < 2 ^ (prefixWord ++ tailWord_569935).sum := by decide
  have hdescent : baseEnd_569935 < baseStart_569935 := by decide
  rcases family_descends (prefixWord ++ tailWord_569935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570115 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 4, 5]
def baseStart_570115 : Nat := 118140960795 + 570115 * 2 ^ 59
def prefixEnd_570115 : Nat := 4983230072969 + 3 ^ 40 * 570115 * 2
def baseEnd_570115 : Nat := 195162015558761437427063

theorem tailTrace_570115 : CollatzResearch.WordTrace tailWord_570115 prefixEnd_570115 195162015558761437427063 := by
  unfold tailWord_570115
  simp only [CollatzResearch.WordTrace]
  refine ⟨20793802329578197735255799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13862534886385465156837199 20793802329578197735255799)
  ·
    refine ⟨31190703494367296602883699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20793802329578197735255799 31190703494367296602883699)
    ·
      refine ⟨46786055241550944904325549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31190703494367296602883699 46786055241550944904325549)
      ·
        refine ⟨17544770715581604339122081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46786055241550944904325549 17544770715581604339122081)
        ·
          refine ⟨13158578036686203254341561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17544770715581604339122081 13158578036686203254341561)
          ·
            refine ⟨9868933527514652440756171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13158578036686203254341561 9868933527514652440756171)
            ·
              refine ⟨14803400291271978661134257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9868933527514652440756171 14803400291271978661134257)
              ·
                refine ⟨11102550218453983995850693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14803400291271978661134257 11102550218453983995850693)
                ·
                  refine ⟨2081728165960121999222005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11102550218453983995850693 2081728165960121999222005)
                  ·
                    refine ⟨195162015558761437427063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2081728165960121999222005 195162015558761437427063)
                    ·
                      rfl

theorem cell22_570115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 5].length) (baseStart_570115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570115 prefixEnd_570115 := by exact prefixLift 570115
  have htrace : WordTrace (prefixWord ++ tailWord_570115) baseStart_570115 baseEnd_570115 := by
    simpa [prefixWord, tailWord_570115, baseEnd_570115] using wordTrace_append hprefix tailTrace_570115
  have hstable : (prefixWord ++ tailWord_570115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570115).length < 2 ^ (prefixWord ++ tailWord_570115).sum := by decide
  have hdescent : baseEnd_570115 < baseStart_570115 := by decide
  rcases family_descends (prefixWord ++ tailWord_570115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570162 : List Nat := [3, 2, 1, 1, 3, 1, 3, 2, 6]
def baseStart_570162 : Nat := 118140960795 + 570162 * 2 ^ 59
def prefixEnd_570162 : Nat := 4983230072969 + 3 ^ 40 * 570162 * 2
def baseEnd_570162 : Nat := 65059368206422993833973

theorem tailTrace_570162 : CollatzResearch.WordTrace tailWord_570162 prefixEnd_570162 65059368206422993833973 := by
  unfold tailWord_570162
  simp only [CollatzResearch.WordTrace]
  refine ⟨5198879140101981190554185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13863677706938616508144493 5198879140101981190554185)
  ·
    refine ⟨3899159355076485892915639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5198879140101981190554185 3899159355076485892915639)
    ·
      refine ⟨5848739032614728839373459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3899159355076485892915639 5848739032614728839373459)
      ·
        refine ⟨8773108548922093259060189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5848739032614728839373459 8773108548922093259060189)
        ·
          refine ⟨3289915705845784972147571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8773108548922093259060189 3289915705845784972147571)
          ·
            refine ⟨4934873558768677458221357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3289915705845784972147571 4934873558768677458221357)
            ·
              refine ⟨1850577584538254046833009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4934873558768677458221357 1850577584538254046833009)
              ·
                refine ⟨1387933188403690535124757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1850577584538254046833009 1387933188403690535124757)
                ·
                  refine ⟨65059368206422993833973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1387933188403690535124757 65059368206422993833973)
                  ·
                    rfl

theorem cell22_570162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_570162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570162 prefixEnd_570162 := by exact prefixLift 570162
  have htrace : WordTrace (prefixWord ++ tailWord_570162) baseStart_570162 baseEnd_570162 := by
    simpa [prefixWord, tailWord_570162, baseEnd_570162] using wordTrace_append hprefix tailTrace_570162
  have hstable : (prefixWord ++ tailWord_570162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570162).length < 2 ^ (prefixWord ++ tailWord_570162).sum := by decide
  have hdescent : baseEnd_570162 < baseStart_570162 := by decide
  rcases family_descends (prefixWord ++ tailWord_570162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570179 : List Nat := [1, 1, 1, 3, 1, 4, 4, 3, 4]
def baseStart_570179 : Nat := 118140960795 + 570179 * 2 ^ 59
def prefixEnd_570179 : Nat := 4983230072969 + 3 ^ 40 * 570179 * 2
def baseEnd_570179 : Nat := 65061308022228867942289

theorem tailTrace_570179 : CollatzResearch.WordTrace tailWord_570179 prefixEnd_570179 65061308022228867942289 := by
  unfold tailWord_570179
  simp only [CollatzResearch.WordTrace]
  refine ⟨20796136601346336665585591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13864091067564224443723727 20796136601346336665585591)
  ·
    refine ⟨31194204902019504998378387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20796136601346336665585591 31194204902019504998378387)
    ·
      refine ⟨46791307353029257497567581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31194204902019504998378387 46791307353029257497567581)
      ·
        refine ⟨17546740257385971561587843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46791307353029257497567581 17546740257385971561587843)
        ·
          refine ⟨26320110386078957342381765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17546740257385971561587843 26320110386078957342381765)
          ·
            refine ⟨4935020697389804501696581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26320110386078957342381765 4935020697389804501696581)
            ·
              refine ⟨925316380760588344068109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4935020697389804501696581 925316380760588344068109)
              ·
                refine ⟨346993642785220629025541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 925316380760588344068109 346993642785220629025541)
                ·
                  refine ⟨65061308022228867942289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 346993642785220629025541 65061308022228867942289)
                  ·
                    rfl

theorem cell22_570179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 4].length) (baseStart_570179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570179 prefixEnd_570179 := by exact prefixLift 570179
  have htrace : WordTrace (prefixWord ++ tailWord_570179) baseStart_570179 baseEnd_570179 := by
    simpa [prefixWord, tailWord_570179, baseEnd_570179] using wordTrace_append hprefix tailTrace_570179
  have hstable : (prefixWord ++ tailWord_570179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570179).length < 2 ^ (prefixWord ++ tailWord_570179).sum := by decide
  have hdescent : baseEnd_570179 < baseStart_570179 := by decide
  rcases family_descends (prefixWord ++ tailWord_570179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570192 : List Nat := [2, 1, 1, 1, 1, 4, 2, 4, 2, 4]
def baseStart_570192 : Nat := 118140960795 + 570192 * 2 ^ 59
def prefixEnd_570192 : Nat := 4983230072969 + 3 ^ 40 * 570192 * 2
def baseEnd_570192 : Nat := 195188374232358903251827

theorem tailTrace_570192 : CollatzResearch.WordTrace tailWord_570192 prefixEnd_570192 195188374232358903251827 := by
  unfold tailWord_570192
  simp only [CollatzResearch.WordTrace]
  refine ⟨10398305375149619942904415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13864407166866159923872553 10398305375149619942904415)
  ·
    refine ⟨15597458062724429914356623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10398305375149619942904415 15597458062724429914356623)
    ·
      refine ⟨23396187094086644871534935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15597458062724429914356623 23396187094086644871534935)
      ·
        refine ⟨35094280641129967307302403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23396187094086644871534935 35094280641129967307302403)
        ·
          refine ⟨52641420961694950960953605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35094280641129967307302403 52641420961694950960953605)
          ·
            refine ⟨9870266430317803305178801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52641420961694950960953605 9870266430317803305178801)
            ·
              refine ⟨7402699822738352478884101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9870266430317803305178801 7402699822738352478884101)
              ·
                refine ⟨1388006216763441089790769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7402699822738352478884101 1388006216763441089790769)
                ·
                  refine ⟨1041004662572580817343077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1388006216763441089790769 1041004662572580817343077)
                  ·
                    refine ⟨195188374232358903251827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1041004662572580817343077 195188374232358903251827)
                    ·
                      rfl

theorem cell22_570192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_570192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570192 prefixEnd_570192 := by exact prefixLift 570192
  have htrace : WordTrace (prefixWord ++ tailWord_570192) baseStart_570192 baseEnd_570192 := by
    simpa [prefixWord, tailWord_570192, baseEnd_570192] using wordTrace_append hprefix tailTrace_570192
  have hstable : (prefixWord ++ tailWord_570192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570192).length < 2 ^ (prefixWord ++ tailWord_570192).sum := by decide
  have hdescent : baseEnd_570192 < baseStart_570192 := by decide
  rcases family_descends (prefixWord ++ tailWord_570192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570194 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 4, 3]
def baseStart_570194 : Nat := 118140960795 + 570194 * 2 ^ 59
def prefixEnd_570194 : Nat := 4983230072969 + 3 ^ 40 * 570194 * 2
def baseEnd_570194 : Nat := 195189058873231564701821

theorem tailTrace_570194 : CollatzResearch.WordTrace tailWord_570194 prefixEnd_570194 195189058873231564701821 := by
  unfold tailWord_570194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5199170924072998556845409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13864455797527996151587757 5199170924072998556845409)
  ·
    refine ⟨3899378193054748917634057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5199170924072998556845409 3899378193054748917634057)
    ·
      refine ⟨2924533644791061688225543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3899378193054748917634057 2924533644791061688225543)
      ·
        refine ⟨4386800467186592532338315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2924533644791061688225543 4386800467186592532338315)
        ·
          refine ⟨6580200700779888798507473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4386800467186592532338315 6580200700779888798507473)
          ·
            refine ⟨4935150525584916598880605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6580200700779888798507473 4935150525584916598880605)
            ·
              refine ⟨1850681447094343724580227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4935150525584916598880605 1850681447094343724580227)
              ·
                refine ⟨2776022170641515586870341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1850681447094343724580227 2776022170641515586870341)
                ·
                  refine ⟨520504156995284172538189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2776022170641515586870341 520504156995284172538189)
                  ·
                    refine ⟨195189058873231564701821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 520504156995284172538189 195189058873231564701821)
                    ·
                      rfl

theorem cell22_570194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_570194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570194 prefixEnd_570194 := by exact prefixLift 570194
  have htrace : WordTrace (prefixWord ++ tailWord_570194) baseStart_570194 baseEnd_570194 := by
    simpa [prefixWord, tailWord_570194, baseEnd_570194] using wordTrace_append hprefix tailTrace_570194
  have hstable : (prefixWord ++ tailWord_570194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570194).length < 2 ^ (prefixWord ++ tailWord_570194).sum := by decide
  have hdescent : baseEnd_570194 < baseStart_570194 := by decide
  rcases family_descends (prefixWord ++ tailWord_570194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570252 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 7]
def baseStart_570252 : Nat := 118140960795 + 570252 * 2 ^ 59
def prefixEnd_570252 : Nat := 4983230072969 + 3 ^ 40 * 570252 * 2
def baseEnd_570252 : Nat := 65069637819512915583881

theorem tailTrace_570252 : CollatzResearch.WordTrace tailWord_570252 prefixEnd_570252 65069637819512915583881 := by
  unfold tailWord_570252
  simp only [CollatzResearch.WordTrace]
  refine ⟨10399399565040935066496505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13865866086721246755328673 10399399565040935066496505)
  ·
    refine ⟨7799549673780701299872379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10399399565040935066496505 7799549673780701299872379)
    ·
      refine ⟨11699324510671051949808569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7799549673780701299872379 11699324510671051949808569)
      ·
        refine ⟨8774493383003288962356427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11699324510671051949808569 8774493383003288962356427)
        ·
          refine ⟨13161740074504933443534641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8774493383003288962356427 13161740074504933443534641)
          ·
            refine ⟨9871305055878700082650981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13161740074504933443534641 9871305055878700082650981)
            ·
              refine ⟨1850869697977256265497059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9871305055878700082650981 1850869697977256265497059)
              ·
                refine ⟨2776304546965884398245589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1850869697977256265497059 2776304546965884398245589)
                ·
                  refine ⟨65069637819512915583881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2776304546965884398245589 65069637819512915583881)
                  ·
                    rfl

theorem cell22_570252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_570252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570252 prefixEnd_570252 := by exact prefixLift 570252
  have htrace : WordTrace (prefixWord ++ tailWord_570252) baseStart_570252 baseEnd_570252 := by
    simpa [prefixWord, tailWord_570252, baseEnd_570252] using wordTrace_append hprefix tailTrace_570252
  have hstable : (prefixWord ++ tailWord_570252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570252).length < 2 ^ (prefixWord ++ tailWord_570252).sum := by decide
  have hdescent : baseEnd_570252 < baseStart_570252 := by decide
  rcases family_descends (prefixWord ++ tailWord_570252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570262 : List Nat := [5, 3, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_570262 : Nat := 118140960795 + 570262 * 2 ^ 59
def prefixEnd_570262 : Nat := 4983230072969 + 3 ^ 40 * 570262 * 2
def baseEnd_570262 : Nat := 195212336662902054001613

theorem tailTrace_570262 : CollatzResearch.WordTrace tailWord_570262 prefixEnd_570262 195212336662902054001613 := by
  unfold tailWord_570262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1299947741252852615053565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13866109240030427893904693 1299947741252852615053565)
  ·
    refine ⟨487480402969819730645087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1299947741252852615053565 487480402969819730645087)
    ·
      refine ⟨731220604454729595967631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 487480402969819730645087 731220604454729595967631)
      ·
        refine ⟨1096830906682094393951447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 731220604454729595967631 1096830906682094393951447)
        ·
          refine ⟨1645246360023141590927171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1096830906682094393951447 1645246360023141590927171)
          ·
            refine ⟨2467869540034712386390757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645246360023141590927171 2467869540034712386390757)
            ·
              refine ⟨462725538756508572448267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2467869540034712386390757 462725538756508572448267)
              ·
                refine ⟨694088308134762858672401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462725538756508572448267 694088308134762858672401)
                ·
                  refine ⟨520566231101072144004301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 694088308134762858672401 520566231101072144004301)
                  ·
                    refine ⟨195212336662902054001613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 520566231101072144004301 195212336662902054001613)
                    ·
                      rfl

theorem cell22_570262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_570262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570262 prefixEnd_570262 := by exact prefixLift 570262
  have htrace : WordTrace (prefixWord ++ tailWord_570262) baseStart_570262 baseEnd_570262 := by
    simpa [prefixWord, tailWord_570262, baseEnd_570262] using wordTrace_append hprefix tailTrace_570262
  have hstable : (prefixWord ++ tailWord_570262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570262).length < 2 ^ (prefixWord ++ tailWord_570262).sum := by decide
  have hdescent : baseEnd_570262 < baseStart_570262 := by decide
  rcases family_descends (prefixWord ++ tailWord_570262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570269 : List Nat := [1, 4, 2, 1, 2, 1, 3, 3, 5]
def baseStart_570269 : Nat := 118140960795 + 570269 * 2 ^ 59
def prefixEnd_570269 : Nat := 4983230072969 + 3 ^ 40 * 570269 * 2
def baseEnd_570269 : Nat := 65071577635318789692197

theorem tailTrace_570269 : CollatzResearch.WordTrace tailWord_570269 prefixEnd_570269 65071577635318789692197 := by
  unfold tailWord_570269
  simp only [CollatzResearch.WordTrace]
  refine ⟨20799419171020282036361861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13866279447346854690907907 20799419171020282036361861)
  ·
    refine ⟨3899891094566302881817849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20799419171020282036361861 3899891094566302881817849)
    ·
      refine ⟨2924918320924727161363387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3899891094566302881817849 2924918320924727161363387)
      ·
        refine ⟨4387377481387090742045081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2924918320924727161363387 4387377481387090742045081)
        ·
          refine ⟨3290533111040318056533811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4387377481387090742045081 3290533111040318056533811)
          ·
            refine ⟨4935799666560477084800717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3290533111040318056533811 4935799666560477084800717)
            ·
              refine ⟨1850924874960178906800269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4935799666560477084800717 1850924874960178906800269)
              ·
                refine ⟨694096828110067090050101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1850924874960178906800269 694096828110067090050101)
                ·
                  refine ⟨65071577635318789692197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 694096828110067090050101 65071577635318789692197)
                  ·
                    rfl

theorem cell22_570269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_570269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570269 prefixEnd_570269 := by exact prefixLift 570269
  have htrace : WordTrace (prefixWord ++ tailWord_570269) baseStart_570269 baseEnd_570269 := by
    simpa [prefixWord, tailWord_570269, baseEnd_570269] using wordTrace_append hprefix tailTrace_570269
  have hstable : (prefixWord ++ tailWord_570269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570269).length < 2 ^ (prefixWord ++ tailWord_570269).sum := by decide
  have hdescent : baseEnd_570269 < baseStart_570269 := by decide
  rcases family_descends (prefixWord ++ tailWord_570269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570329 : List Nat := [1, 2, 1, 2, 5, 1, 1, 3, 1, 5]
def baseStart_570329 : Nat := 118140960795 + 570329 * 2 ^ 59
def prefixEnd_570329 : Nat := 4983230072969 + 3 ^ 40 * 570329 * 2
def baseEnd_570329 : Nat := 195235272132136212576407

theorem tailTrace_570329 : CollatzResearch.WordTrace tailWord_570329 prefixEnd_570329 195235272132136212576407 := by
  unfold tailWord_570329
  simp only [CollatzResearch.WordTrace]
  refine ⟨20801607550802912283546041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13867738367201941522364027 20801607550802912283546041)
  ·
    refine ⟨15601205663102184212659531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20801607550802912283546041 15601205663102184212659531)
    ·
      refine ⟨23401808494653276318989297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15601205663102184212659531 23401808494653276318989297)
      ·
        refine ⟨17551356370989957239241973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23401808494653276318989297 17551356370989957239241973)
        ·
          refine ⟨1645439659780308491178935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17551356370989957239241973 1645439659780308491178935)
          ·
            refine ⟨2468159489670462736768403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645439659780308491178935 2468159489670462736768403)
            ·
              refine ⟨3702239234505694105152605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2468159489670462736768403 3702239234505694105152605)
              ·
                refine ⟨1388339712939635289432227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3702239234505694105152605 1388339712939635289432227)
                ·
                  refine ⟨2082509569409452934148341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1388339712939635289432227 2082509569409452934148341)
                  ·
                    refine ⟨195235272132136212576407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2082509569409452934148341 195235272132136212576407)
                    ·
                      rfl

theorem cell22_570329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_570329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570329 prefixEnd_570329 := by exact prefixLift 570329
  have htrace : WordTrace (prefixWord ++ tailWord_570329) baseStart_570329 baseEnd_570329 := by
    simpa [prefixWord, tailWord_570329, baseEnd_570329] using wordTrace_append hprefix tailTrace_570329
  have hstable : (prefixWord ++ tailWord_570329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570329).length < 2 ^ (prefixWord ++ tailWord_570329).sum := by decide
  have hdescent : baseEnd_570329 < baseStart_570329 := by decide
  rcases family_descends (prefixWord ++ tailWord_570329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570350 : List Nat := [4, 1, 2, 1, 4, 2, 2, 1, 1, 4]
def baseStart_570350 : Nat := 118140960795 + 570350 * 2 ^ 59
def prefixEnd_570350 : Nat := 4983230072969 + 3 ^ 40 * 570350 * 2
def baseEnd_570350 : Nat := 195242460861299157801343

theorem tailTrace_570350 : CollatzResearch.WordTrace tailWord_570350 prefixEnd_570350 195242460861299157801343 := by
  unfold tailWord_570350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2600296685465854108757563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13868248989151221913373669 2600296685465854108757563)
  ·
    refine ⟨3900445028198781163136345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2600296685465854108757563 3900445028198781163136345)
    ·
      refine ⟨2925333771149085872352259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3900445028198781163136345 2925333771149085872352259)
      ·
        refine ⟨4388000656723628808528389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2925333771149085872352259 4388000656723628808528389)
        ·
          refine ⟨822750123135680401599073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4388000656723628808528389 822750123135680401599073)
          ·
            refine ⟨617062592351760301199305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 822750123135680401599073 617062592351760301199305)
            ·
              refine ⟨462796944263820225899479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 617062592351760301199305 462796944263820225899479)
              ·
                refine ⟨694195416395730338849219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462796944263820225899479 694195416395730338849219)
                ·
                  refine ⟨1041293124593595508273829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 694195416395730338849219 1041293124593595508273829)
                  ·
                    refine ⟨195242460861299157801343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1041293124593595508273829 195242460861299157801343)
                    ·
                      rfl

theorem cell22_570350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_570350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570350 prefixEnd_570350 := by exact prefixLift 570350
  have htrace : WordTrace (prefixWord ++ tailWord_570350) baseStart_570350 baseEnd_570350 := by
    simpa [prefixWord, tailWord_570350, baseEnd_570350] using wordTrace_append hprefix tailTrace_570350
  have hstable : (prefixWord ++ tailWord_570350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570350).length < 2 ^ (prefixWord ++ tailWord_570350).sum := by decide
  have hdescent : baseEnd_570350 < baseStart_570350 := by decide
  rcases family_descends (prefixWord ++ tailWord_570350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570449 : List Nat := [1, 2, 2, 1, 3, 1, 2, 4, 6]
def baseStart_570449 : Nat := 118140960795 + 570449 * 2 ^ 59
def prefixEnd_570449 : Nat := 4983230072969 + 3 ^ 40 * 570449 * 2
def baseEnd_570449 : Nat := 65092116861498633192013

theorem tailTrace_570449 : CollatzResearch.WordTrace tailWord_570449 prefixEnd_570449 65092116861498633192013 := by
  unfold tailWord_570449
  simp only [CollatzResearch.WordTrace]
  refine ⟨20805984310368172777914401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13870656206912115185276267 20805984310368172777914401)
  ·
    refine ⟨15604488232776129583435801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20805984310368172777914401 15604488232776129583435801)
    ·
      refine ⟨11703366174582097187576851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15604488232776129583435801 11703366174582097187576851)
      ·
        refine ⟨17555049261873145781365277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11703366174582097187576851 17555049261873145781365277)
        ·
          refine ⟨6583143473202429668011979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17555049261873145781365277 6583143473202429668011979)
          ·
            refine ⟨9874715209803644502017969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6583143473202429668011979 9874715209803644502017969)
            ·
              refine ⟨7406036407352733376513477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9874715209803644502017969 7406036407352733376513477)
              ·
                refine ⟨1388631826378637508096277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7406036407352733376513477 1388631826378637508096277)
                ·
                  refine ⟨65092116861498633192013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1388631826378637508096277 65092116861498633192013)
                  ·
                    rfl

theorem cell22_570449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 6].length) (baseStart_570449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570449 prefixEnd_570449 := by exact prefixLift 570449
  have htrace : WordTrace (prefixWord ++ tailWord_570449) baseStart_570449 baseEnd_570449 := by
    simpa [prefixWord, tailWord_570449, baseEnd_570449] using wordTrace_append hprefix tailTrace_570449
  have hstable : (prefixWord ++ tailWord_570449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570449).length < 2 ^ (prefixWord ++ tailWord_570449).sum := by decide
  have hdescent : baseEnd_570449 < baseStart_570449 := by decide
  rcases family_descends (prefixWord ++ tailWord_570449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570586 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 5, 4]
def baseStart_570586 : Nat := 118140960795 + 570586 * 2 ^ 59
def prefixEnd_570586 : Nat := 4983230072969 + 3 ^ 40 * 570586 * 2
def baseEnd_570586 : Nat := 195323248484273208900619

theorem tailTrace_570586 : CollatzResearch.WordTrace tailWord_570586 prefixEnd_570586 195323248484273208900619 := by
  unfold tailWord_570586
  simp only [CollatzResearch.WordTrace]
  refine ⟨5202745277717961293912903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13873987407247896783767741 5202745277717961293912903)
  ·
    refine ⟨7804117916576941940869355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5202745277717961293912903 7804117916576941940869355)
    ·
      refine ⟨11706176874865412911304033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7804117916576941940869355 11706176874865412911304033)
      ·
        refine ⟨8779632656149059683478025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11706176874865412911304033 8779632656149059683478025)
        ·
          refine ⟨6584724492111794762608519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8779632656149059683478025 6584724492111794762608519)
          ·
            refine ⟨9877086738167692143912779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6584724492111794762608519 9877086738167692143912779)
            ·
              refine ⟨14815630107251538215869169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9877086738167692143912779 14815630107251538215869169)
              ·
                refine ⟨11111722580438653661901877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14815630107251538215869169 11111722580438653661901877)
                ·
                  refine ⟨1041723991916123780803301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11111722580438653661901877 1041723991916123780803301)
                  ·
                    refine ⟨195323248484273208900619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1041723991916123780803301 195323248484273208900619)
                    ·
                      rfl

theorem cell22_570586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_570586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570586 prefixEnd_570586 := by exact prefixLift 570586
  have htrace : WordTrace (prefixWord ++ tailWord_570586) baseStart_570586 baseEnd_570586 := by
    simpa [prefixWord, tailWord_570586, baseEnd_570586] using wordTrace_append hprefix tailTrace_570586
  have hstable : (prefixWord ++ tailWord_570586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570586).length < 2 ^ (prefixWord ++ tailWord_570586).sum := by decide
  have hdescent : baseEnd_570586 < baseStart_570586 := by decide
  rcases family_descends (prefixWord ++ tailWord_570586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570607 : List Nat := [1, 1, 2, 1, 8, 1, 2, 1, 5]
def baseStart_570607 : Nat := 118140960795 + 570607 * 2 ^ 59
def prefixEnd_570607 : Nat := 4983230072969 + 3 ^ 40 * 570607 * 2
def baseEnd_570607 : Nat := 65110145737812051375185

theorem tailTrace_570607 : CollatzResearch.WordTrace tailWord_570607 prefixEnd_570607 65110145737812051375185 := by
  unfold tailWord_570607
  simp only [CollatzResearch.WordTrace]
  refine ⟨20811747043795765762166075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13874498029197177174777383 20811747043795765762166075)
  ·
    refine ⟨31217620565693648643249113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20811747043795765762166075 31217620565693648643249113)
    ·
      refine ⟨23413215424270236482436835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31217620565693648643249113 23413215424270236482436835)
      ·
        refine ⟨35119823136405354723655253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23413215424270236482436835 35119823136405354723655253)
        ·
          refine ⟨411560427379750250667835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 35119823136405354723655253 411560427379750250667835)
          ·
            refine ⟨617340641069625376001753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411560427379750250667835 617340641069625376001753)
            ·
              refine ⟨463005480802219032001315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 617340641069625376001753 463005480802219032001315)
              ·
                refine ⟨694508221203328548001973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463005480802219032001315 694508221203328548001973)
                ·
                  refine ⟨65110145737812051375185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 694508221203328548001973 65110145737812051375185)
                  ·
                    rfl

theorem cell22_570607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 5].length) (baseStart_570607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570607 prefixEnd_570607 := by exact prefixLift 570607
  have htrace : WordTrace (prefixWord ++ tailWord_570607) baseStart_570607 baseEnd_570607 := by
    simpa [prefixWord, tailWord_570607, baseEnd_570607] using wordTrace_append hprefix tailTrace_570607
  have hstable : (prefixWord ++ tailWord_570607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570607).length < 2 ^ (prefixWord ++ tailWord_570607).sum := by decide
  have hdescent : baseEnd_570607 < baseStart_570607 := by decide
  rcases family_descends (prefixWord ++ tailWord_570607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570648 : List Nat := [2, 1, 2, 3, 1, 3, 2, 2, 2, 4]
def baseStart_570648 : Nat := 118140960795 + 570648 * 2 ^ 59
def prefixEnd_570648 : Nat := 4983230072969 + 3 ^ 40 * 570648 * 2
def baseEnd_570648 : Nat := 195344472351325713850429

theorem tailTrace_570648 : CollatzResearch.WordTrace tailWord_570648 prefixEnd_570648 195344472351325713850429 := by
  unfold tailWord_570648
  simp only [CollatzResearch.WordTrace]
  refine ⟨10406621218323614882204299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13875494957764819842939065 10406621218323614882204299)
  ·
    refine ⟨15609931827485422323306449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10406621218323614882204299 15609931827485422323306449)
    ·
      refine ⟨11707448870614066742479837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15609931827485422323306449 11707448870614066742479837)
      ·
        refine ⟨4390293326480275028429939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11707448870614066742479837 4390293326480275028429939)
        ·
          refine ⟨6585439989720412542644909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4390293326480275028429939 6585439989720412542644909)
          ·
            refine ⟨2469539996145154703491841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6585439989720412542644909 2469539996145154703491841)
            ·
              refine ⟨1852154997108866027618881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2469539996145154703491841 1852154997108866027618881)
              ·
                refine ⟨1389116247831649520714161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1852154997108866027618881 1389116247831649520714161)
                ·
                  refine ⟨1041837185873737140535621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1389116247831649520714161 1041837185873737140535621)
                  ·
                    refine ⟨195344472351325713850429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1041837185873737140535621 195344472351325713850429)
                    ·
                      rfl

theorem cell22_570648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_570648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570648 prefixEnd_570648 := by exact prefixLift 570648
  have htrace : WordTrace (prefixWord ++ tailWord_570648) baseStart_570648 baseEnd_570648 := by
    simpa [prefixWord, tailWord_570648, baseEnd_570648] using wordTrace_append hprefix tailTrace_570648
  have hstable : (prefixWord ++ tailWord_570648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570648).length < 2 ^ (prefixWord ++ tailWord_570648).sum := by decide
  have hdescent : baseEnd_570648 < baseStart_570648 := by decide
  rcases family_descends (prefixWord ++ tailWord_570648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570650 : List Nat := [3, 1, 1, 3, 3, 1, 1, 4, 2, 3]
def baseStart_570650 : Nat := 118140960795 + 570650 * 2 ^ 59
def prefixEnd_570650 : Nat := 4983230072969 + 3 ^ 40 * 570650 * 2
def baseEnd_570650 : Nat := 195345156992198375300423

theorem tailTrace_570650 : CollatzResearch.WordTrace tailWord_570650 prefixEnd_570650 195345156992198375300423 := by
  unfold tailWord_570650
  simp only [CollatzResearch.WordTrace]
  refine ⟨5203328845659996026495351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13875543588426656070654269 5203328845659996026495351)
  ·
    refine ⟨7804993268489994039743027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5203328845659996026495351 7804993268489994039743027)
    ·
      refine ⟨11707489902734991059614541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7804993268489994039743027 11707489902734991059614541)
      ·
        refine ⟨4390308713525621647355453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11707489902734991059614541 4390308713525621647355453)
        ·
          refine ⟨1646365767572108117758295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4390308713525621647355453 1646365767572108117758295)
          ·
            refine ⟨2469548651358162176637443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1646365767572108117758295 2469548651358162176637443)
            ·
              refine ⟨3704322977037243264956165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469548651358162176637443 3704322977037243264956165)
              ·
                refine ⟨694560558194483112179281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3704322977037243264956165 694560558194483112179281)
                ·
                  refine ⟨520920418645862334134461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 694560558194483112179281 520920418645862334134461)
                  ·
                    refine ⟨195345156992198375300423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 520920418645862334134461 195345156992198375300423)
                    ·
                      rfl

theorem cell22_570650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_570650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570650 prefixEnd_570650 := by exact prefixLift 570650
  have htrace : WordTrace (prefixWord ++ tailWord_570650) baseStart_570650 baseEnd_570650 := by
    simpa [prefixWord, tailWord_570650, baseEnd_570650] using wordTrace_append hprefix tailTrace_570650
  have hstable : (prefixWord ++ tailWord_570650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570650).length < 2 ^ (prefixWord ++ tailWord_570650).sum := by decide
  have hdescent : baseEnd_570650 < baseStart_570650 := by decide
  rcases family_descends (prefixWord ++ tailWord_570650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570691 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 7]
def baseStart_570691 : Nat := 118140960795 + 570691 * 2 ^ 59
def prefixEnd_570691 : Nat := 4983230072969 + 3 ^ 40 * 570691 * 2
def baseEnd_570691 : Nat := 65119730710029311675099

theorem tailTrace_570691 : CollatzResearch.WordTrace tailWord_570691 prefixEnd_570691 65119730710029311675099 := by
  unfold tailWord_570691
  simp only [CollatzResearch.WordTrace]
  refine ⟨20814810775491448108223927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13876540516994298738815951 20814810775491448108223927)
  ·
    refine ⟨31222216163237172162335891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20814810775491448108223927 31222216163237172162335891)
    ·
      refine ⟨46833324244855758243503837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31222216163237172162335891 46833324244855758243503837)
      ·
        refine ⟨17562496591820909341313939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46833324244855758243503837 17562496591820909341313939)
        ·
          refine ⟨26343744887731364011970909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17562496591820909341313939 26343744887731364011970909)
          ·
            refine ⟨9878904332899261504489091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26343744887731364011970909 9878904332899261504489091)
            ·
              refine ⟨14818356499348892256733637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9878904332899261504489091 14818356499348892256733637)
              ·
                refine ⟨2778441843627917298137557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14818356499348892256733637 2778441843627917298137557)
                ·
                  refine ⟨65119730710029311675099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2778441843627917298137557 65119730710029311675099)
                  ·
                    rfl

theorem cell22_570691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 7].length) (baseStart_570691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570691 prefixEnd_570691 := by exact prefixLift 570691
  have htrace : WordTrace (prefixWord ++ tailWord_570691) baseStart_570691 baseEnd_570691 := by
    simpa [prefixWord, tailWord_570691, baseEnd_570691] using wordTrace_append hprefix tailTrace_570691
  have hstable : (prefixWord ++ tailWord_570691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570691).length < 2 ^ (prefixWord ++ tailWord_570691).sum := by decide
  have hdescent : baseEnd_570691 < baseStart_570691 := by decide
  rcases family_descends (prefixWord ++ tailWord_570691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570701 : List Nat := [1, 6, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_570701 : Nat := 118140960795 + 570701 * 2 ^ 59
def prefixEnd_570701 : Nat := 4983230072969 + 3 ^ 40 * 570701 * 2
def baseEnd_570701 : Nat := 195362615334451242275267

theorem tailTrace_570701 : CollatzResearch.WordTrace tailWord_570701 prefixEnd_570701 195362615334451242275267 := by
  unfold tailWord_570701
  simp only [CollatzResearch.WordTrace]
  refine ⟨20815175505455219816087957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13876783670303479877391971 20815175505455219816087957)
  ·
    refine ⟨975711351818213428879123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20815175505455219816087957 975711351818213428879123)
    ·
      refine ⟨1463567027727320143318685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 975711351818213428879123 1463567027727320143318685)
      ·
        refine ⟨548837635397745053744507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1463567027727320143318685 548837635397745053744507)
        ·
          refine ⟨823256453096617580616761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548837635397745053744507 823256453096617580616761)
          ·
            refine ⟨617442339822463185462571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 823256453096617580616761 617442339822463185462571)
            ·
              refine ⟨926163509733694778193857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 617442339822463185462571 926163509733694778193857)
              ·
                refine ⟨694622632300271083645393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 926163509733694778193857 694622632300271083645393)
                ·
                  refine ⟨520966974225203312734045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 694622632300271083645393 520966974225203312734045)
                  ·
                    refine ⟨195362615334451242275267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 520966974225203312734045 195362615334451242275267)
                    ·
                      rfl

theorem cell22_570701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_570701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570701 prefixEnd_570701 := by exact prefixLift 570701
  have htrace : WordTrace (prefixWord ++ tailWord_570701) baseStart_570701 baseEnd_570701 := by
    simpa [prefixWord, tailWord_570701, baseEnd_570701] using wordTrace_append hprefix tailTrace_570701
  have hstable : (prefixWord ++ tailWord_570701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570701).length < 2 ^ (prefixWord ++ tailWord_570701).sum := by decide
  have hdescent : baseEnd_570701 < baseStart_570701 := by decide
  rcases family_descends (prefixWord ++ tailWord_570701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570708 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 7]
def baseStart_570708 : Nat := 118140960795 + 570708 * 2 ^ 59
def prefixEnd_570708 : Nat := 4983230072969 + 3 ^ 40 * 570708 * 2
def baseEnd_570708 : Nat := 65121670525835185783415

theorem tailTrace_570708 : CollatzResearch.WordTrace tailWord_570708 prefixEnd_570708 65121670525835185783415 := by
  unfold tailWord_570708
  simp only [CollatzResearch.WordTrace]
  refine ⟨10407715408214930005796389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13876953877619906674395185 10407715408214930005796389)
  ·
    refine ⟨1951446639040299376086823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10407715408214930005796389 1951446639040299376086823)
    ·
      refine ⟨2927169958560449064130235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1951446639040299376086823 2927169958560449064130235)
      ·
        refine ⟨4390754937840673596195353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2927169958560449064130235 4390754937840673596195353)
        ·
          refine ⟨3293066203380505197146515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4390754937840673596195353 3293066203380505197146515)
          ·
            refine ⟨4939599305070757795719773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3293066203380505197146515 4939599305070757795719773)
            ·
              refine ⟨1852349739401534173394915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4939599305070757795719773 1852349739401534173394915)
              ·
                refine ⟨2778524609102301260092373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1852349739401534173394915 2778524609102301260092373)
                ·
                  refine ⟨65121670525835185783415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2778524609102301260092373 65121670525835185783415)
                  ·
                    rfl

theorem cell22_570708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_570708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570708 prefixEnd_570708 := by exact prefixLift 570708
  have htrace : WordTrace (prefixWord ++ tailWord_570708) baseStart_570708 baseEnd_570708 := by
    simpa [prefixWord, tailWord_570708, baseEnd_570708] using wordTrace_append hprefix tailTrace_570708
  have hstable : (prefixWord ++ tailWord_570708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570708).length < 2 ^ (prefixWord ++ tailWord_570708).sum := by decide
  have hdescent : baseEnd_570708 < baseStart_570708 := by decide
  rcases family_descends (prefixWord ++ tailWord_570708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570723 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 2, 5]
def baseStart_570723 : Nat := 118140960795 + 570723 * 2 ^ 59
def prefixEnd_570723 : Nat := 4983230072969 + 3 ^ 40 * 570723 * 2
def baseEnd_570723 : Nat := 195370146384050518225199

theorem tailTrace_570723 : CollatzResearch.WordTrace tailWord_570723 prefixEnd_570723 195370146384050518225199 := by
  unfold tailWord_570723
  simp only [CollatzResearch.WordTrace]
  refine ⟨20815977911375517573388823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13877318607583678382259215 20815977911375517573388823)
  ·
    refine ⟨31223966867063276360083235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20815977911375517573388823 31223966867063276360083235)
    ·
      refine ⟨46835950300594914540124853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31223966867063276360083235 46835950300594914540124853)
      ·
        refine ⟨4390870340680773238136705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46835950300594914540124853 4390870340680773238136705)
        ·
          refine ⟨3293152755510579928602529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4390870340680773238136705 3293152755510579928602529)
          ·
            refine ⟨2469864566632934946451897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3293152755510579928602529 2469864566632934946451897)
            ·
              refine ⟨1852398424974701209838923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2469864566632934946451897 1852398424974701209838923)
              ·
                refine ⟨2778597637462051814758385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1852398424974701209838923 2778597637462051814758385)
                ·
                  refine ⟨2083948228096538861068789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2778597637462051814758385 2083948228096538861068789)
                  ·
                    refine ⟨195370146384050518225199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2083948228096538861068789 195370146384050518225199)
                    ·
                      rfl

theorem cell22_570723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 5].length) (baseStart_570723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570723 prefixEnd_570723 := by exact prefixLift 570723
  have htrace : WordTrace (prefixWord ++ tailWord_570723) baseStart_570723 baseEnd_570723 := by
    simpa [prefixWord, tailWord_570723, baseEnd_570723] using wordTrace_append hprefix tailTrace_570723
  have hstable : (prefixWord ++ tailWord_570723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570723).length < 2 ^ (prefixWord ++ tailWord_570723).sum := by decide
  have hdescent : baseEnd_570723 < baseStart_570723 := by decide
  rcases family_descends (prefixWord ++ tailWord_570723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570725 : List Nat := [1, 3, 1, 3, 1, 2, 5, 1, 5]
def baseStart_570725 : Nat := 118140960795 + 570725 * 2 ^ 59
def prefixEnd_570725 : Nat := 4983230072969 + 3 ^ 40 * 570725 * 2
def baseEnd_570725 : Nat := 65123610341641059891731

theorem tailTrace_570725 : CollatzResearch.WordTrace tailWord_570725 prefixEnd_570725 65123610341641059891731 := by
  unfold tailWord_570725
  simp only [CollatzResearch.WordTrace]
  refine ⟨20816050857368271914961629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13877367238245514609974419 20816050857368271914961629)
  ·
    refine ⟨7806019071513101968110611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20816050857368271914961629 7806019071513101968110611)
    ·
      refine ⟨11709028607269652952165917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7806019071513101968110611 11709028607269652952165917)
      ·
        refine ⟨4390885727726119857062219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11709028607269652952165917 4390885727726119857062219)
        ·
          refine ⟨6586328591589179785593329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4390885727726119857062219 6586328591589179785593329)
          ·
            refine ⟨4939746443691884839194997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6586328591589179785593329 4939746443691884839194997)
            ·
              refine ⟨463101229096114203674531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4939746443691884839194997 463101229096114203674531)
              ·
                refine ⟨694651843644171305511797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463101229096114203674531 694651843644171305511797)
                ·
                  refine ⟨65123610341641059891731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 694651843644171305511797 65123610341641059891731)
                  ·
                    rfl

theorem cell22_570725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_570725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570725 prefixEnd_570725 := by exact prefixLift 570725
  have htrace : WordTrace (prefixWord ++ tailWord_570725) baseStart_570725 baseEnd_570725 := by
    simpa [prefixWord, tailWord_570725, baseEnd_570725] using wordTrace_append hprefix tailTrace_570725
  have hstable : (prefixWord ++ tailWord_570725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570725).length < 2 ^ (prefixWord ++ tailWord_570725).sum := by decide
  have hdescent : baseEnd_570725 < baseStart_570725 := by decide
  rcases family_descends (prefixWord ++ tailWord_570725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570755 : List Nat := [1, 1, 1, 3, 5, 1, 2, 3, 1, 4]
def baseStart_570755 : Nat := 118140960795 + 570755 * 2 ^ 59
def prefixEnd_570755 : Nat := 4983230072969 + 3 ^ 40 * 570755 * 2
def baseEnd_570755 : Nat := 195381100638013101425101

theorem tailTrace_570755 : CollatzResearch.WordTrace tailWord_570755 prefixEnd_570755 195381100638013101425101 := by
  unfold tailWord_570755
  simp only [CollatzResearch.WordTrace]
  refine ⟨20817145047259587038553719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13878096698173058025702479 20817145047259587038553719)
  ·
    refine ⟨31225717570889380557830579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20817145047259587038553719 31225717570889380557830579)
    ·
      refine ⟨46838576356334070836745869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31225717570889380557830579 46838576356334070836745869)
      ·
        refine ⟨17564466133625276563779701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46838576356334070836745869 17564466133625276563779701)
        ·
          refine ⟨1646668700027369677854347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17564466133625276563779701 1646668700027369677854347)
          ·
            refine ⟨2470003050041054516781521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1646668700027369677854347 2470003050041054516781521)
            ·
              refine ⟨1852502287530790887586141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2470003050041054516781521 1852502287530790887586141)
              ·
                refine ⟨694688357824046582844803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1852502287530790887586141 694688357824046582844803)
                ·
                  refine ⟨1042032536736069874267205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 694688357824046582844803 1042032536736069874267205)
                  ·
                    refine ⟨195381100638013101425101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1042032536736069874267205 195381100638013101425101)
                    ·
                      rfl

theorem cell22_570755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 4].length) (baseStart_570755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570755 prefixEnd_570755 := by exact prefixLift 570755
  have htrace : WordTrace (prefixWord ++ tailWord_570755) baseStart_570755 baseEnd_570755 := by
    simpa [prefixWord, tailWord_570755, baseEnd_570755] using wordTrace_append hprefix tailTrace_570755
  have hstable : (prefixWord ++ tailWord_570755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570755).length < 2 ^ (prefixWord ++ tailWord_570755).sum := by decide
  have hdescent : baseEnd_570755 < baseStart_570755 := by decide
  rcases family_descends (prefixWord ++ tailWord_570755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570864 : List Nat := [2, 1, 1, 1, 3, 5, 2, 3, 1, 3]
def baseStart_570864 : Nat := 118140960795 + 570864 * 2 ^ 59
def prefixEnd_570864 : Nat := 4983230072969 + 3 ^ 40 * 570864 * 2
def baseEnd_570864 : Nat := 195418413565573150449767

theorem tailTrace_570864 : CollatzResearch.WordTrace tailWord_570864 prefixEnd_570864 195418413565573150449767 := by
  unfold tailWord_570864
  simp only [CollatzResearch.WordTrace]
  refine ⟨10410560301932349327135823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13880747069243132436181097 10410560301932349327135823)
  ·
    refine ⟨15615840452898523990703735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10410560301932349327135823 15615840452898523990703735)
    ·
      refine ⟨23423760679347785986055603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15615840452898523990703735 23423760679347785986055603)
      ·
        refine ⟨35135641019021678979083405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23423760679347785986055603 35135641019021678979083405)
        ·
          refine ⟨13175865382133129617156277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35135641019021678979083405 13175865382133129617156277)
          ·
            refine ⟨1235237379574980901608401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13175865382133129617156277 1235237379574980901608401)
            ·
              refine ⟨926428034681235676206301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1235237379574980901608401 926428034681235676206301)
              ·
                refine ⟨347410513005463378577363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 926428034681235676206301 347410513005463378577363)
                ·
                  refine ⟨521115769508195067866045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 347410513005463378577363 521115769508195067866045)
                  ·
                    refine ⟨195418413565573150449767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 521115769508195067866045 195418413565573150449767)
                    ·
                      rfl

theorem cell22_570864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 1, 3].length) (baseStart_570864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570864 prefixEnd_570864 := by exact prefixLift 570864
  have htrace : WordTrace (prefixWord ++ tailWord_570864) baseStart_570864 baseEnd_570864 := by
    simpa [prefixWord, tailWord_570864, baseEnd_570864] using wordTrace_append hprefix tailTrace_570864
  have hstable : (prefixWord ++ tailWord_570864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570864).length < 2 ^ (prefixWord ++ tailWord_570864).sum := by decide
  have hdescent : baseEnd_570864 < baseStart_570864 := by decide
  rcases family_descends (prefixWord ++ tailWord_570864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570877 : List Nat := [1, 4, 1, 1, 1, 6, 1, 2, 5]
def baseStart_570877 : Nat := 118140960795 + 570877 * 2 ^ 59
def prefixEnd_570877 : Nat := 4983230072969 + 3 ^ 40 * 570877 * 2
def baseEnd_570877 : Nat := 65140954577081816624909

theorem tailTrace_570877 : CollatzResearch.WordTrace tailWord_570877 prefixEnd_570877 65140954577081816624909 := by
  unfold tailWord_570877
  simp only [CollatzResearch.WordTrace]
  refine ⟨20821594752817601874494885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13881063168545067916329923 20821594752817601874494885)
  ·
    refine ⟨3904049016153300351467791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20821594752817601874494885 3904049016153300351467791)
    ·
      refine ⟨5856073524229950527201687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3904049016153300351467791 5856073524229950527201687)
      ·
        refine ⟨8784110286344925790802531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5856073524229950527201687 8784110286344925790802531)
        ·
          refine ⟨13176165429517388686203797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8784110286344925790802531 13176165429517388686203797)
          ·
            refine ⟨617632754508627594665803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13176165429517388686203797 617632754508627594665803)
            ·
              refine ⟨926449131762941391998705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 617632754508627594665803 926449131762941391998705)
              ·
                refine ⟨694836848822206043999029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 926449131762941391998705 694836848822206043999029)
                ·
                  refine ⟨65140954577081816624909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 694836848822206043999029 65140954577081816624909)
                  ·
                    rfl

theorem cell22_570877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_570877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570877 prefixEnd_570877 := by exact prefixLift 570877
  have htrace : WordTrace (prefixWord ++ tailWord_570877) baseStart_570877 baseEnd_570877 := by
    simpa [prefixWord, tailWord_570877, baseEnd_570877] using wordTrace_append hprefix tailTrace_570877
  have hstable : (prefixWord ++ tailWord_570877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570877).length < 2 ^ (prefixWord ++ tailWord_570877).sum := by decide
  have hdescent : baseEnd_570877 < baseStart_570877 := by decide
  rcases family_descends (prefixWord ++ tailWord_570877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570894 : List Nat := [4, 1, 1, 2, 4, 1, 3, 1, 5]
def baseStart_570894 : Nat := 118140960795 + 570894 * 2 ^ 59
def prefixEnd_570894 : Nat := 4983230072969 + 3 ^ 40 * 570894 * 2
def baseEnd_570894 : Nat := 65142894392887690733225

theorem tailTrace_570894 : CollatzResearch.WordTrace tailWord_570894 prefixEnd_570894 65142894392887690733225 := by
  unfold tailWord_570894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2602776849219501722232967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13881476529170675851909157 2602776849219501722232967)
  ·
    refine ⟨3904165273829252583349451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2602776849219501722232967 3904165273829252583349451)
    ·
      refine ⟨5856247910743878875024177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3904165273829252583349451 5856247910743878875024177)
      ·
        refine ⟨4392185933057909156268133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5856247910743878875024177 4392185933057909156268133)
        ·
          refine ⟨823534862448357966800275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4392185933057909156268133 823534862448357966800275)
          ·
            refine ⟨1235302293672536950200413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823534862448357966800275 1235302293672536950200413)
            ·
              refine ⟨463238360127201356325155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1235302293672536950200413 463238360127201356325155)
              ·
                refine ⟨694857540190802034487733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463238360127201356325155 694857540190802034487733)
                ·
                  refine ⟨65142894392887690733225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 694857540190802034487733 65142894392887690733225)
                  ·
                    rfl

theorem cell22_570894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_570894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570894 prefixEnd_570894 := by exact prefixLift 570894
  have htrace : WordTrace (prefixWord ++ tailWord_570894) baseStart_570894 baseEnd_570894 := by
    simpa [prefixWord, tailWord_570894, baseEnd_570894] using wordTrace_append hprefix tailTrace_570894
  have hstable : (prefixWord ++ tailWord_570894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570894).length < 2 ^ (prefixWord ++ tailWord_570894).sum := by decide
  have hdescent : baseEnd_570894 < baseStart_570894 := by decide
  rcases family_descends (prefixWord ++ tailWord_570894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570935 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 4, 4]
def baseStart_570935 : Nat := 118140960795 + 570935 * 2 ^ 59
def prefixEnd_570935 : Nat := 4983230072969 + 3 ^ 40 * 570935 * 2
def baseEnd_570935 : Nat := 195442718316552631924549

theorem tailTrace_570935 : CollatzResearch.WordTrace tailWord_570935 prefixEnd_570935 195442718316552631924549 := by
  unfold tailWord_570935
  simp only [CollatzResearch.WordTrace]
  refine ⟨20823710186607477780106259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13882473457738318520070839 20823710186607477780106259)
  ·
    refine ⟨31235565279911216670159389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20823710186607477780106259 31235565279911216670159389)
    ·
      refine ⟨11713336979966706251309771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31235565279911216670159389 11713336979966706251309771)
      ·
        refine ⟨17570005469950059376964657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11713336979966706251309771 17570005469950059376964657)
        ·
          refine ⟨13177504102462544532723493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17570005469950059376964657 13177504102462544532723493)
          ·
            refine ⟨2470782019211727099885655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13177504102462544532723493 2470782019211727099885655)
            ·
              refine ⟨3706173028817590649828483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2470782019211727099885655 3706173028817590649828483)
              ·
                refine ⟨5559259543226385974742725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3706173028817590649828483 5559259543226385974742725)
                ·
                  refine ⟨1042361164354947370264261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5559259543226385974742725 1042361164354947370264261)
                  ·
                    refine ⟨195442718316552631924549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1042361164354947370264261 195442718316552631924549)
                    ·
                      rfl

theorem cell22_570935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_570935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570935 prefixEnd_570935 := by exact prefixLift 570935
  have htrace : WordTrace (prefixWord ++ tailWord_570935) baseStart_570935 baseEnd_570935 := by
    simpa [prefixWord, tailWord_570935, baseEnd_570935] using wordTrace_append hprefix tailTrace_570935
  have hstable : (prefixWord ++ tailWord_570935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570935).length < 2 ^ (prefixWord ++ tailWord_570935).sum := by decide
  have hdescent : baseEnd_570935 < baseStart_570935 := by decide
  rcases family_descends (prefixWord ++ tailWord_570935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570937 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 4, 3]
def baseStart_570937 : Nat := 118140960795 + 570937 * 2 ^ 59
def prefixEnd_570937 : Nat := 4983230072969 + 3 ^ 40 * 570937 * 2
def baseEnd_570937 : Nat := 195443402957425293374543

theorem tailTrace_570937 : CollatzResearch.WordTrace tailWord_570937 prefixEnd_570937 195443402957425293374543 := by
  unfold tailWord_570937
  simp only [CollatzResearch.WordTrace]
  refine ⟨20823783132600232121679065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13882522088400154747786043 20823783132600232121679065)
  ·
    refine ⟨15617837349450174091259299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20823783132600232121679065 15617837349450174091259299)
    ·
      refine ⟨23426756024175261136888949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15617837349450174091259299 23426756024175261136888949)
      ·
        refine ⟨2196258377266430731583339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23426756024175261136888949 2196258377266430731583339)
        ·
          refine ⟨3294387565899646097375009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2196258377266430731583339 3294387565899646097375009)
          ·
            refine ⟨2470790674424734573031257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3294387565899646097375009 2470790674424734573031257)
            ·
              refine ⟨1853093005818550929773443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2470790674424734573031257 1853093005818550929773443)
              ·
                refine ⟨2779639508727826394660165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1853093005818550929773443 2779639508727826394660165)
                ·
                  refine ⟨521182407886467448998781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2779639508727826394660165 521182407886467448998781)
                  ·
                    refine ⟨195443402957425293374543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 521182407886467448998781 195443402957425293374543)
                    ·
                      rfl

theorem cell22_570937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 3].length) (baseStart_570937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570937 prefixEnd_570937 := by exact prefixLift 570937
  have htrace : WordTrace (prefixWord ++ tailWord_570937) baseStart_570937 baseEnd_570937 := by
    simpa [prefixWord, tailWord_570937, baseEnd_570937] using wordTrace_append hprefix tailTrace_570937
  have hstable : (prefixWord ++ tailWord_570937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570937).length < 2 ^ (prefixWord ++ tailWord_570937).sum := by decide
  have hdescent : baseEnd_570937 < baseStart_570937 := by decide
  rcases family_descends (prefixWord ++ tailWord_570937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570997 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 2, 6]
def baseStart_570997 : Nat := 118140960795 + 570997 * 2 ^ 59
def prefixEnd_570997 : Nat := 4983230072969 + 3 ^ 40 * 570997 * 2
def baseEnd_570997 : Nat := 195463942183605136874359

theorem tailTrace_570997 : CollatzResearch.WordTrace tailWord_570997 prefixEnd_570997 195463942183605136874359 := by
  unfold tailWord_570997
  simp only [CollatzResearch.WordTrace]
  refine ⟨20825971512382862368863245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13883981008255241579242163 20825971512382862368863245)
  ·
    refine ⟨7809739317143573388323717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20825971512382862368863245 7809739317143573388323717)
    ·
      refine ⟨1464326121964420010310697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7809739317143573388323717 1464326121964420010310697)
      ·
        refine ⟨1098244591473315007733023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1464326121964420010310697 1098244591473315007733023)
        ·
          refine ⟨1647366887209972511599535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1098244591473315007733023 1647366887209972511599535)
          ·
            refine ⟨2471050330814958767399303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1647366887209972511599535 2471050330814958767399303)
            ·
              refine ⟨3706575496222438151098955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2471050330814958767399303 3706575496222438151098955)
              ·
                refine ⟨5559863244333657226648433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3706575496222438151098955 5559863244333657226648433)
                ·
                  refine ⟨4169897433250242919986325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5559863244333657226648433 4169897433250242919986325)
                  ·
                    refine ⟨195463942183605136874359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4169897433250242919986325 195463942183605136874359)
                    ·
                      rfl

theorem cell22_570997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_570997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_570997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_570997 prefixEnd_570997 := by exact prefixLift 570997
  have htrace : WordTrace (prefixWord ++ tailWord_570997) baseStart_570997 baseEnd_570997 := by
    simpa [prefixWord, tailWord_570997, baseEnd_570997] using wordTrace_append hprefix tailTrace_570997
  have hstable : (prefixWord ++ tailWord_570997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570997).length < 2 ^ (prefixWord ++ tailWord_570997).sum := by decide
  have hdescent : baseEnd_570997 < baseStart_570997 := by decide
  rcases family_descends (prefixWord ++ tailWord_570997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571016 : List Nat := [2, 1, 3, 5, 1, 1, 1, 2, 3, 3]
def baseStart_571016 : Nat := 118140960795 + 571016 * 2 ^ 59
def prefixEnd_571016 : Nat := 4983230072969 + 3 ^ 40 * 571016 * 2
def baseEnd_571016 : Nat := 195470446271895420649301

theorem tailTrace_571016 : CollatzResearch.WordTrace tailWord_571016 prefixEnd_571016 195470446271895420649301 := by
  unfold tailWord_571016
  simp only [CollatzResearch.WordTrace]
  refine ⟨10413332249657014306902451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13884442999542685742536601 10413332249657014306902451)
  ·
    refine ⟨15619998374485521460353677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10413332249657014306902451 15619998374485521460353677)
    ·
      refine ⟨5857499390432070547632629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15619998374485521460353677 5857499390432070547632629)
      ·
        refine ⟨549140567853006613840559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5857499390432070547632629 549140567853006613840559)
        ·
          refine ⟨823710851779509920760839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549140567853006613840559 823710851779509920760839)
          ·
            refine ⟨1235566277669264881141259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823710851779509920760839 1235566277669264881141259)
            ·
              refine ⟨1853349416503897321711889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235566277669264881141259 1853349416503897321711889)
              ·
                refine ⟨1390012062377922991283917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1853349416503897321711889 1390012062377922991283917)
                ·
                  refine ⟨521254523391721121731469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1390012062377922991283917 521254523391721121731469)
                  ·
                    refine ⟨195470446271895420649301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 521254523391721121731469 195470446271895420649301)
                    ·
                      rfl

theorem cell22_571016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_571016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_571016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_571016 prefixEnd_571016 := by exact prefixLift 571016
  have htrace : WordTrace (prefixWord ++ tailWord_571016) baseStart_571016 baseEnd_571016 := by
    simpa [prefixWord, tailWord_571016, baseEnd_571016] using wordTrace_append hprefix tailTrace_571016
  have hstable : (prefixWord ++ tailWord_571016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571016).length < 2 ^ (prefixWord ++ tailWord_571016).sum := by decide
  have hdescent : baseEnd_571016 < baseStart_571016 := by decide
  rcases family_descends (prefixWord ++ tailWord_571016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571164 : List Nat := [2, 2, 3, 1, 1, 2, 4, 2, 5]
def baseStart_571164 : Nat := 118140960795 + 571164 * 2 ^ 59
def prefixEnd_571164 : Nat := 4983230072969 + 3 ^ 40 * 571164 * 2
def baseEnd_571164 : Nat := 65173703232157455982949

theorem tailTrace_571164 : CollatzResearch.WordTrace tailWord_571164 prefixEnd_571164 65173703232157455982949 := by
  unfold tailWord_571164
  simp only [CollatzResearch.WordTrace]
  refine ⟨10416031251388924945096273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13888041668518566593461697 10416031251388924945096273)
  ·
    refine ⟨7812023438541693708822205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10416031251388924945096273 7812023438541693708822205)
    ·
      refine ⟨2929508789453135140808327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7812023438541693708822205 2929508789453135140808327)
      ·
        refine ⟨4394263184179702711212491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2929508789453135140808327 4394263184179702711212491)
        ·
          refine ⟨6591394776269554066818737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4394263184179702711212491 6591394776269554066818737)
          ·
            refine ⟨4943546082202165550114053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6591394776269554066818737 4943546082202165550114053)
            ·
              refine ⟨926914890412906040646385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4943546082202165550114053 926914890412906040646385)
              ·
                refine ⟨695186167809679530484789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 926914890412906040646385 695186167809679530484789)
                ·
                  refine ⟨65173703232157455982949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 695186167809679530484789 65173703232157455982949)
                  ·
                    rfl

theorem cell22_571164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_571164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_571164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_571164 prefixEnd_571164 := by exact prefixLift 571164
  have htrace : WordTrace (prefixWord ++ tailWord_571164) baseStart_571164 baseEnd_571164 := by
    simpa [prefixWord, tailWord_571164, baseEnd_571164] using wordTrace_append hprefix tailTrace_571164
  have hstable : (prefixWord ++ tailWord_571164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571164).length < 2 ^ (prefixWord ++ tailWord_571164).sum := by decide
  have hdescent : baseEnd_571164 < baseStart_571164 := by decide
  rcases family_descends (prefixWord ++ tailWord_571164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571192 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 8]
def baseStart_571192 : Nat := 118140960795 + 571192 * 2 ^ 59
def prefixEnd_571192 : Nat := 4983230072969 + 3 ^ 40 * 571192 * 2
def baseEnd_571192 : Nat := 65176898222896542749587

theorem tailTrace_571192 : CollatzResearch.WordTrace tailWord_571192 prefixEnd_571192 65176898222896542749587 := by
  unfold tailWord_571192
  simp only [CollatzResearch.WordTrace]
  refine ⟨10416541873338205336105915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13888722497784273781474553 10416541873338205336105915)
  ·
    refine ⟨15624812810007308004158873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10416541873338205336105915 15624812810007308004158873)
    ·
      refine ⟨11718609607505481003119155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15624812810007308004158873 11718609607505481003119155)
      ·
        refine ⟨17577914411258221504678733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11718609607505481003119155 17577914411258221504678733)
        ·
          refine ⟨6591717904221833064254525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17577914411258221504678733 6591717904221833064254525)
          ·
            refine ⟨2471894214083187399095447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6591717904221833064254525 2471894214083187399095447)
            ·
              refine ⟨3707841321124781098643171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2471894214083187399095447 3707841321124781098643171)
              ·
                refine ⟨5561761981687171647964757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3707841321124781098643171 5561761981687171647964757)
                ·
                  refine ⟨65176898222896542749587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5561761981687171647964757 65176898222896542749587)
                  ·
                    rfl

theorem cell22_571192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 8].length) (baseStart_571192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_571192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_571192 prefixEnd_571192 := by exact prefixLift 571192
  have htrace : WordTrace (prefixWord ++ tailWord_571192) baseStart_571192 baseEnd_571192 := by
    simpa [prefixWord, tailWord_571192, baseEnd_571192] using wordTrace_append hprefix tailTrace_571192
  have hstable : (prefixWord ++ tailWord_571192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571192).length < 2 ^ (prefixWord ++ tailWord_571192).sum := by decide
  have hdescent : baseEnd_571192 < baseStart_571192 := by decide
  rcases family_descends (prefixWord ++ tailWord_571192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571194 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 3, 4]
def baseStart_571194 : Nat := 118140960795 + 571194 * 2 ^ 59
def prefixEnd_571194 : Nat := 4983230072969 + 3 ^ 40 * 571194 * 2
def baseEnd_571194 : Nat := 195531379309562289698755

theorem tailTrace_571194 : CollatzResearch.WordTrace tailWord_571194 prefixEnd_571194 195531379309562289698755 := by
  unfold tailWord_571194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5208289173167291253446159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13888771128446110009189757 5208289173167291253446159)
  ·
    refine ⟨7812433759750936880169239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5208289173167291253446159 7812433759750936880169239)
    ·
      refine ⟨11718650639626405320253859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7812433759750936880169239 11718650639626405320253859)
      ·
        refine ⟨17577975959439607980380789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11718650639626405320253859 17577975959439607980380789)
        ·
          refine ⟨1647935246197463248160699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17577975959439607980380789 1647935246197463248160699)
          ·
            refine ⟨2471902869296194872241049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1647935246197463248160699 2471902869296194872241049)
            ·
              refine ⟨1853927151972146154180787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2471902869296194872241049 1853927151972146154180787)
              ·
                refine ⟨2780890727958219231271181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1853927151972146154180787 2780890727958219231271181)
                ·
                  refine ⟨1042834022984332211726693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2780890727958219231271181 1042834022984332211726693)
                  ·
                    refine ⟨195531379309562289698755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1042834022984332211726693 195531379309562289698755)
                    ·
                      rfl

theorem cell22_571194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_571194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_571194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_571194 prefixEnd_571194 := by exact prefixLift 571194
  have htrace : WordTrace (prefixWord ++ tailWord_571194) baseStart_571194 baseEnd_571194 := by
    simpa [prefixWord, tailWord_571194, baseEnd_571194] using wordTrace_append hprefix tailTrace_571194
  have hstable : (prefixWord ++ tailWord_571194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571194).length < 2 ^ (prefixWord ++ tailWord_571194).sum := by decide
  have hdescent : baseEnd_571194 < baseStart_571194 := by decide
  rcases family_descends (prefixWord ++ tailWord_571194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571237 : List Nat := [1, 3, 1, 3, 1, 1, 1, 11]
def baseStart_571237 : Nat := 118140960795 + 571237 * 2 ^ 59
def prefixEnd_571237 : Nat := 4983230072969 + 3 ^ 40 * 571237 * 2
def baseEnd_571237 : Nat := 21727344343147167874847

theorem tailTrace_571237 : CollatzResearch.WordTrace tailWord_571237 prefixEnd_571237 21727344343147167874847 := by
  unfold tailWord_571237
  simp only [CollatzResearch.WordTrace]
  refine ⟨20834725031513383357599965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13889816687675588905066643 20834725031513383357599965)
  ·
    refine ⟨7813021886817518759099987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20834725031513383357599965 7813021886817518759099987)
    ·
      refine ⟨11719532830226278138649981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7813021886817518759099987 11719532830226278138649981)
      ·
        refine ⟨4394824811334854301993743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11719532830226278138649981 4394824811334854301993743)
        ·
          refine ⟨6592237217002281452990615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4394824811334854301993743 6592237217002281452990615)
          ·
            refine ⟨9888355825503422179485923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6592237217002281452990615 9888355825503422179485923)
            ·
              refine ⟨14832533738255133269228885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9888355825503422179485923 14832533738255133269228885)
              ·
                refine ⟨21727344343147167874847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 14832533738255133269228885 21727344343147167874847)
                ·
                  rfl

theorem cell22_571237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 11].length) (baseStart_571237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_571237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_571237 prefixEnd_571237 := by exact prefixLift 571237
  have htrace : WordTrace (prefixWord ++ tailWord_571237) baseStart_571237 baseEnd_571237 := by
    simpa [prefixWord, tailWord_571237, baseEnd_571237] using wordTrace_append hprefix tailTrace_571237
  have hstable : (prefixWord ++ tailWord_571237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571237).length < 2 ^ (prefixWord ++ tailWord_571237).sum := by decide
  have hdescent : baseEnd_571237 < baseStart_571237 := by decide
  rcases family_descends (prefixWord ++ tailWord_571237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571271 : List Nat := [1, 1, 4, 2, 5, 1, 8]
def baseStart_571271 : Nat := 118140960795 + 571271 * 2 ^ 59
def prefixEnd_571271 : Nat := 4983230072969 + 3 ^ 40 * 571271 * 2
def baseEnd_571271 : Nat := 7242879184561472426797

theorem tailTrace_571271 : CollatzResearch.WordTrace tailWord_571271 prefixEnd_571271 7242879184561472426797 := by
  unfold tailWord_571271
  simp only [CollatzResearch.WordTrace]
  refine ⟨20835965113390207164337667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13890643408926804776225111 20835965113390207164337667)
  ·
    refine ⟨31253947670085310746506501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20835965113390207164337667 31253947670085310746506501)
    ·
      refine ⟨5860115188140995764969969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31253947670085310746506501 5860115188140995764969969)
      ·
        refine ⟨4395086391105746823727477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5860115188140995764969969 4395086391105746823727477)
        ·
          refine ⟨412039349166163764724451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4395086391105746823727477 412039349166163764724451)
          ·
            refine ⟨618059023749245647086677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412039349166163764724451 618059023749245647086677)
            ·
              refine ⟨7242879184561472426797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 618059023749245647086677 7242879184561472426797)
              ·
                rfl

theorem cell22_571271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 8].length) (baseStart_571271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_571271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_571271 prefixEnd_571271 := by exact prefixLift 571271
  have htrace : WordTrace (prefixWord ++ tailWord_571271) baseStart_571271 baseEnd_571271 := by
    simpa [prefixWord, tailWord_571271, baseEnd_571271] using wordTrace_append hprefix tailTrace_571271
  have hstable : (prefixWord ++ tailWord_571271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571271).length < 2 ^ (prefixWord ++ tailWord_571271).sum := by decide
  have hdescent : baseEnd_571271 < baseStart_571271 := by decide
  rcases family_descends (prefixWord ++ tailWord_571271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571468 : List Nat := [2, 2, 1, 3, 1, 1, 6, 1, 5]
def baseStart_571468 : Nat := 118140960795 + 571468 * 2 ^ 59
def prefixEnd_571468 : Nat := 4983230072969 + 3 ^ 40 * 571468 * 2
def baseEnd_571468 : Nat := 65208391703038969449305

theorem tailTrace_571468 : CollatzResearch.WordTrace tailWord_571468 prefixEnd_571468 65208391703038969449305 := by
  unfold tailWord_571468
  simp only [CollatzResearch.WordTrace]
  refine ⟨10421575146838254904629529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13895433529117673206172705 10421575146838254904629529)
  ·
    refine ⟨7816181360128691178472147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10421575146838254904629529 7816181360128691178472147)
    ·
      refine ⟨11724272040193036767708221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7816181360128691178472147 11724272040193036767708221)
      ·
        refine ⟨4396602015072388787890583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11724272040193036767708221 4396602015072388787890583)
        ·
          refine ⟨6594903022608583181835875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4396602015072388787890583 6594903022608583181835875)
          ·
            refine ⟨9892354533912874772753813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6594903022608583181835875 9892354533912874772753813)
            ·
              refine ⟨463704118777166004972835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9892354533912874772753813 463704118777166004972835)
              ·
                refine ⟨695556178165749007459253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463704118777166004972835 695556178165749007459253)
                ·
                  refine ⟨65208391703038969449305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 695556178165749007459253 65208391703038969449305)
                  ·
                    rfl

theorem cell22_571468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_571468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_571468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_571468 prefixEnd_571468 := by exact prefixLift 571468
  have htrace : WordTrace (prefixWord ++ tailWord_571468) baseStart_571468 baseEnd_571468 := by
    simpa [prefixWord, tailWord_571468, baseEnd_571468] using wordTrace_append hprefix tailTrace_571468
  have hstable : (prefixWord ++ tailWord_571468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571468).length < 2 ^ (prefixWord ++ tailWord_571468).sum := by decide
  have hdescent : baseEnd_571468 < baseStart_571468 := by decide
  rcases family_descends (prefixWord ++ tailWord_571468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571481 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 3, 4]
def baseStart_571481 : Nat := 118140960795 + 571481 * 2 ^ 59
def prefixEnd_571481 : Nat := 4983230072969 + 3 ^ 40 * 571481 * 2
def baseEnd_571481 : Nat := 195629625274789207772875

theorem tailTrace_571481 : CollatzResearch.WordTrace tailWord_571481 prefixEnd_571481 195629625274789207772875 := by
  unfold tailWord_571481
  simp only [CollatzResearch.WordTrace]
  refine ⟨20843624442629413029482297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13895749628419608686321531 20843624442629413029482297)
  ·
    refine ⟨15632718331972059772111723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20843624442629413029482297 15632718331972059772111723)
    ·
      refine ⟨23449077497958089658167585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15632718331972059772111723 23449077497958089658167585)
      ·
        refine ⟨17586808123468567243625689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23449077497958089658167585 17586808123468567243625689)
        ·
          refine ⟨13190106092601425432719267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17586808123468567243625689 13190106092601425432719267)
          ·
            refine ⟨19785159138902138149078901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13190106092601425432719267 19785159138902138149078901)
            ·
              refine ⟨1854858669272075451476147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19785159138902138149078901 1854858669272075451476147)
              ·
                refine ⟨2782288003908113177214221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854858669272075451476147 2782288003908113177214221)
                ·
                  refine ⟨1043358001465542441455333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2782288003908113177214221 1043358001465542441455333)
                  ·
                    refine ⟨195629625274789207772875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1043358001465542441455333 195629625274789207772875)
                    ·
                      rfl

theorem cell22_571481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_571481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_571481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_571481 prefixEnd_571481 := by exact prefixLift 571481
  have htrace : WordTrace (prefixWord ++ tailWord_571481) baseStart_571481 baseEnd_571481 := by
    simpa [prefixWord, tailWord_571481, baseEnd_571481] using wordTrace_append hprefix tailTrace_571481
  have hstable : (prefixWord ++ tailWord_571481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571481).length < 2 ^ (prefixWord ++ tailWord_571481).sum := by decide
  have hdescent : baseEnd_571481 < baseStart_571481 := by decide
  rcases family_descends (prefixWord ++ tailWord_571481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571528 : List Nat := [2, 1, 3, 4, 1, 1, 1, 3, 1, 5]
def baseStart_571528 : Nat := 118140960795 + 571528 * 2 ^ 59
def prefixEnd_571528 : Nat := 4983230072969 + 3 ^ 40 * 571528 * 2
def baseEnd_571528 : Nat := 195645714335296751847731

theorem tailTrace_571528 : CollatzResearch.WordTrace tailWord_571528 prefixEnd_571528 195645714335296751847731 := by
  unfold tailWord_571528
  simp only [CollatzResearch.WordTrace]
  refine ⟨10422669336729570028221619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13896892448972760037628825 10422669336729570028221619)
  ·
    refine ⟨15634004005094355042332429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10422669336729570028221619 15634004005094355042332429)
    ·
      refine ⟨5862751501910383140874661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15634004005094355042332429 5862751501910383140874661)
      ·
        refine ⟨1099265906608196838913999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5862751501910383140874661 1099265906608196838913999)
        ·
          refine ⟨1648898859912295258370999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1099265906608196838913999 1648898859912295258370999)
          ·
            refine ⟨2473348289868442887556499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1648898859912295258370999 2473348289868442887556499)
            ·
              refine ⟨3710022434802664331334749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2473348289868442887556499 3710022434802664331334749)
              ·
                refine ⟨1391258413050999124250531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3710022434802664331334749 1391258413050999124250531)
                ·
                  refine ⟨2086887619576498686375797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391258413050999124250531 2086887619576498686375797)
                  ·
                    refine ⟨195645714335296751847731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2086887619576498686375797 195645714335296751847731)
                    ·
                      rfl

theorem cell22_571528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_571528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_571528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_571528 prefixEnd_571528 := by exact prefixLift 571528
  have htrace : WordTrace (prefixWord ++ tailWord_571528) baseStart_571528 baseEnd_571528 := by
    simpa [prefixWord, tailWord_571528, baseEnd_571528] using wordTrace_append hprefix tailTrace_571528
  have hstable : (prefixWord ++ tailWord_571528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571528).length < 2 ^ (prefixWord ++ tailWord_571528).sum := by decide
  have hdescent : baseEnd_571528 < baseStart_571528 := by decide
  rcases family_descends (prefixWord ++ tailWord_571528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571543 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 1, 6]
def baseStart_571543 : Nat := 118140960795 + 571543 * 2 ^ 59
def prefixEnd_571543 : Nat := 4983230072969 + 3 ^ 40 * 571543 * 2
def baseEnd_571543 : Nat := 195650849141841712722685

theorem tailTrace_571543 : CollatzResearch.WordTrace tailWord_571543 prefixEnd_571543 195650849141841712722685 := by
  unfold tailWord_571543
  simp only [CollatzResearch.WordTrace]
  refine ⟨20845885768404797618239283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13897257178936531745492855 20845885768404797618239283)
  ·
    refine ⟨31268828652607196427358925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20845885768404797618239283 31268828652607196427358925)
    ·
      refine ⟨11725810744727698660259597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31268828652607196427358925 11725810744727698660259597)
      ·
        refine ⟨4397179029272886997597349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11725810744727698660259597 4397179029272886997597349)
        ·
          refine ⟨824471067988666312049503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4397179029272886997597349 824471067988666312049503)
          ·
            refine ⟨1236706601982999468074255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824471067988666312049503 1236706601982999468074255)
            ·
              refine ⟨1855059902974499202111383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1236706601982999468074255 1855059902974499202111383)
              ·
                refine ⟨2782589854461748803167075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1855059902974499202111383 2782589854461748803167075)
                ·
                  refine ⟨4173884781692623204750613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2782589854461748803167075 4173884781692623204750613)
                  ·
                    refine ⟨195650849141841712722685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4173884781692623204750613 195650849141841712722685)
                    ·
                      rfl

theorem cell22_571543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_571543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_571543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_571543 prefixEnd_571543 := by exact prefixLift 571543
  have htrace : WordTrace (prefixWord ++ tailWord_571543) baseStart_571543 baseEnd_571543 := by
    simpa [prefixWord, tailWord_571543, baseEnd_571543] using wordTrace_append hprefix tailTrace_571543
  have hstable : (prefixWord ++ tailWord_571543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571543).length < 2 ^ (prefixWord ++ tailWord_571543).sum := by decide
  have hdescent : baseEnd_571543 < baseStart_571543 := by decide
  rcases family_descends (prefixWord ++ tailWord_571543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571562 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 4, 3]
def baseStart_571562 : Nat := 118140960795 + 571562 * 2 ^ 59
def prefixEnd_571562 : Nat := 4983230072969 + 3 ^ 40 * 571562 * 2
def baseEnd_571562 : Nat := 195657353230131996497627

theorem tailTrace_571562 : CollatzResearch.WordTrace tailWord_571562 prefixEnd_571562 195657353230131996497627 := by
  unfold tailWord_571562
  simp only [CollatzResearch.WordTrace]
  refine ⟨5211644688833990965795235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13897719170223975908787293 5211644688833990965795235)
  ·
    refine ⟨7817467033250986448692853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5211644688833990965795235 7817467033250986448692853)
    ·
      refine ⟨732887534367279979564955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7817467033250986448692853 732887534367279979564955)
      ·
        refine ⟨1099331301550919969347433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 732887534367279979564955 1099331301550919969347433)
        ·
          refine ⟨824498476163189977010575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1099331301550919969347433 824498476163189977010575)
          ·
            refine ⟨1236747714244784965515863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824498476163189977010575 1236747714244784965515863)
            ·
              refine ⟨1855121571367177448273795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1236747714244784965515863 1855121571367177448273795)
              ·
                refine ⟨2782682357050766172410693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1855121571367177448273795 2782682357050766172410693)
                ·
                  refine ⟨521752941947018657327005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2782682357050766172410693 521752941947018657327005)
                  ·
                    refine ⟨195657353230131996497627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 521752941947018657327005 195657353230131996497627)
                    ·
                      rfl

theorem cell22_571562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_571562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_571562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_571562 prefixEnd_571562 := by exact prefixLift 571562
  have htrace : WordTrace (prefixWord ++ tailWord_571562) baseStart_571562 baseEnd_571562 := by
    simpa [prefixWord, tailWord_571562, baseEnd_571562] using wordTrace_append hprefix tailTrace_571562
  have hstable : (prefixWord ++ tailWord_571562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571562).length < 2 ^ (prefixWord ++ tailWord_571562).sum := by decide
  have hdescent : baseEnd_571562 < baseStart_571562 := by decide
  rcases family_descends (prefixWord ++ tailWord_571562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571601 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 1, 7]
def baseStart_571601 : Nat := 118140960795 + 571601 * 2 ^ 59
def prefixEnd_571601 : Nat := 4983230072969 + 3 ^ 40 * 571601 * 2
def baseEnd_571601 : Nat := 195670703727148894772507

theorem tailTrace_571601 : CollatzResearch.WordTrace tailWord_571601 prefixEnd_571601 195670703727148894772507 := by
  unfold tailWord_571601
  simp only [CollatzResearch.WordTrace]
  refine ⟨20848001202194673523850657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13898667468129782349233771 20848001202194673523850657)
  ·
    refine ⟨15636000901646005142887993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20848001202194673523850657 15636000901646005142887993)
    ·
      refine ⟨11727000676234503857165995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15636000901646005142887993 11727000676234503857165995)
      ·
        refine ⟨17590501014351755785748993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11727000676234503857165995 17590501014351755785748993)
        ·
          refine ⟨13192875760763816839311745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17590501014351755785748993 13192875760763816839311745)
          ·
            refine ⟨9894656820572862629483809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13192875760763816839311745 9894656820572862629483809)
            ·
              refine ⟨7420992615429646972112857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9894656820572862629483809 7420992615429646972112857)
              ·
                refine ⟨5565744461572235229084643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7420992615429646972112857 5565744461572235229084643)
                ·
                  refine ⟨8348616692358352843626965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5565744461572235229084643 8348616692358352843626965)
                  ·
                    refine ⟨195670703727148894772507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8348616692358352843626965 195670703727148894772507)
                    ·
                      rfl

theorem cell22_571601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_571601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_571601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_571601 prefixEnd_571601 := by exact prefixLift 571601
  have htrace : WordTrace (prefixWord ++ tailWord_571601) baseStart_571601 baseEnd_571601 := by
    simpa [prefixWord, tailWord_571601, baseEnd_571601] using wordTrace_append hprefix tailTrace_571601
  have hstable : (prefixWord ++ tailWord_571601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571601).length < 2 ^ (prefixWord ++ tailWord_571601).sum := by decide
  have hdescent : baseEnd_571601 < baseStart_571601 := by decide
  rcases family_descends (prefixWord ++ tailWord_571601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571624 : List Nat := [2, 1, 4, 1, 2, 3, 3, 2, 1, 3]
def baseStart_571624 : Nat := 118140960795 + 571624 * 2 ^ 59
def prefixEnd_571624 : Nat := 4983230072969 + 3 ^ 40 * 571624 * 2
def baseEnd_571624 : Nat := 195678577097184501447437

theorem tailTrace_571624 : CollatzResearch.WordTrace tailWord_571624 prefixEnd_571624 195678577097184501447437 := by
  unfold tailWord_571624
  simp only [CollatzResearch.WordTrace]
  refine ⟨10424420040555674225968963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13899226720740898967958617 10424420040555674225968963)
  ·
    refine ⟨15636630060833511338953445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10424420040555674225968963 15636630060833511338953445)
    ·
      refine ⟨2931868136406283376053771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15636630060833511338953445 2931868136406283376053771)
      ·
        refine ⟨4397802204609425064080657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2931868136406283376053771 4397802204609425064080657)
        ·
          refine ⟨3298351653457068798060493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4397802204609425064080657 3298351653457068798060493)
          ·
            refine ⟨1236881870046400799272685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3298351653457068798060493 1236881870046400799272685)
            ·
              refine ⟨463830701267400299727257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1236881870046400799272685 463830701267400299727257)
              ·
                refine ⟨347873025950550224795443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 463830701267400299727257 347873025950550224795443)
                ·
                  refine ⟨521809538925825337193165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 347873025950550224795443 521809538925825337193165)
                  ·
                    refine ⟨195678577097184501447437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 521809538925825337193165 195678577097184501447437)
                    ·
                      rfl

theorem cell22_571624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_571624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_571624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_571624 prefixEnd_571624 := by exact prefixLift 571624
  have htrace : WordTrace (prefixWord ++ tailWord_571624) baseStart_571624 baseEnd_571624 := by
    simpa [prefixWord, tailWord_571624, baseEnd_571624] using wordTrace_append hprefix tailTrace_571624
  have hstable : (prefixWord ++ tailWord_571624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571624).length < 2 ^ (prefixWord ++ tailWord_571624).sum := by decide
  have hdescent : baseEnd_571624 < baseStart_571624 := by decide
  rcases family_descends (prefixWord ++ tailWord_571624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571663 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 6, 3]
def baseStart_571663 : Nat := 118140960795 + 571663 * 2 ^ 59
def prefixEnd_571663 : Nat := 4983230072969 + 3 ^ 40 * 571663 * 2
def baseEnd_571663 : Nat := 195691927594201399722317

theorem tailTrace_571663 : CollatzResearch.WordTrace tailWord_571663 prefixEnd_571663 195691927594201399722317 := by
  unfold tailWord_571663
  simp only [CollatzResearch.WordTrace]
  refine ⟨20850262527970058112607643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13900175018646705408405095 20850262527970058112607643)
  ·
    refine ⟨31275393791955087168911465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20850262527970058112607643 31275393791955087168911465)
    ·
      refine ⟨23456545343966315376683599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31275393791955087168911465 23456545343966315376683599)
      ·
        refine ⟨35184818015949473065025399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23456545343966315376683599 35184818015949473065025399)
        ·
          refine ⟨52777227023924209597538099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35184818015949473065025399 52777227023924209597538099)
          ·
            refine ⟨79165840535886314396307149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52777227023924209597538099 79165840535886314396307149)
            ·
              refine ⟨29687190200957367898615181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79165840535886314396307149 29687190200957367898615181)
              ·
                refine ⟨11132696325359012961980693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29687190200957367898615181 11132696325359012961980693)
                ·
                  refine ⟨521845140251203732592845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11132696325359012961980693 521845140251203732592845)
                  ·
                    refine ⟨195691927594201399722317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 521845140251203732592845 195691927594201399722317)
                    ·
                      rfl

theorem cell22_571663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 3].length) (baseStart_571663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_571663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_571663 prefixEnd_571663 := by exact prefixLift 571663
  have htrace : WordTrace (prefixWord ++ tailWord_571663) baseStart_571663 baseEnd_571663 := by
    simpa [prefixWord, tailWord_571663, baseEnd_571663] using wordTrace_append hprefix tailTrace_571663
  have hstable : (prefixWord ++ tailWord_571663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571663).length < 2 ^ (prefixWord ++ tailWord_571663).sum := by decide
  have hdescent : baseEnd_571663 < baseStart_571663 := by decide
  rcases family_descends (prefixWord ++ tailWord_571663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571682 : List Nat := [3, 3, 1, 1, 3, 2, 1, 4, 4]
def baseStart_571682 : Nat := 118140960795 + 571682 * 2 ^ 59
def prefixEnd_571682 : Nat := 4983230072969 + 3 ^ 40 * 571682 * 2
def baseEnd_571682 : Nat := 65232810560830561165753

theorem tailTrace_571682 : CollatzResearch.WordTrace tailWord_571682 prefixEnd_571682 65232810560830561165753 := by
  unfold tailWord_571682
  simp only [CollatzResearch.WordTrace]
  refine ⟨5212738878725306089387325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13900637009934149571699533 5212738878725306089387325)
  ·
    refine ⟨1954777079521989783520247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5212738878725306089387325 1954777079521989783520247)
    ·
      refine ⟨2932165619282984675280371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1954777079521989783520247 2932165619282984675280371)
      ·
        refine ⟨4398248428924477012920557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2932165619282984675280371 4398248428924477012920557)
        ·
          refine ⟨1649343160846678879845209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4398248428924477012920557 1649343160846678879845209)
          ·
            refine ⟨1237007370635009159883907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1649343160846678879845209 1237007370635009159883907)
            ·
              refine ⟨1855511055952513739825861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1237007370635009159883907 1855511055952513739825861)
              ·
                refine ⟨347908322991096326217349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1855511055952513739825861 347908322991096326217349)
                ·
                  refine ⟨65232810560830561165753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 347908322991096326217349 65232810560830561165753)
                  ·
                    rfl

theorem cell22_571682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_571682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_571682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_571682 prefixEnd_571682 := by exact prefixLift 571682
  have htrace : WordTrace (prefixWord ++ tailWord_571682) baseStart_571682 baseEnd_571682 := by
    simpa [prefixWord, tailWord_571682, baseEnd_571682] using wordTrace_append hprefix tailTrace_571682
  have hstable : (prefixWord ++ tailWord_571682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571682).length < 2 ^ (prefixWord ++ tailWord_571682).sum := by decide
  have hdescent : baseEnd_571682 < baseStart_571682 := by decide
  rcases family_descends (prefixWord ++ tailWord_571682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571753 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 2, 5]
def baseStart_571753 : Nat := 118140960795 + 571753 * 2 ^ 59
def prefixEnd_571753 : Nat := 4983230072969 + 3 ^ 40 * 571753 * 2
def baseEnd_571753 : Nat := 195722736433471164972041

theorem tailTrace_571753 : CollatzResearch.WordTrace tailWord_571753 prefixEnd_571753 195722736433471164972041 := by
  unfold tailWord_571753
  simp only [CollatzResearch.WordTrace]
  refine ⟨20853545097644003483383913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13902363398429335655589275 20853545097644003483383913)
  ·
    refine ⟨15640158823233002612537935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20853545097644003483383913 15640158823233002612537935)
    ·
      refine ⟨23460238234849503918806903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15640158823233002612537935 23460238234849503918806903)
      ·
        refine ⟨35190357352274255878210355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23460238234849503918806903 35190357352274255878210355)
        ·
          refine ⟨52785536028411383817315533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35190357352274255878210355 52785536028411383817315533)
          ·
            refine ⟨19794576010654268931493325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52785536028411383817315533 19794576010654268931493325)
            ·
              refine ⟨7422966003995350849309997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19794576010654268931493325 7422966003995350849309997)
              ·
                refine ⟨2783612251498256568491249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7422966003995350849309997 2783612251498256568491249)
                ·
                  refine ⟨2087709188623692426368437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2783612251498256568491249 2087709188623692426368437)
                  ·
                    refine ⟨195722736433471164972041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2087709188623692426368437 195722736433471164972041)
                    ·
                      rfl

theorem cell22_571753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_571753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_571753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_571753 prefixEnd_571753 := by exact prefixLift 571753
  have htrace : WordTrace (prefixWord ++ tailWord_571753) baseStart_571753 baseEnd_571753 := by
    simpa [prefixWord, tailWord_571753, baseEnd_571753] using wordTrace_append hprefix tailTrace_571753
  have hstable : (prefixWord ++ tailWord_571753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571753).length < 2 ^ (prefixWord ++ tailWord_571753).sum := by decide
  have hdescent : baseEnd_571753 < baseStart_571753 := by decide
  rcases family_descends (prefixWord ++ tailWord_571753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571806 : List Nat := [4, 3, 1, 2, 1, 3, 2, 1, 5]
def baseStart_571806 : Nat := 118140960795 + 571806 * 2 ^ 59
def prefixEnd_571806 : Nat := 4983230072969 + 3 ^ 40 * 571806 * 2
def baseEnd_571806 : Nat := 65246959805532231132293

theorem tailTrace_571806 : CollatzResearch.WordTrace tailWord_571806 prefixEnd_571806 65246959805532231132293 := by
  unfold tailWord_571806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2606934770806499191882909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13903652110967995690042181 2606934770806499191882909)
  ·
    refine ⟨977600539052437196956091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2606934770806499191882909 977600539052437196956091)
    ·
      refine ⟨1466400808578655795434137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 977600539052437196956091 1466400808578655795434137)
      ·
        refine ⟨1099800606433991846575603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1466400808578655795434137 1099800606433991846575603)
        ·
          refine ⟨1649700909650987769863405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1099800606433991846575603 1649700909650987769863405)
          ·
            refine ⟨618637841119120413698777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1649700909650987769863405 618637841119120413698777)
            ·
              refine ⟨463978380839340310274083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 618637841119120413698777 463978380839340310274083)
              ·
                refine ⟨695967571259010465411125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463978380839340310274083 695967571259010465411125)
                ·
                  refine ⟨65246959805532231132293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 695967571259010465411125 65246959805532231132293)
                  ·
                    rfl

theorem cell22_571806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_571806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_571806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_571806 prefixEnd_571806 := by exact prefixLift 571806
  have htrace : WordTrace (prefixWord ++ tailWord_571806) baseStart_571806 baseEnd_571806 := by
    simpa [prefixWord, tailWord_571806, baseEnd_571806] using wordTrace_append hprefix tailTrace_571806
  have hstable : (prefixWord ++ tailWord_571806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571806).length < 2 ^ (prefixWord ++ tailWord_571806).sum := by decide
  have hdescent : baseEnd_571806 < baseStart_571806 := by decide
  rcases family_descends (prefixWord ++ tailWord_571806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571967 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 4, 3]
def baseStart_571967 : Nat := 118140960795 + 571967 * 2 ^ 59
def prefixEnd_571967 : Nat := 4983230072969 + 3 ^ 40 * 571967 * 2
def baseEnd_571967 : Nat := 195795993006845940121385

theorem tailTrace_571967 : CollatzResearch.WordTrace tailWord_571967 prefixEnd_571967 195795993006845940121385 := by
  unfold tailWord_571967
  simp only [CollatzResearch.WordTrace]
  refine ⟨20861350318868718031674155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13907566879245812021116103 20861350318868718031674155)
  ·
    refine ⟨31292025478303077047511233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20861350318868718031674155 31292025478303077047511233)
    ·
      refine ⟨23469019108727307785633425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31292025478303077047511233 23469019108727307785633425)
      ·
        refine ⟨17601764331545480839225069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23469019108727307785633425 17601764331545480839225069)
        ·
          refine ⟨6600661624329555314709401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17601764331545480839225069 6600661624329555314709401)
          ·
            refine ⟨4950496218247166486032051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6600661624329555314709401 4950496218247166486032051)
            ·
              refine ⟨7425744327370749729048077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4950496218247166486032051 7425744327370749729048077)
              ·
                refine ⟨2784654122764031148393029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7425744327370749729048077 2784654122764031148393029)
                ·
                  refine ⟨522122648018255840323693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2784654122764031148393029 522122648018255840323693)
                  ·
                    refine ⟨195795993006845940121385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 522122648018255840323693 195795993006845940121385)
                    ·
                      rfl

theorem cell22_571967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 3].length) (baseStart_571967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_571967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_571967 prefixEnd_571967 := by exact prefixLift 571967
  have htrace : WordTrace (prefixWord ++ tailWord_571967) baseStart_571967 baseEnd_571967 := by
    simpa [prefixWord, tailWord_571967, baseEnd_571967] using wordTrace_append hprefix tailTrace_571967
  have hstable : (prefixWord ++ tailWord_571967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571967).length < 2 ^ (prefixWord ++ tailWord_571967).sum := by decide
  have hdescent : baseEnd_571967 < baseStart_571967 := by decide
  rcases family_descends (prefixWord ++ tailWord_571967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571969 : List Nat := [1, 2, 5, 1, 1, 4, 1, 1, 6]
def baseStart_571969 : Nat := 118140960795 + 571969 * 2 ^ 59
def prefixEnd_571969 : Nat := 4983230072969 + 3 ^ 40 * 571969 * 2
def baseEnd_571969 : Nat := 65265559215906200523793

theorem tailTrace_571969 : CollatzResearch.WordTrace tailWord_571969 prefixEnd_571969 65265559215906200523793 := by
  unfold tailWord_571969
  simp only [CollatzResearch.WordTrace]
  refine ⟨20861423264861472373246961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13907615509907648248831307 20861423264861472373246961)
  ·
    refine ⟨15646067448646104279935221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20861423264861472373246961 15646067448646104279935221)
    ·
      refine ⟨1466818823310572276243927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15646067448646104279935221 1466818823310572276243927)
      ·
        refine ⟨2200228234965858414365891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1466818823310572276243927 2200228234965858414365891)
        ·
          refine ⟨3300342352448787621548837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2200228234965858414365891 3300342352448787621548837)
          ·
            refine ⟨618814191084147679040407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3300342352448787621548837 618814191084147679040407)
            ·
              refine ⟨928221286626221518560611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 618814191084147679040407 928221286626221518560611)
              ·
                refine ⟨1392331929939332277840917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 928221286626221518560611 1392331929939332277840917)
                ·
                  refine ⟨65265559215906200523793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1392331929939332277840917 65265559215906200523793)
                  ·
                    rfl

theorem cell22_571969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 6].length) (baseStart_571969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_571969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_571969 prefixEnd_571969 := by exact prefixLift 571969
  have htrace : WordTrace (prefixWord ++ tailWord_571969) baseStart_571969 baseEnd_571969 := by
    simpa [prefixWord, tailWord_571969, baseEnd_571969] using wordTrace_append hprefix tailTrace_571969
  have hstable : (prefixWord ++ tailWord_571969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571969).length < 2 ^ (prefixWord ++ tailWord_571969).sum := by decide
  have hdescent : baseEnd_571969 < baseStart_571969 := by decide
  rcases family_descends (prefixWord ++ tailWord_571969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572106 : List Nat := [3, 1, 2, 1, 4, 2, 2, 2, 1, 4]
def baseStart_572106 : Nat := 118140960795 + 572106 * 2 ^ 59
def prefixEnd_572106 : Nat := 4983230072969 + 3 ^ 40 * 572106 * 2
def baseEnd_572106 : Nat := 195843575547495910895959

theorem tailTrace_572106 : CollatzResearch.WordTrace tailWord_572106 prefixEnd_572106 195843575547495910895959 := by
  unfold tailWord_572106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5216605016341286192746043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13910946710243429847322781 5216605016341286192746043)
  ·
    refine ⟨7824907524511929289119065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5216605016341286192746043 7824907524511929289119065)
    ·
      refine ⟨5868680643383946966839299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7824907524511929289119065 5868680643383946966839299)
      ·
        refine ⟨8803020965075920450258949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5868680643383946966839299 8803020965075920450258949)
        ·
          refine ⟨1650566430951735084423553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8803020965075920450258949 1650566430951735084423553)
          ·
            refine ⟨1237924823213801313317665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1650566430951735084423553 1237924823213801313317665)
            ·
              refine ⟨928443617410350984988249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1237924823213801313317665 928443617410350984988249)
              ·
                refine ⟨696332713057763238741187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 928443617410350984988249 696332713057763238741187)
                ·
                  refine ⟨1044499069586644858111781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 696332713057763238741187 1044499069586644858111781)
                  ·
                    refine ⟨195843575547495910895959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1044499069586644858111781 195843575547495910895959)
                    ·
                      rfl

theorem cell22_572106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_572106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572106 prefixEnd_572106 := by exact prefixLift 572106
  have htrace : WordTrace (prefixWord ++ tailWord_572106) baseStart_572106 baseEnd_572106 := by
    simpa [prefixWord, tailWord_572106, baseEnd_572106] using wordTrace_append hprefix tailTrace_572106
  have hstable : (prefixWord ++ tailWord_572106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572106).length < 2 ^ (prefixWord ++ tailWord_572106).sum := by decide
  have hdescent : baseEnd_572106 < baseStart_572106 := by decide
  rcases family_descends (prefixWord ++ tailWord_572106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572119 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 4, 3]
def baseStart_572119 : Nat := 118140960795 + 572119 * 2 ^ 59
def prefixEnd_572119 : Nat := 4983230072969 + 3 ^ 40 * 572119 * 2
def baseEnd_572119 : Nat := 195848025713168210320919

theorem tailTrace_572119 : CollatzResearch.WordTrace tailWord_572119 prefixEnd_572119 195848025713168210320919 := by
  unfold tailWord_572119
  simp only [CollatzResearch.WordTrace]
  refine ⟨20866894214318047991207411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13911262809545365327471607 20866894214318047991207411)
  ·
    refine ⟨31300341321477071986811117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20866894214318047991207411 31300341321477071986811117)
    ·
      refine ⟨11737627995553901995054169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31300341321477071986811117 11737627995553901995054169)
      ·
        refine ⟨8803220996665426496290627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11737627995553901995054169 8803220996665426496290627)
        ·
          refine ⟨13204831494998139744435941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8803220996665426496290627 13204831494998139744435941)
          ·
            refine ⟨2475905905312151202081739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13204831494998139744435941 2475905905312151202081739)
            ·
              refine ⟨3713858857968226803122609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2475905905312151202081739 3713858857968226803122609)
              ·
                refine ⟨2785394143476170102341957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3713858857968226803122609 2785394143476170102341957)
                ·
                  refine ⟨522261401901781894189117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2785394143476170102341957 522261401901781894189117)
                  ·
                    refine ⟨195848025713168210320919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 522261401901781894189117 195848025713168210320919)
                    ·
                      rfl

theorem cell22_572119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_572119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572119 prefixEnd_572119 := by exact prefixLift 572119
  have htrace : WordTrace (prefixWord ++ tailWord_572119) baseStart_572119 baseEnd_572119 := by
    simpa [prefixWord, tailWord_572119, baseEnd_572119] using wordTrace_append hprefix tailTrace_572119
  have hstable : (prefixWord ++ tailWord_572119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572119).length < 2 ^ (prefixWord ++ tailWord_572119).sum := by decide
  have hdescent : baseEnd_572119 < baseStart_572119 := by decide
  rcases family_descends (prefixWord ++ tailWord_572119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572132 : List Nat := [2, 3, 1, 1, 1, 4, 10]
def baseStart_572132 : Nat := 118140960795 + 572132 * 2 ^ 59
def prefixEnd_572132 : Nat := 4983230072969 + 3 ^ 40 * 572132 * 2
def baseEnd_572132 : Nat := 7253795402920018879477

theorem tailTrace_572132 : CollatzResearch.WordTrace tailWord_572132 prefixEnd_572132 7253795402920018879477 := by
  unfold tailWord_572132
  simp only [CollatzResearch.WordTrace]
  refine ⟨10433684181635475605715325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13911578908847300807620433 10433684181635475605715325)
  ·
    refine ⟨3912631568113303352143247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10433684181635475605715325 3912631568113303352143247)
    ·
      refine ⟨5868947352169955028214871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3912631568113303352143247 5868947352169955028214871)
      ·
        refine ⟨8803421028254932542322307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5868947352169955028214871 8803421028254932542322307)
        ·
          refine ⟨13205131542382398813483461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8803421028254932542322307 13205131542382398813483461)
          ·
            refine ⟨2475962164196699777528149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13205131542382398813483461 2475962164196699777528149)
            ·
              refine ⟨7253795402920018879477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2475962164196699777528149 7253795402920018879477)
              ·
                rfl

theorem cell22_572132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 10].length) (baseStart_572132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572132 prefixEnd_572132 := by exact prefixLift 572132
  have htrace : WordTrace (prefixWord ++ tailWord_572132) baseStart_572132 baseEnd_572132 := by
    simpa [prefixWord, tailWord_572132, baseEnd_572132] using wordTrace_append hprefix tailTrace_572132
  have hstable : (prefixWord ++ tailWord_572132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572132).length < 2 ^ (prefixWord ++ tailWord_572132).sum := by decide
  have hdescent : baseEnd_572132 < baseStart_572132 := by decide
  rcases family_descends (prefixWord ++ tailWord_572132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572177 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 9]
def baseStart_572177 : Nat := 118140960795 + 572177 * 2 ^ 59
def prefixEnd_572177 : Nat := 4983230072969 + 3 ^ 40 * 572177 * 2
def baseEnd_572177 : Nat := 65289293432825130790247

theorem tailTrace_572177 : CollatzResearch.WordTrace tailWord_572177 prefixEnd_572177 65289293432825130790247 := by
  unfold tailWord_572177
  simp only [CollatzResearch.WordTrace]
  refine ⟨20869009648107923896818785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13912673098738615931212523 20869009648107923896818785)
  ·
    refine ⟨15651757236080942922614089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20869009648107923896818785 15651757236080942922614089)
    ·
      refine ⟨11738817927060707191960567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15651757236080942922614089 11738817927060707191960567)
      ·
        refine ⟨17608226890591060787940851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11738817927060707191960567 17608226890591060787940851)
        ·
          refine ⟨26412340335886591181911277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17608226890591060787940851 26412340335886591181911277)
          ·
            refine ⟨9904627625957471693216729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26412340335886591181911277 9904627625957471693216729)
            ·
              refine ⟨7428470719468103769912547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9904627625957471693216729 7428470719468103769912547)
              ·
                refine ⟨11142706079202155654868821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7428470719468103769912547 11142706079202155654868821)
                ·
                  refine ⟨65289293432825130790247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11142706079202155654868821 65289293432825130790247)
                  ·
                    rfl

theorem cell22_572177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 9].length) (baseStart_572177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572177 prefixEnd_572177 := by exact prefixLift 572177
  have htrace : WordTrace (prefixWord ++ tailWord_572177) baseStart_572177 baseEnd_572177 := by
    simpa [prefixWord, tailWord_572177, baseEnd_572177] using wordTrace_append hprefix tailTrace_572177
  have hstable : (prefixWord ++ tailWord_572177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572177).length < 2 ^ (prefixWord ++ tailWord_572177).sum := by decide
  have hdescent : baseEnd_572177 < baseStart_572177 := by decide
  rcases family_descends (prefixWord ++ tailWord_572177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572207 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 1, 10]
def baseStart_572207 : Nat := 118140960795 + 572207 * 2 ^ 59
def prefixEnd_572207 : Nat := 4983230072969 + 3 ^ 40 * 572207 * 2
def baseEnd_572207 : Nat := 195878149911565314120649

theorem tailTrace_572207 : CollatzResearch.WordTrace tailWord_572207 prefixEnd_572207 195878149911565314120649 := by
  unfold tailWord_572207
  simp only [CollatzResearch.WordTrace]
  refine ⟨20870103837999239020410875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13913402558666159346940583 20870103837999239020410875)
  ·
    refine ⟨31305155756998858530616313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20870103837999239020410875 31305155756998858530616313)
    ·
      refine ⟨23478866817749143897962235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31305155756998858530616313 23478866817749143897962235)
      ·
        refine ⟨35218300226623715846943353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23478866817749143897962235 35218300226623715846943353)
        ·
          refine ⟨26413725169967786885207515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35218300226623715846943353 26413725169967786885207515)
          ·
            refine ⟨39620587754951680327811273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26413725169967786885207515 39620587754951680327811273)
            ·
              refine ⟨29715440816213760245858455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39620587754951680327811273 29715440816213760245858455)
              ·
                refine ⟨44573161224320640368787683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29715440816213760245858455 44573161224320640368787683)
                ·
                  refine ⟨66859741836480960553181525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44573161224320640368787683 66859741836480960553181525)
                  ·
                    refine ⟨195878149911565314120649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 66859741836480960553181525 195878149911565314120649)
                    ·
                      rfl

theorem cell22_572207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_572207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572207 prefixEnd_572207 := by exact prefixLift 572207
  have htrace : WordTrace (prefixWord ++ tailWord_572207) baseStart_572207 baseEnd_572207 := by
    simpa [prefixWord, tailWord_572207, baseEnd_572207] using wordTrace_append hprefix tailTrace_572207
  have hstable : (prefixWord ++ tailWord_572207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572207).length < 2 ^ (prefixWord ++ tailWord_572207).sum := by decide
  have hdescent : baseEnd_572207 < baseStart_572207 := by decide
  rcases family_descends (prefixWord ++ tailWord_572207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572209 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 2, 5]
def baseStart_572209 : Nat := 118140960795 + 572209 * 2 ^ 59
def prefixEnd_572209 : Nat := 4983230072969 + 3 ^ 40 * 572209 * 2
def baseEnd_572209 : Nat := 195878834552437975570643

theorem tailTrace_572209 : CollatzResearch.WordTrace tailWord_572209 prefixEnd_572209 195878834552437975570643 := by
  unfold tailWord_572209
  simp only [CollatzResearch.WordTrace]
  refine ⟨20870176783991993361983681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13913451189327995574655787 20870176783991993361983681)
  ·
    refine ⟨15652632587993995021487761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20870176783991993361983681 15652632587993995021487761)
    ·
      refine ⟨11739474440995496266115821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15652632587993995021487761 11739474440995496266115821)
      ·
        refine ⟨4402302915373311099793433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11739474440995496266115821 4402302915373311099793433)
        ·
          refine ⟨3301727186529983324845075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4402302915373311099793433 3301727186529983324845075)
          ·
            refine ⟨4952590779794974987267613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3301727186529983324845075 4952590779794974987267613)
            ·
              refine ⟨1857221542423115620225355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4952590779794974987267613 1857221542423115620225355)
              ·
                refine ⟨2785832313634673430338033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1857221542423115620225355 2785832313634673430338033)
                ·
                  refine ⟨2089374235226005072753525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2785832313634673430338033 2089374235226005072753525)
                  ·
                    refine ⟨195878834552437975570643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2089374235226005072753525 195878834552437975570643)
                    ·
                      rfl

theorem cell22_572209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_572209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572209 prefixEnd_572209 := by exact prefixLift 572209
  have htrace : WordTrace (prefixWord ++ tailWord_572209) baseStart_572209 baseEnd_572209 := by
    simpa [prefixWord, tailWord_572209, baseEnd_572209] using wordTrace_append hprefix tailTrace_572209
  have hstable : (prefixWord ++ tailWord_572209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572209).length < 2 ^ (prefixWord ++ tailWord_572209).sum := by decide
  have hdescent : baseEnd_572209 < baseStart_572209 := by decide
  rcases family_descends (prefixWord ++ tailWord_572209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572256 : List Nat := [2, 1, 1, 3, 3, 1, 1, 6, 4]
def baseStart_572256 : Nat := 118140960795 + 572256 * 2 ^ 59
def prefixEnd_572256 : Nat := 4983230072969 + 3 ^ 40 * 572256 * 2
def baseEnd_572256 : Nat := 65298307870981839881833

theorem tailTrace_572256 : CollatzResearch.WordTrace tailWord_572256 prefixEnd_572256 65298307870981839881833 := by
  unfold tailWord_572256
  simp only [CollatzResearch.WordTrace]
  refine ⟨10435945507410860194472311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13914594009881146925963081 10435945507410860194472311)
  ·
    refine ⟨15653918261116290291708467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10435945507410860194472311 15653918261116290291708467)
    ·
      refine ⟨23480877391674435437562701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15653918261116290291708467 23480877391674435437562701)
      ·
        refine ⟨8805329021877913289086013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23480877391674435437562701 8805329021877913289086013)
        ·
          refine ⟨3301998383204217483407255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8805329021877913289086013 3301998383204217483407255)
          ·
            refine ⟨4952997574806326225110883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3301998383204217483407255 4952997574806326225110883)
            ·
              refine ⟨7429496362209489337666325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4952997574806326225110883 7429496362209489337666325)
              ·
                refine ⟨348257641978569812703109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7429496362209489337666325 348257641978569812703109)
                ·
                  refine ⟨65298307870981839881833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 348257641978569812703109 65298307870981839881833)
                  ·
                    rfl

theorem cell22_572256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 4].length) (baseStart_572256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572256 prefixEnd_572256 := by exact prefixLift 572256
  have htrace : WordTrace (prefixWord ++ tailWord_572256) baseStart_572256 baseEnd_572256 := by
    simpa [prefixWord, tailWord_572256, baseEnd_572256] using wordTrace_append hprefix tailTrace_572256
  have hstable : (prefixWord ++ tailWord_572256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572256).length < 2 ^ (prefixWord ++ tailWord_572256).sum := by decide
  have hdescent : baseEnd_572256 < baseStart_572256 := by decide
  rcases family_descends (prefixWord ++ tailWord_572256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572271 : List Nat := [1, 1, 2, 1, 3, 1, 1, 7, 2, 3]
def baseStart_572271 : Nat := 118140960795 + 572271 * 2 ^ 59
def prefixEnd_572271 : Nat := 4983230072969 + 3 ^ 40 * 572271 * 2
def baseEnd_572271 : Nat := 195900058419490480520453

theorem tailTrace_572271 : CollatzResearch.WordTrace tailWord_572271 prefixEnd_572271 195900058419490480520453 := by
  unfold tailWord_572271
  simp only [CollatzResearch.WordTrace]
  refine ⟨20872438109767377950740667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13914958739844918633827111 20872438109767377950740667)
  ·
    refine ⟨31308657164651066926111001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20872438109767377950740667 31308657164651066926111001)
    ·
      refine ⟨23481492873488300194583251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31308657164651066926111001 23481492873488300194583251)
      ·
        refine ⟨35222239310232450291874877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23481492873488300194583251 35222239310232450291874877)
        ·
          refine ⟨13208339741337168859453079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35222239310232450291874877 13208339741337168859453079)
          ·
            refine ⟨19812509612005753289179619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13208339741337168859453079 19812509612005753289179619)
            ·
              refine ⟨29718764418008629933769429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19812509612005753289179619 29718764418008629933769429)
              ·
                refine ⟨696533541047077264072721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29718764418008629933769429 696533541047077264072721)
                ·
                  refine ⟨522400155785307948054541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 696533541047077264072721 522400155785307948054541)
                  ·
                    refine ⟨195900058419490480520453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 522400155785307948054541 195900058419490480520453)
                    ·
                      rfl

theorem cell22_572271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 3].length) (baseStart_572271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572271 prefixEnd_572271 := by exact prefixLift 572271
  have htrace : WordTrace (prefixWord ++ tailWord_572271) baseStart_572271 baseEnd_572271 := by
    simpa [prefixWord, tailWord_572271, baseEnd_572271] using wordTrace_append hprefix tailTrace_572271
  have hstable : (prefixWord ++ tailWord_572271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572271).length < 2 ^ (prefixWord ++ tailWord_572271).sum := by decide
  have hdescent : baseEnd_572271 < baseStart_572271 := by decide
  rcases family_descends (prefixWord ++ tailWord_572271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572322 : List Nat := [3, 3, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_572322 : Nat := 118140960795 + 572322 * 2 ^ 59
def prefixEnd_572322 : Nat := 4983230072969 + 3 ^ 40 * 572322 * 2
def baseEnd_572322 : Nat := 195917516761743347495297

theorem tailTrace_572322 : CollatzResearch.WordTrace tailWord_572322 prefixEnd_572322 195917516761743347495297 := by
  unfold tailWord_572322
  simp only [CollatzResearch.WordTrace]
  refine ⟨5218574558145653415211805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13916198821721742440564813 5218574558145653415211805)
  ·
    refine ⟨1956965459304620030704427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5218574558145653415211805 1956965459304620030704427)
    ·
      refine ⟨2935448188956930046056641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1956965459304620030704427 2935448188956930046056641)
      ·
        refine ⟨2201586141717697534542481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2935448188956930046056641 2201586141717697534542481)
        ·
          refine ⟨1651189606288273150906861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2201586141717697534542481 1651189606288273150906861)
          ·
            refine ⟨619196102358102431590073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1651189606288273150906861 619196102358102431590073)
            ·
              refine ⟨464397076768576823692555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619196102358102431590073 464397076768576823692555)
              ·
                refine ⟨696595615152865235538833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464397076768576823692555 696595615152865235538833)
                ·
                  refine ⟨522446711364648926654125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 696595615152865235538833 522446711364648926654125)
                  ·
                    refine ⟨195917516761743347495297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 522446711364648926654125 195917516761743347495297)
                    ·
                      rfl

theorem cell22_572322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_572322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572322 prefixEnd_572322 := by exact prefixLift 572322
  have htrace : WordTrace (prefixWord ++ tailWord_572322) baseStart_572322 baseEnd_572322 := by
    simpa [prefixWord, tailWord_572322, baseEnd_572322] using wordTrace_append hprefix tailTrace_572322
  have hstable : (prefixWord ++ tailWord_572322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572322).length < 2 ^ (prefixWord ++ tailWord_572322).sum := by decide
  have hdescent : baseEnd_572322 < baseStart_572322 := by decide
  rcases family_descends (prefixWord ++ tailWord_572322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572350 : List Nat := [4, 2, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_572350 : Nat := 118140960795 + 572350 * 2 ^ 59
def prefixEnd_572350 : Nat := 4983230072969 + 3 ^ 40 * 572350 * 2
def baseEnd_572350 : Nat := 195927101733960607795211

theorem tailTrace_572350 : CollatzResearch.WordTrace tailWord_572350 prefixEnd_572350 195927101733960607795211 := by
  unfold tailWord_572350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2609414934560146805358313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13916879650987449628577669 2609414934560146805358313)
  ·
    refine ⟨1957061200920110104018735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2609414934560146805358313 1957061200920110104018735)
    ·
      refine ⟨2935591801380165156028103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1957061200920110104018735 2935591801380165156028103)
      ·
        refine ⟨4403387702070247734042155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2935591801380165156028103 4403387702070247734042155)
        ·
          refine ⟨6605081553105371601063233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4403387702070247734042155 6605081553105371601063233)
          ·
            refine ⟨4953811164829028700797425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6605081553105371601063233 4953811164829028700797425)
            ·
              refine ⟨3715358373621771525598069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4953811164829028700797425 3715358373621771525598069)
              ·
                refine ⟨348314847527041080524819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3715358373621771525598069 348314847527041080524819)
                ·
                  refine ⟨522472271290561620787229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348314847527041080524819 522472271290561620787229)
                  ·
                    refine ⟨195927101733960607795211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 522472271290561620787229 195927101733960607795211)
                    ·
                      rfl

theorem cell22_572350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_572350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572350 prefixEnd_572350 := by exact prefixLift 572350
  have htrace : WordTrace (prefixWord ++ tailWord_572350) baseStart_572350 baseEnd_572350 := by
    simpa [prefixWord, tailWord_572350, baseEnd_572350] using wordTrace_append hprefix tailTrace_572350
  have hstable : (prefixWord ++ tailWord_572350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572350).length < 2 ^ (prefixWord ++ tailWord_572350).sum := by decide
  have hdescent : baseEnd_572350 < baseStart_572350 := by decide
  rcases family_descends (prefixWord ++ tailWord_572350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572358 : List Nat := [6, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_572358 : Nat := 118140960795 + 572358 * 2 ^ 59
def prefixEnd_572358 : Nat := 4983230072969 + 3 ^ 40 * 572358 * 2
def baseEnd_572358 : Nat := 65309946765817084531729

theorem tailTrace_572358 : CollatzResearch.WordTrace tailWord_572358 prefixEnd_572358 65309946765817084531729 := by
  unfold tailWord_572358
  simp only [CollatzResearch.WordTrace]
  refine ⟨652362851889130994036179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13917074173634794539438485 652362851889130994036179)
  ·
    refine ⟨978544277833696491054269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 652362851889130994036179 978544277833696491054269)
    ·
      refine ⟨366954104187636184145351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 978544277833696491054269 366954104187636184145351)
      ·
        refine ⟨550431156281454276218027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366954104187636184145351 550431156281454276218027)
        ·
          refine ⟨825646734422181414327041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550431156281454276218027 825646734422181414327041)
          ·
            refine ⟨619235050816636060745281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 825646734422181414327041 619235050816636060745281)
            ·
              refine ⟨464426288112477045558961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619235050816636060745281 464426288112477045558961)
              ·
                refine ⟨348319716084357784169221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 464426288112477045558961 348319716084357784169221)
                ·
                  refine ⟨65309946765817084531729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 348319716084357784169221 65309946765817084531729)
                  ·
                    rfl

theorem cell22_572358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_572358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572358 prefixEnd_572358 := by exact prefixLift 572358
  have htrace : WordTrace (prefixWord ++ tailWord_572358) baseStart_572358 baseEnd_572358 := by
    simpa [prefixWord, tailWord_572358, baseEnd_572358] using wordTrace_append hprefix tailTrace_572358
  have hstable : (prefixWord ++ tailWord_572358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572358).length < 2 ^ (prefixWord ++ tailWord_572358).sum := by decide
  have hdescent : baseEnd_572358 < baseStart_572358 := by decide
  rcases family_descends (prefixWord ++ tailWord_572358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572367 : List Nat := [1, 1, 2, 1, 1, 8, 2, 2, 1, 3]
def baseStart_572367 : Nat := 118140960795 + 572367 * 2 ^ 59
def prefixEnd_572367 : Nat := 4983230072969 + 3 ^ 40 * 572367 * 2
def baseEnd_572367 : Nat := 195932921181378230120159

theorem tailTrace_572367 : CollatzResearch.WordTrace tailWord_572367 prefixEnd_572367 195932921181378230120159 := by
  unfold tailWord_572367
  simp only [CollatzResearch.WordTrace]
  refine ⟨20875939517419586346235355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13917293011613057564156903 20875939517419586346235355)
  ·
    refine ⟨31313909276129379519353033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20875939517419586346235355 31313909276129379519353033)
    ·
      refine ⟨23485431957097034639514775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31313909276129379519353033 23485431957097034639514775)
      ·
        refine ⟨35228147935645551959272163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23485431957097034639514775 35228147935645551959272163)
        ·
          refine ⟨52842221903468327938908245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35228147935645551959272163 52842221903468327938908245)
          ·
            refine ⟨619244787931269468034081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 52842221903468327938908245 619244787931269468034081)
            ·
              refine ⟨464433590948452101025561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619244787931269468034081 464433590948452101025561)
              ·
                refine ⟨348325193211339075769171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 464433590948452101025561 348325193211339075769171)
                ·
                  refine ⟨522487789817008613653757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348325193211339075769171 522487789817008613653757)
                  ·
                    refine ⟨195932921181378230120159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 522487789817008613653757 195932921181378230120159)
                    ·
                      rfl

theorem cell22_572367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 1, 3].length) (baseStart_572367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572367 prefixEnd_572367 := by exact prefixLift 572367
  have htrace : WordTrace (prefixWord ++ tailWord_572367) baseStart_572367 baseEnd_572367 := by
    simpa [prefixWord, tailWord_572367, baseEnd_572367] using wordTrace_append hprefix tailTrace_572367
  have hstable : (prefixWord ++ tailWord_572367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572367).length < 2 ^ (prefixWord ++ tailWord_572367).sum := by decide
  have hdescent : baseEnd_572367 < baseStart_572367 := by decide
  rcases family_descends (prefixWord ++ tailWord_572367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572376 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 3, 4]
def baseStart_572376 : Nat := 118140960795 + 572376 * 2 ^ 59
def prefixEnd_572376 : Nat := 4983230072969 + 3 ^ 40 * 572376 * 2
def baseEnd_572376 : Nat := 195936002065305206645131

theorem tailTrace_572376 : CollatzResearch.WordTrace tailWord_572376 prefixEnd_572376 195936002065305206645131 := by
  unfold tailWord_572376
  simp only [CollatzResearch.WordTrace]
  refine ⟨10438133887193490441656491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13917511849591320588875321 10438133887193490441656491)
  ·
    refine ⟨15657200830790235662484737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10438133887193490441656491 15657200830790235662484737)
    ·
      refine ⟨11742900623092676746863553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15657200830790235662484737 11742900623092676746863553)
      ·
        refine ⟨8807175467319507560147665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11742900623092676746863553 8807175467319507560147665)
        ·
          refine ⟨6605381600489630670110749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8807175467319507560147665 6605381600489630670110749)
          ·
            refine ⟨2477018100183611501291531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6605381600489630670110749 2477018100183611501291531)
            ·
              refine ⟨3715527150275417251937297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2477018100183611501291531 3715527150275417251937297)
              ·
                refine ⟨2786645362706562938952973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3715527150275417251937297 2786645362706562938952973)
                ·
                  refine ⟨1044992011014961102107365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2786645362706562938952973 1044992011014961102107365)
                  ·
                    refine ⟨195936002065305206645131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1044992011014961102107365 195936002065305206645131)
                    ·
                      rfl

theorem cell22_572376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_572376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572376 prefixEnd_572376 := by exact prefixLift 572376
  have htrace : WordTrace (prefixWord ++ tailWord_572376) baseStart_572376 baseEnd_572376 := by
    simpa [prefixWord, tailWord_572376, baseEnd_572376] using wordTrace_append hprefix tailTrace_572376
  have hstable : (prefixWord ++ tailWord_572376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572376).length < 2 ^ (prefixWord ++ tailWord_572376).sum := by decide
  have hdescent : baseEnd_572376 < baseStart_572376 := by decide
  rcases family_descends (prefixWord ++ tailWord_572376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572391 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 8]
def baseStart_572391 : Nat := 118140960795 + 572391 * 2 ^ 59
def prefixEnd_572391 : Nat := 4983230072969 + 3 ^ 40 * 572391 * 2
def baseEnd_572391 : Nat := 65313712290616722506695

theorem tailTrace_572391 : CollatzResearch.WordTrace tailWord_572391 prefixEnd_572391 65313712290616722506695 := by
  unfold tailWord_572391
  simp only [CollatzResearch.WordTrace]
  refine ⟨20876814869332638445109027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13917876579555092296739351 20876814869332638445109027)
  ·
    refine ⟨31315222303998957667663541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20876814869332638445109027 31315222303998957667663541)
    ·
      refine ⟨2935802090999902281343457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31315222303998957667663541 2935802090999902281343457)
      ·
        refine ⟨2201851568249926711007593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2935802090999902281343457 2201851568249926711007593)
        ·
          refine ⟨1651388676187445033255695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2201851568249926711007593 1651388676187445033255695)
          ·
            refine ⟨2477083014281167549883543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1651388676187445033255695 2477083014281167549883543)
            ·
              refine ⟨3715624521421751324825315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2477083014281167549883543 3715624521421751324825315)
              ·
                refine ⟨5573436782132626987237973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3715624521421751324825315 5573436782132626987237973)
                ·
                  refine ⟨65313712290616722506695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5573436782132626987237973 65313712290616722506695)
                  ·
                    rfl

theorem cell22_572391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 8].length) (baseStart_572391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572391 prefixEnd_572391 := by exact prefixLift 572391
  have htrace : WordTrace (prefixWord ++ tailWord_572391) baseStart_572391 baseEnd_572391 := by
    simpa [prefixWord, tailWord_572391, baseEnd_572391] using wordTrace_append hprefix tailTrace_572391
  have hstable : (prefixWord ++ tailWord_572391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572391).length < 2 ^ (prefixWord ++ tailWord_572391).sum := by decide
  have hdescent : baseEnd_572391 < baseStart_572391 := by decide
  rcases family_descends (prefixWord ++ tailWord_572391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572421 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 4, 4]
def baseStart_572421 : Nat := 118140960795 + 572421 * 2 ^ 59
def prefixEnd_572421 : Nat := 4983230072969 + 3 ^ 40 * 572421 * 2
def baseEnd_572421 : Nat := 195951406484940089269993

theorem tailTrace_572421 : CollatzResearch.WordTrace tailWord_572421 prefixEnd_572421 195951406484940089269993 := by
  unfold tailWord_572421
  simp only [CollatzResearch.WordTrace]
  refine ⟨20877909059223953568701117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13918606039482635712467411 20877909059223953568701117)
  ·
    refine ⟨7829215897208982588262919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20877909059223953568701117 7829215897208982588262919)
    ·
      refine ⟨11743823845813473882394379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7829215897208982588262919 11743823845813473882394379)
      ·
        refine ⟨17615735768720210823591569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11743823845813473882394379 17615735768720210823591569)
        ·
          refine ⟨13211801826540158117693677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17615735768720210823591569 13211801826540158117693677)
          ·
            refine ⟨4954425684952559294135129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13211801826540158117693677 4954425684952559294135129)
            ·
              refine ⟨3715819263714419470601347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4954425684952559294135129 3715819263714419470601347)
              ·
                refine ⟨5573728895571629205902021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3715819263714419470601347 5573728895571629205902021)
                ·
                  refine ⟨1045074167919680476106629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5573728895571629205902021 1045074167919680476106629)
                  ·
                    refine ⟨195951406484940089269993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1045074167919680476106629 195951406484940089269993)
                    ·
                      rfl

theorem cell22_572421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_572421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572421 prefixEnd_572421 := by exact prefixLift 572421
  have htrace : WordTrace (prefixWord ++ tailWord_572421) baseStart_572421 baseEnd_572421 := by
    simpa [prefixWord, tailWord_572421, baseEnd_572421] using wordTrace_append hprefix tailTrace_572421
  have hstable : (prefixWord ++ tailWord_572421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572421).length < 2 ^ (prefixWord ++ tailWord_572421).sum := by decide
  have hdescent : baseEnd_572421 < baseStart_572421 := by decide
  rcases family_descends (prefixWord ++ tailWord_572421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572423 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 4, 3]
def baseStart_572423 : Nat := 118140960795 + 572423 * 2 ^ 59
def prefixEnd_572423 : Nat := 4983230072969 + 3 ^ 40 * 572423 * 2
def baseEnd_572423 : Nat := 195952091125812750719987

theorem tailTrace_572423 : CollatzResearch.WordTrace tailWord_572423 prefixEnd_572423 195952091125812750719987 := by
  unfold tailWord_572423
  simp only [CollatzResearch.WordTrace]
  refine ⟨20877982005216707910273923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13918654670144471940182615 20877982005216707910273923)
  ·
    refine ⟨31316973007825061865410885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20877982005216707910273923 31316973007825061865410885)
    ·
      refine ⟨5871932438967199099764541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31316973007825061865410885 5871932438967199099764541)
      ·
        refine ⟨2201974664612699662411703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5871932438967199099764541 2201974664612699662411703)
        ·
          refine ⟨3302961996919049493617555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2201974664612699662411703 3302961996919049493617555)
          ·
            refine ⟨4954442995378574240426333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3302961996919049493617555 4954442995378574240426333)
            ·
              refine ⟨1857916123266965340159875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4954442995378574240426333 1857916123266965340159875)
              ·
                refine ⟨2786874184900448010239813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1857916123266965340159875 2786874184900448010239813)
                ·
                  refine ⟨522538909668834001919965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2786874184900448010239813 522538909668834001919965)
                  ·
                    refine ⟨195952091125812750719987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 522538909668834001919965 195952091125812750719987)
                    ·
                      rfl

theorem cell22_572423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_572423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572423 prefixEnd_572423 := by exact prefixLift 572423
  have htrace : WordTrace (prefixWord ++ tailWord_572423) baseStart_572423 baseEnd_572423 := by
    simpa [prefixWord, tailWord_572423, baseEnd_572423] using wordTrace_append hprefix tailTrace_572423
  have hstable : (prefixWord ++ tailWord_572423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572423).length < 2 ^ (prefixWord ++ tailWord_572423).sum := by decide
  have hdescent : baseEnd_572423 < baseStart_572423 := by decide
  rcases family_descends (prefixWord ++ tailWord_572423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572485 : List Nat := [1, 3, 1, 1, 1, 3, 2, 6, 1, 3]
def baseStart_572485 : Nat := 118140960795 + 572485 * 2 ^ 59
def prefixEnd_572485 : Nat := 4983230072969 + 3 ^ 40 * 572485 * 2
def baseEnd_572485 : Nat := 195973314992865255669797

theorem tailTrace_572485 : CollatzResearch.WordTrace tailWord_572485 prefixEnd_572485 195973314992865255669797 := by
  unfold tailWord_572485
  simp only [CollatzResearch.WordTrace]
  refine ⟨20880243330992092499030909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13920162220661394999353939 20880243330992092499030909)
  ·
    refine ⟨7830091249122034687136591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20880243330992092499030909 7830091249122034687136591)
    ·
      refine ⟨11745136873683052030704887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7830091249122034687136591 11745136873683052030704887)
      ·
        refine ⟨17617705310524578046057331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11745136873683052030704887 17617705310524578046057331)
        ·
          refine ⟨26426557965786867069085997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17617705310524578046057331 26426557965786867069085997)
          ·
            refine ⟨9909959237170075150907249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26426557965786867069085997 9909959237170075150907249)
            ·
              refine ⟨7432469427877556363180437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9909959237170075150907249 7432469427877556363180437)
              ·
                refine ⟨348397004431760454524083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7432469427877556363180437 348397004431760454524083)
                ·
                  refine ⟨522595506647640681786125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348397004431760454524083 522595506647640681786125)
                  ·
                    refine ⟨195973314992865255669797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 522595506647640681786125 195973314992865255669797)
                    ·
                      rfl

theorem cell22_572485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 1, 3].length) (baseStart_572485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572485 prefixEnd_572485 := by exact prefixLift 572485
  have htrace : WordTrace (prefixWord ++ tailWord_572485) baseStart_572485 baseEnd_572485 := by
    simpa [prefixWord, tailWord_572485, baseEnd_572485] using wordTrace_append hprefix tailTrace_572485
  have hstable : (prefixWord ++ tailWord_572485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572485).length < 2 ^ (prefixWord ++ tailWord_572485).sum := by decide
  have hdescent : baseEnd_572485 < baseStart_572485 := by decide
  rcases family_descends (prefixWord ++ tailWord_572485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572496 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 2, 5]
def baseStart_572496 : Nat := 118140960795 + 572496 * 2 ^ 59
def prefixEnd_572496 : Nat := 4983230072969 + 3 ^ 40 * 572496 * 2
def baseEnd_572496 : Nat := 195977080517664893644763

theorem tailTrace_572496 : CollatzResearch.WordTrace tailWord_572496 prefixEnd_572496 195977080517664893644763 := by
  unfold tailWord_572496
  simp only [CollatzResearch.WordTrace]
  refine ⟨10440322266976120688840671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13920429689301494251787561 10440322266976120688840671)
  ·
    refine ⟨15660483400464181033261007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10440322266976120688840671 15660483400464181033261007)
    ·
      refine ⟨23490725100696271549891511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15660483400464181033261007 23490725100696271549891511)
      ·
        refine ⟨35236087651044407324837267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23490725100696271549891511 35236087651044407324837267)
        ·
          refine ⟨52854131476566610987255901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35236087651044407324837267 52854131476566610987255901)
          ·
            refine ⟨19820299303712479120220963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52854131476566610987255901 19820299303712479120220963)
            ·
              refine ⟨29730448955568718680331445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19820299303712479120220963 29730448955568718680331445)
              ·
                refine ⟨2787229589584567376281073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29730448955568718680331445 2787229589584567376281073)
                ·
                  refine ⟨2090422192188425532210805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2787229589584567376281073 2090422192188425532210805)
                  ·
                    refine ⟨195977080517664893644763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2090422192188425532210805 195977080517664893644763)
                    ·
                      rfl

theorem cell22_572496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_572496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572496 prefixEnd_572496 := by exact prefixLift 572496
  have htrace : WordTrace (prefixWord ++ tailWord_572496) baseStart_572496 baseEnd_572496 := by
    simpa [prefixWord, tailWord_572496, baseEnd_572496] using wordTrace_append hprefix tailTrace_572496
  have hstable : (prefixWord ++ tailWord_572496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572496).length < 2 ^ (prefixWord ++ tailWord_572496).sum := by decide
  have hdescent : baseEnd_572496 < baseStart_572496 := by decide
  rcases family_descends (prefixWord ++ tailWord_572496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572573 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_572573 : Nat := 118140960795 + 572573 * 2 ^ 59
def prefixEnd_572573 : Nat := 4983230072969 + 3 ^ 40 * 572573 * 2
def baseEnd_572573 : Nat := 196003439191262359469527

theorem tailTrace_572573 : CollatzResearch.WordTrace tailWord_572573 prefixEnd_572573 196003439191262359469527 := by
  unfold tailWord_572573
  simp only [CollatzResearch.WordTrace]
  refine ⟨20883452954673283528234373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13922301969782189018822915 20883452954673283528234373)
  ·
    refine ⟨3915647429001240661543945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20883452954673283528234373 3915647429001240661543945)
    ·
      refine ⟨2936735571750930496157959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3915647429001240661543945 2936735571750930496157959)
      ·
        refine ⟨4405103357626395744236939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2936735571750930496157959 4405103357626395744236939)
        ·
          refine ⟨6607655036439593616355409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4405103357626395744236939 6607655036439593616355409)
          ·
            refine ⟨4955741277329695212266557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6607655036439593616355409 4955741277329695212266557)
            ·
              refine ⟨1858402978998635704599959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4955741277329695212266557 1858402978998635704599959)
              ·
                refine ⟨2787604468497953556899939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1858402978998635704599959 2787604468497953556899939)
                ·
                  refine ⟨4181406702746930335349909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2787604468497953556899939 4181406702746930335349909)
                  ·
                    refine ⟨196003439191262359469527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4181406702746930335349909 196003439191262359469527)
                    ·
                      rfl

theorem cell22_572573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_572573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572573 prefixEnd_572573 := by exact prefixLift 572573
  have htrace : WordTrace (prefixWord ++ tailWord_572573) baseStart_572573 baseEnd_572573 := by
    simpa [prefixWord, tailWord_572573, baseEnd_572573] using wordTrace_append hprefix tailTrace_572573
  have hstable : (prefixWord ++ tailWord_572573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572573).length < 2 ^ (prefixWord ++ tailWord_572573).sum := by decide
  have hdescent : baseEnd_572573 < baseStart_572573 := by decide
  rcases family_descends (prefixWord ++ tailWord_572573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572622 : List Nat := [4, 1, 1, 1, 5, 2, 2, 6]
def baseStart_572622 : Nat := 118140960795 + 572622 * 2 ^ 59
def prefixEnd_572622 : Nat := 4983230072969 + 3 ^ 40 * 572622 * 2
def baseEnd_572622 : Nat := 21780023654738062777153

theorem tailTrace_572622 : CollatzResearch.WordTrace tailWord_572622 prefixEnd_572622 21780023654738062777153 := by
  unfold tailWord_572622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2610655016436970612096015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13923493420997176597845413 2610655016436970612096015)
  ·
    refine ⟨3915982524655455918144023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2610655016436970612096015 3915982524655455918144023)
    ·
      refine ⟨5873973786983183877216035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3915982524655455918144023 5873973786983183877216035)
      ·
        refine ⟨8810960680474775815824053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5873973786983183877216035 8810960680474775815824053)
        ·
          refine ⟨826027563794510232733505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8810960680474775815824053 826027563794510232733505)
          ·
            refine ⟨619520672845882674550129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 826027563794510232733505 619520672845882674550129)
            ·
              refine ⟨464640504634412005912597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619520672845882674550129 464640504634412005912597)
              ·
                refine ⟨21780023654738062777153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 464640504634412005912597 21780023654738062777153)
                ·
                  rfl

theorem cell22_572622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_572622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572622 prefixEnd_572622 := by exact prefixLift 572622
  have htrace : WordTrace (prefixWord ++ tailWord_572622) baseStart_572622 baseEnd_572622 := by
    simpa [prefixWord, tailWord_572622, baseEnd_572622] using wordTrace_append hprefix tailTrace_572622
  have hstable : (prefixWord ++ tailWord_572622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572622).length < 2 ^ (prefixWord ++ tailWord_572622).sum := by decide
  have hdescent : baseEnd_572622 < baseStart_572622 := by decide
  rcases family_descends (prefixWord ++ tailWord_572622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572660 : List Nat := [2, 6, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_572660 : Nat := 118140960795 + 572660 * 2 ^ 59
def prefixEnd_572660 : Nat := 4983230072969 + 3 ^ 40 * 572660 * 2
def baseEnd_572660 : Nat := 196033221069223132544261

theorem tailTrace_572660 : CollatzResearch.WordTrace tailWord_572660 prefixEnd_572660 196033221069223132544261 := by
  unfold tailWord_572660
  simp only [CollatzResearch.WordTrace]
  refine ⟨10443313052679048693325717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13924417403572064924434289 10443313052679048693325717)
  ·
    refine ⟨489530299344330407499643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10443313052679048693325717 489530299344330407499643)
    ·
      refine ⟨734295449016495611249465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 489530299344330407499643 734295449016495611249465)
      ·
        refine ⟨550721586762371708437099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 734295449016495611249465 550721586762371708437099)
        ·
          refine ⟨826082380143557562655649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550721586762371708437099 826082380143557562655649)
          ·
            refine ⟨619561785107668171991737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 826082380143557562655649 619561785107668171991737)
            ·
              refine ⟨464671338830751128993803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619561785107668171991737 464671338830751128993803)
              ·
                refine ⟨697007008246126693490705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464671338830751128993803 697007008246126693490705)
                ·
                  refine ⟨522755256184595020118029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 697007008246126693490705 522755256184595020118029)
                  ·
                    refine ⟨196033221069223132544261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 522755256184595020118029 196033221069223132544261)
                    ·
                      rfl

theorem cell22_572660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_572660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572660 prefixEnd_572660 := by exact prefixLift 572660
  have htrace : WordTrace (prefixWord ++ tailWord_572660) baseStart_572660 baseEnd_572660 := by
    simpa [prefixWord, tailWord_572660, baseEnd_572660] using wordTrace_append hprefix tailTrace_572660
  have hstable : (prefixWord ++ tailWord_572660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572660).length < 2 ^ (prefixWord ++ tailWord_572660).sum := by decide
  have hdescent : baseEnd_572660 < baseStart_572660 := by decide
  rcases family_descends (prefixWord ++ tailWord_572660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572663 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 5, 4]
def baseStart_572663 : Nat := 118140960795 + 572663 * 2 ^ 59
def prefixEnd_572663 : Nat := 4983230072969 + 3 ^ 40 * 572663 * 2
def baseEnd_572663 : Nat := 196034248030532124719251

theorem tailTrace_572663 : CollatzResearch.WordTrace tailWord_572663 prefixEnd_572663 196034248030532124719251 := by
  unfold tailWord_572663
  simp only [CollatzResearch.WordTrace]
  refine ⟨20886735524347228899010643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13924490349564819266007095 20886735524347228899010643)
  ·
    refine ⟨31330103286520843348515965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20886735524347228899010643 31330103286520843348515965)
    ·
      refine ⟨11748788732445316255693487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31330103286520843348515965 11748788732445316255693487)
      ·
        refine ⟨17623183098667974383540231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11748788732445316255693487 17623183098667974383540231)
        ·
          refine ⟨26434774648001961575310347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17623183098667974383540231 26434774648001961575310347)
          ·
            refine ⟨39652161972002942362965521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26434774648001961575310347 39652161972002942362965521)
            ·
              refine ⟨29739121479002206772224141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39652161972002942362965521 29739121479002206772224141)
              ·
                refine ⟨11152170554625827539584053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29739121479002206772224141 11152170554625827539584053)
                ·
                  refine ⟨1045515989496171331836005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11152170554625827539584053 1045515989496171331836005)
                  ·
                    refine ⟨196034248030532124719251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1045515989496171331836005 196034248030532124719251)
                    ·
                      rfl

theorem cell22_572663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_572663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572663 prefixEnd_572663 := by exact prefixLift 572663
  have htrace : WordTrace (prefixWord ++ tailWord_572663) baseStart_572663 baseEnd_572663 := by
    simpa [prefixWord, tailWord_572663, baseEnd_572663] using wordTrace_append hprefix tailTrace_572663
  have hstable : (prefixWord ++ tailWord_572663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572663).length < 2 ^ (prefixWord ++ tailWord_572663).sum := by decide
  have hdescent : baseEnd_572663 < baseStart_572663 := by decide
  rcases family_descends (prefixWord ++ tailWord_572663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572755 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 5, 3]
def baseStart_572755 : Nat := 118140960795 + 572755 * 2 ^ 59
def prefixEnd_572755 : Nat := 4983230072969 + 3 ^ 40 * 572755 * 2
def baseEnd_572755 : Nat := 196065741510674551418969

theorem tailTrace_572755 : CollatzResearch.WordTrace tailWord_572755 prefixEnd_572755 196065741510674551418969 := by
  unfold tailWord_572755
  simp only [CollatzResearch.WordTrace]
  refine ⟨20890091040013928611359719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13926727360009285740906479 20890091040013928611359719)
  ·
    refine ⟨31335136560020892917039579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20890091040013928611359719 31335136560020892917039579)
    ·
      refine ⟨47002704840031339375559369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31335136560020892917039579 47002704840031339375559369)
      ·
        refine ⟨35252028630023504531669527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47002704840031339375559369 35252028630023504531669527)
        ·
          refine ⟨52878042945035256797504291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35252028630023504531669527 52878042945035256797504291)
          ·
            refine ⟨79317064417552885196256437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52878042945035256797504291 79317064417552885196256437)
            ·
              refine ⟨7435974789145582987149041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79317064417552885196256437 7435974789145582987149041)
              ·
                refine ⟨5576981091859187240361781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7435974789145582987149041 5576981091859187240361781)
                ·
                  refine ⟨522841977361798803783917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5576981091859187240361781 522841977361798803783917)
                  ·
                    refine ⟨196065741510674551418969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 522841977361798803783917 196065741510674551418969)
                    ·
                      rfl

theorem cell22_572755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 3].length) (baseStart_572755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572755 prefixEnd_572755 := by exact prefixLift 572755
  have htrace : WordTrace (prefixWord ++ tailWord_572755) baseStart_572755 baseEnd_572755 := by
    simpa [prefixWord, tailWord_572755, baseEnd_572755] using wordTrace_append hprefix tailTrace_572755
  have hstable : (prefixWord ++ tailWord_572755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572755).length < 2 ^ (prefixWord ++ tailWord_572755).sum := by decide
  have hdescent : baseEnd_572755 < baseStart_572755 := by decide
  rcases family_descends (prefixWord ++ tailWord_572755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572772 : List Nat := [2, 3, 1, 1, 3, 2, 1, 3, 3, 3]
def baseStart_572772 : Nat := 118140960795 + 572772 * 2 ^ 59
def prefixEnd_572772 : Nat := 4983230072969 + 3 ^ 40 * 572772 * 2
def baseEnd_572772 : Nat := 196071560958092173743917

theorem tailTrace_572772 : CollatzResearch.WordTrace tailWord_572772 prefixEnd_572772 196071560958092173743917 := by
  unfold tailWord_572772
  simp only [CollatzResearch.WordTrace]
  refine ⟨10445355540476170257364285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13927140720634893676485713 10445355540476170257364285)
  ·
    refine ⟨3917008327678563846511607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10445355540476170257364285 3917008327678563846511607)
    ·
      refine ⟨5875512491517845769767411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3917008327678563846511607 5875512491517845769767411)
      ·
        refine ⟨8813268737276768654651117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5875512491517845769767411 8813268737276768654651117)
        ·
          refine ⟨3304975776478788245494169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8813268737276768654651117 3304975776478788245494169)
          ·
            refine ⟨2478731832359091184120627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3304975776478788245494169 2478731832359091184120627)
            ·
              refine ⟨3718097748538636776180941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2478731832359091184120627 3718097748538636776180941)
              ·
                refine ⟨1394286655701988791067853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3718097748538636776180941 1394286655701988791067853)
                ·
                  refine ⟨522857495888245796650445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1394286655701988791067853 522857495888245796650445)
                  ·
                    refine ⟨196071560958092173743917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 522857495888245796650445 196071560958092173743917)
                    ·
                      rfl

theorem cell22_572772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_572772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572772 prefixEnd_572772 := by exact prefixLift 572772
  have htrace : WordTrace (prefixWord ++ tailWord_572772) baseStart_572772 baseEnd_572772 := by
    simpa [prefixWord, tailWord_572772, baseEnd_572772] using wordTrace_append hprefix tailTrace_572772
  have hstable : (prefixWord ++ tailWord_572772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572772).length < 2 ^ (prefixWord ++ tailWord_572772).sum := by decide
  have hdescent : baseEnd_572772 < baseStart_572772 := by decide
  rcases family_descends (prefixWord ++ tailWord_572772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572785 : List Nat := [1, 2, 2, 2, 1, 2, 2, 5, 5]
def baseStart_572785 : Nat := 118140960795 + 572785 * 2 ^ 59
def prefixEnd_572785 : Nat := 4983230072969 + 3 ^ 40 * 572785 * 2
def baseEnd_572785 : Nat := 65358670374588157722959

theorem tailTrace_572785 : CollatzResearch.WordTrace tailWord_572785 prefixEnd_572785 65358670374588157722959 := by
  unfold tailWord_572785
  simp only [CollatzResearch.WordTrace]
  refine ⟨20891185229905243734951809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13927456819936829156634539 20891185229905243734951809)
  ·
    refine ⟨15668388922428932801213857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20891185229905243734951809 15668388922428932801213857)
    ·
      refine ⟨11751291691821699600910393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15668388922428932801213857 11751291691821699600910393)
      ·
        refine ⟨8813468768866274700682795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11751291691821699600910393 8813468768866274700682795)
        ·
          refine ⟨13220203153299412051024193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8813468768866274700682795 13220203153299412051024193)
          ·
            refine ⟨9915152364974559038268145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13220203153299412051024193 9915152364974559038268145)
            ·
              refine ⟨7436364273730919278701109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9915152364974559038268145 7436364273730919278701109)
              ·
                refine ⟨697159150662273682378229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7436364273730919278701109 697159150662273682378229)
                ·
                  refine ⟨65358670374588157722959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 697159150662273682378229 65358670374588157722959)
                  ·
                    rfl

theorem cell22_572785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 5].length) (baseStart_572785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572785 prefixEnd_572785 := by exact prefixLift 572785
  have htrace : WordTrace (prefixWord ++ tailWord_572785) baseStart_572785 baseEnd_572785 := by
    simpa [prefixWord, tailWord_572785, baseEnd_572785] using wordTrace_append hprefix tailTrace_572785
  have hstable : (prefixWord ++ tailWord_572785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572785).length < 2 ^ (prefixWord ++ tailWord_572785).sum := by decide
  have hdescent : baseEnd_572785 < baseStart_572785 := by decide
  rcases family_descends (prefixWord ++ tailWord_572785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572984 : List Nat := [2, 1, 2, 1, 4, 2, 2, 3, 1, 4]
def baseStart_572984 : Nat := 118140960795 + 572984 * 2 ^ 59
def prefixEnd_572984 : Nat := 4983230072969 + 3 ^ 40 * 572984 * 2
def baseEnd_572984 : Nat := 196144132890594287443267

theorem tailTrace_572984 : CollatzResearch.WordTrace tailWord_572984 prefixEnd_572984 196144132890594287443267 := by
  unfold tailWord_572984
  simp only [CollatzResearch.WordTrace]
  refine ⟨10449221678092150360723003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13932295570789533814297337 10449221678092150360723003)
  ·
    refine ⟨15673832517138225541084505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10449221678092150360723003 15673832517138225541084505)
    ·
      refine ⟨11755374387853669155813379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15673832517138225541084505 11755374387853669155813379)
      ·
        refine ⟨17633061581780503733720069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11755374387853669155813379 17633061581780503733720069)
        ·
          refine ⟨3306199046583844450072513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17633061581780503733720069 3306199046583844450072513)
          ·
            refine ⟨2479649284937883337554385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3306199046583844450072513 2479649284937883337554385)
            ·
              refine ⟨1859736963703412503165789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2479649284937883337554385 1859736963703412503165789)
              ·
                refine ⟨697401361388779688687171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1859736963703412503165789 697401361388779688687171)
                ·
                  refine ⟨1046102042083169533030757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 697401361388779688687171 1046102042083169533030757)
                  ·
                    refine ⟨196144132890594287443267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1046102042083169533030757 196144132890594287443267)
                    ·
                      rfl

theorem cell22_572984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_572984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_572984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_572984 prefixEnd_572984 := by exact prefixLift 572984
  have htrace : WordTrace (prefixWord ++ tailWord_572984) baseStart_572984 baseEnd_572984 := by
    simpa [prefixWord, tailWord_572984, baseEnd_572984] using wordTrace_append hprefix tailTrace_572984
  have hstable : (prefixWord ++ tailWord_572984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572984).length < 2 ^ (prefixWord ++ tailWord_572984).sum := by decide
  have hdescent : baseEnd_572984 < baseStart_572984 := by decide
  rcases family_descends (prefixWord ++ tailWord_572984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573005 : List Nat := [1, 6, 1, 1, 4, 1, 2, 1, 5]
def baseStart_573005 : Nat := 118140960795 + 573005 * 2 ^ 59
def prefixEnd_573005 : Nat := 4983230072969 + 3 ^ 40 * 573005 * 2
def baseEnd_573005 : Nat := 65383773873252410889401

theorem tailTrace_573005 : CollatzResearch.WordTrace tailWord_573005 prefixEnd_573005 65383773873252410889401 := by
  unfold tailWord_573005
  simp only [CollatzResearch.WordTrace]
  refine ⟨20899209289108221307960469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13932806192738814205306979 20899209289108221307960469)
  ·
    refine ⟨979650435426947873810647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20899209289108221307960469 979650435426947873810647)
    ·
      refine ⟨1469475653140421810715971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 979650435426947873810647 1469475653140421810715971)
      ·
        refine ⟨2204213479710632716073957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1469475653140421810715971 2204213479710632716073957)
        ·
          refine ⟨413290027445743634263867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2204213479710632716073957 413290027445743634263867)
          ·
            refine ⟨619935041168615451395801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413290027445743634263867 619935041168615451395801)
            ·
              refine ⟨464951280876461588546851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619935041168615451395801 464951280876461588546851)
              ·
                refine ⟨697426921314692382820277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464951280876461588546851 697426921314692382820277)
                ·
                  refine ⟨65383773873252410889401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 697426921314692382820277 65383773873252410889401)
                  ·
                    rfl

theorem cell22_573005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_573005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573005 prefixEnd_573005 := by exact prefixLift 573005
  have htrace : WordTrace (prefixWord ++ tailWord_573005) baseStart_573005 baseEnd_573005 := by
    simpa [prefixWord, tailWord_573005, baseEnd_573005] using wordTrace_append hprefix tailTrace_573005
  have hstable : (prefixWord ++ tailWord_573005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573005).length < 2 ^ (prefixWord ++ tailWord_573005).sum := by decide
  have hdescent : baseEnd_573005 < baseStart_573005 := by decide
  rcases family_descends (prefixWord ++ tailWord_573005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573027 : List Nat := [1, 1, 1, 5, 1, 3, 2, 8]
def baseStart_573027 : Nat := 118140960795 + 573027 * 2 ^ 59
def prefixEnd_573027 : Nat := 4983230072969 + 3 ^ 40 * 573027 * 2
def baseEnd_573027 : Nat := 21795428074372945402015

theorem tailTrace_573027 : CollatzResearch.WordTrace tailWord_573027 prefixEnd_573027 21795428074372945402015 := by
  unfold tailWord_573027
  simp only [CollatzResearch.WordTrace]
  refine ⟨20900011695028519065261335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13933341130019012710174223 20900011695028519065261335)
  ·
    refine ⟨31350017542542778597892003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20900011695028519065261335 31350017542542778597892003)
    ·
      refine ⟨47025026313814167896838005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31350017542542778597892003 47025026313814167896838005)
      ·
        refine ⟨4408596216920078240328563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47025026313814167896838005 4408596216920078240328563)
        ·
          refine ⟨6612894325380117360492845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4408596216920078240328563 6612894325380117360492845)
          ·
            refine ⟨2479835372017544010184817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6612894325380117360492845 2479835372017544010184817)
            ·
              refine ⟨1859876529013158007638613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2479835372017544010184817 1859876529013158007638613)
              ·
                refine ⟨21795428074372945402015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1859876529013158007638613 21795428074372945402015)
                ·
                  rfl

theorem cell22_573027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 8].length) (baseStart_573027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573027 prefixEnd_573027 := by exact prefixLift 573027
  have htrace : WordTrace (prefixWord ++ tailWord_573027) baseStart_573027 baseEnd_573027 := by
    simpa [prefixWord, tailWord_573027, baseEnd_573027] using wordTrace_append hprefix tailTrace_573027
  have hstable : (prefixWord ++ tailWord_573027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573027).length < 2 ^ (prefixWord ++ tailWord_573027).sum := by decide
  have hdescent : baseEnd_573027 < baseStart_573027 := by decide
  rcases family_descends (prefixWord ++ tailWord_573027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573029 : List Nat := [1, 3, 1, 3, 3, 1, 1, 3, 2, 4]
def baseStart_573029 : Nat := 118140960795 + 573029 * 2 ^ 59
def prefixEnd_573029 : Nat := 4983230072969 + 3 ^ 40 * 573029 * 2
def baseEnd_573029 : Nat := 196159537310229170068129

theorem tailTrace_573029 : CollatzResearch.WordTrace tailWord_573029 prefixEnd_573029 196159537310229170068129 := by
  unfold tailWord_573029
  simp only [CollatzResearch.WordTrace]
  refine ⟨20900084641021273406834141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13933389760680848937889427 20900084641021273406834141)
  ·
    refine ⟨7837531740382977527562803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20900084641021273406834141 7837531740382977527562803)
    ·
      refine ⟨11756297610574466291344205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7837531740382977527562803 11756297610574466291344205)
      ·
        refine ⟨4408611603965424859254077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11756297610574466291344205 4408611603965424859254077)
        ·
          refine ⟨1653229351487034322220279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4408611603965424859254077 1653229351487034322220279)
          ·
            refine ⟨2479844027230551483330419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1653229351487034322220279 2479844027230551483330419)
            ·
              refine ⟨3719766040845827224995629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2479844027230551483330419 3719766040845827224995629)
              ·
                refine ⟨1394912265317185209373361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3719766040845827224995629 1394912265317185209373361)
                ·
                  refine ⟨1046184198987888907030021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1394912265317185209373361 1046184198987888907030021)
                  ·
                    refine ⟨196159537310229170068129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1046184198987888907030021 196159537310229170068129)
                    ·
                      rfl

theorem cell22_573029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_573029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573029 prefixEnd_573029 := by exact prefixLift 573029
  have htrace : WordTrace (prefixWord ++ tailWord_573029) baseStart_573029 baseEnd_573029 := by
    simpa [prefixWord, tailWord_573029, baseEnd_573029] using wordTrace_append hprefix tailTrace_573029
  have hstable : (prefixWord ++ tailWord_573029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573029).length < 2 ^ (prefixWord ++ tailWord_573029).sum := by decide
  have hdescent : baseEnd_573029 < baseStart_573029 := by decide
  rcases family_descends (prefixWord ++ tailWord_573029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573046 : List Nat := [5, 1, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_573046 : Nat := 118140960795 + 573046 * 2 ^ 59
def prefixEnd_573046 : Nat := 4983230072969 + 3 ^ 40 * 573046 * 2
def baseEnd_573046 : Nat := 196165356757646792393077

theorem tailTrace_573046 : CollatzResearch.WordTrace tailWord_573046 prefixEnd_573046 196165356757646792393077 := by
  unfold tailWord_573046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1306294042622480331887687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13933803121306456873468661 1306294042622480331887687)
  ·
    refine ⟨1959441063933720497831531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1306294042622480331887687 1959441063933720497831531)
    ·
      refine ⟨2939161595900580746747297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1959441063933720497831531 2939161595900580746747297)
      ·
        refine ⟨2204371196925435560060473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2939161595900580746747297 2204371196925435560060473)
        ·
          refine ⟨1653278397694076670045355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2204371196925435560060473 1653278397694076670045355)
          ·
            refine ⟨2479917596541115005068033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1653278397694076670045355 2479917596541115005068033)
            ·
              refine ⟨1859938197405836253801025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2479917596541115005068033 1859938197405836253801025)
              ·
                refine ⟨1394953648054377190350769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1859938197405836253801025 1394953648054377190350769)
                ·
                  refine ⟨1046215236040782892763077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1394953648054377190350769 1046215236040782892763077)
                  ·
                    refine ⟨196165356757646792393077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1046215236040782892763077 196165356757646792393077)
                    ·
                      rfl

theorem cell22_573046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_573046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573046 prefixEnd_573046 := by exact prefixLift 573046
  have htrace : WordTrace (prefixWord ++ tailWord_573046) baseStart_573046 baseEnd_573046 := by
    simpa [prefixWord, tailWord_573046, baseEnd_573046] using wordTrace_append hprefix tailTrace_573046
  have hstable : (prefixWord ++ tailWord_573046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573046).length < 2 ^ (prefixWord ++ tailWord_573046).sum := by decide
  have hdescent : baseEnd_573046 < baseStart_573046 := by decide
  rcases family_descends (prefixWord ++ tailWord_573046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573059 : List Nat := [1, 1, 1, 3, 3, 1, 1, 5, 3, 3]
def baseStart_573059 : Nat := 118140960795 + 573059 * 2 ^ 59
def prefixEnd_573059 : Nat := 4983230072969 + 3 ^ 40 * 573059 * 2
def baseEnd_573059 : Nat := 196169806923319091818037

theorem tailTrace_573059 : CollatzResearch.WordTrace tailWord_573059 prefixEnd_573059 196169806923319091818037 := by
  unfold tailWord_573059
  simp only [CollatzResearch.WordTrace]
  refine ⟨20901178830912588530426231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13934119220608392353617487 20901178830912588530426231)
  ·
    refine ⟨31351768246368882795639347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20901178830912588530426231 31351768246368882795639347)
    ·
      refine ⟨47027652369553324193459021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31351768246368882795639347 47027652369553324193459021)
      ·
        refine ⟨17635369638582496572547133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47027652369553324193459021 17635369638582496572547133)
        ·
          refine ⟨6613263614468436214705175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17635369638582496572547133 6613263614468436214705175)
          ·
            refine ⟨9919895421702654322057763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6613263614468436214705175 9919895421702654322057763)
            ·
              refine ⟨14879843132553981483086645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9919895421702654322057763 14879843132553981483086645)
              ·
                refine ⟨1394985293676935764039373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14879843132553981483086645 1394985293676935764039373)
                ·
                  refine ⟨523119485128850911514765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1394985293676935764039373 523119485128850911514765)
                  ·
                    refine ⟨196169806923319091818037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 523119485128850911514765 196169806923319091818037)
                    ·
                      rfl

theorem cell22_573059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 3].length) (baseStart_573059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573059 prefixEnd_573059 := by exact prefixLift 573059
  have htrace : WordTrace (prefixWord ++ tailWord_573059) baseStart_573059 baseEnd_573059 := by
    simpa [prefixWord, tailWord_573059, baseEnd_573059] using wordTrace_append hprefix tailTrace_573059
  have hstable : (prefixWord ++ tailWord_573059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573059).length < 2 ^ (prefixWord ++ tailWord_573059).sum := by decide
  have hdescent : baseEnd_573059 < baseStart_573059 := by decide
  rcases family_descends (prefixWord ++ tailWord_573059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573110 : List Nat := [5, 1, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_573110 : Nat := 118140960795 + 573110 * 2 ^ 59
def prefixEnd_573110 : Nat := 4983230072969 + 3 ^ 40 * 573110 * 2
def baseEnd_573110 : Nat := 196187265265571958792881

theorem tailTrace_573110 : CollatzResearch.WordTrace tailWord_573110 prefixEnd_573110 196187265265571958792881 := by
  unfold tailWord_573110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1306439934607989015033299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13935359302485216160355189 1306439934607989015033299)
  ·
    refine ⟨1959659901911983522549949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1306439934607989015033299 1959659901911983522549949)
    ·
      refine ⟨734872463216993820956231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1959659901911983522549949 734872463216993820956231)
      ·
        refine ⟨1102308694825490731434347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734872463216993820956231 1102308694825490731434347)
        ·
          refine ⟨1653463042238236097151521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1102308694825490731434347 1653463042238236097151521)
          ·
            refine ⟨1240097281678677072863641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1653463042238236097151521 1240097281678677072863641)
            ·
              refine ⟨930072961259007804647731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1240097281678677072863641 930072961259007804647731)
              ·
                refine ⟨1395109441888511706971597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 930072961259007804647731 1395109441888511706971597)
                ·
                  refine ⟨523166040708191890114349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1395109441888511706971597 523166040708191890114349)
                  ·
                    refine ⟨196187265265571958792881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 523166040708191890114349 196187265265571958792881)
                    ·
                      rfl

theorem cell22_573110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_573110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573110 prefixEnd_573110 := by exact prefixLift 573110
  have htrace : WordTrace (prefixWord ++ tailWord_573110) baseStart_573110 baseEnd_573110 := by
    simpa [prefixWord, tailWord_573110, baseEnd_573110] using wordTrace_append hprefix tailTrace_573110
  have hstable : (prefixWord ++ tailWord_573110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573110).length < 2 ^ (prefixWord ++ tailWord_573110).sum := by decide
  have hdescent : baseEnd_573110 < baseStart_573110 := by decide
  rcases family_descends (prefixWord ++ tailWord_573110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573134 : List Nat := [4, 1, 1, 1, 3, 1, 1, 4, 6]
def baseStart_573134 : Nat := 118140960795 + 573134 * 2 ^ 59
def prefixEnd_573134 : Nat := 4983230072969 + 3 ^ 40 * 573134 * 2
def baseEnd_573134 : Nat := 65398493652014632064269

theorem tailTrace_573134 : CollatzResearch.WordTrace tailWord_573134 prefixEnd_573134 65398493652014632064269 := by
  unfold tailWord_573134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2612989288205109542425807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13935942870427250892937637 2612989288205109542425807)
  ·
    refine ⟨3919483932307664313638711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2612989288205109542425807 3919483932307664313638711)
    ·
      refine ⟨5879225898461496470458067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3919483932307664313638711 5879225898461496470458067)
      ·
        refine ⟨8818838847692244705687101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5879225898461496470458067 8818838847692244705687101)
        ·
          refine ⟨3307064567884591764632663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8818838847692244705687101 3307064567884591764632663)
          ·
            refine ⟨4960596851826887646948995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3307064567884591764632663 4960596851826887646948995)
            ·
              refine ⟨7440895277740331470423493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4960596851826887646948995 7440895277740331470423493)
              ·
                refine ⟨1395167864576312150704405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7440895277740331470423493 1395167864576312150704405)
                ·
                  refine ⟨65398493652014632064269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1395167864576312150704405 65398493652014632064269)
                  ·
                    rfl

theorem cell22_573134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_573134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573134 prefixEnd_573134 := by exact prefixLift 573134
  have htrace : WordTrace (prefixWord ++ tailWord_573134) baseStart_573134 baseEnd_573134 := by
    simpa [prefixWord, tailWord_573134, baseEnd_573134] using wordTrace_append hprefix tailTrace_573134
  have hstable : (prefixWord ++ tailWord_573134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573134).length < 2 ^ (prefixWord ++ tailWord_573134).sum := by decide
  have hdescent : baseEnd_573134 < baseStart_573134 := by decide
  rcases family_descends (prefixWord ++ tailWord_573134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573164 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 4, 4]
def baseStart_573164 : Nat := 118140960795 + 573164 * 2 ^ 59
def prefixEnd_573164 : Nat := 4983230072969 + 3 ^ 40 * 573164 * 2
def baseEnd_573164 : Nat := 196205750569133817942715

theorem tailTrace_573164 : CollatzResearch.WordTrace tailWord_573164 prefixEnd_573164 196205750569133817942715 := by
  unfold tailWord_573164
  simp only [CollatzResearch.WordTrace]
  refine ⟨10452504247766095731499273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13936672330354794308665697 10452504247766095731499273)
  ·
    refine ⟨7839378185824571798624455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10452504247766095731499273 7839378185824571798624455)
    ·
      refine ⟨11759067278736857697936683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7839378185824571798624455 11759067278736857697936683)
      ·
        refine ⟨17638600918105286546905025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11759067278736857697936683 17638600918105286546905025)
        ·
          refine ⟨13228950688578964910178769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17638600918105286546905025 13228950688578964910178769)
          ·
            refine ⟨9921713016434223682634077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13228950688578964910178769 9921713016434223682634077)
            ·
              refine ⟨3720642381162833880987779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9921713016434223682634077 3720642381162833880987779)
              ·
                refine ⟨5580963571744250821481669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3720642381162833880987779 5580963571744250821481669)
                ·
                  refine ⟨1046430669702047029027813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5580963571744250821481669 1046430669702047029027813)
                  ·
                    refine ⟨196205750569133817942715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1046430669702047029027813 196205750569133817942715)
                    ·
                      rfl

theorem cell22_573164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_573164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573164 prefixEnd_573164 := by exact prefixLift 573164
  have htrace : WordTrace (prefixWord ++ tailWord_573164) baseStart_573164 baseEnd_573164 := by
    simpa [prefixWord, tailWord_573164, baseEnd_573164] using wordTrace_append hprefix tailTrace_573164
  have hstable : (prefixWord ++ tailWord_573164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573164).length < 2 ^ (prefixWord ++ tailWord_573164).sum := by decide
  have hdescent : baseEnd_573164 < baseStart_573164 := by decide
  rcases family_descends (prefixWord ++ tailWord_573164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573166 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 4, 3]
def baseStart_573166 : Nat := 118140960795 + 573166 * 2 ^ 59
def prefixEnd_573166 : Nat := 4983230072969 + 3 ^ 40 * 573166 * 2
def baseEnd_573166 : Nat := 196206435210006479392709

theorem tailTrace_573166 : CollatzResearch.WordTrace tailWord_573166 prefixEnd_573166 196206435210006479392709 := by
  unfold tailWord_573166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2613135180190618225571419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13936720961016630536380901 2613135180190618225571419)
  ·
    refine ⟨3919702770285927338357129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2613135180190618225571419 3919702770285927338357129)
    ·
      refine ⟨2939777077714445503767847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3919702770285927338357129 2939777077714445503767847)
      ·
        refine ⟨4409665616571668255651771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2939777077714445503767847 4409665616571668255651771)
        ·
          refine ⟨6614498424857502383477657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4409665616571668255651771 6614498424857502383477657)
          ·
            refine ⟨4960873818643126787608243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6614498424857502383477657 4960873818643126787608243)
            ·
              refine ⟨7441310727964690181412365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4960873818643126787608243 7441310727964690181412365)
              ·
                refine ⟨2790491522986758818029637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7441310727964690181412365 2790491522986758818029637)
                ·
                  refine ⟨523217160560017278380557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2790491522986758818029637 523217160560017278380557)
                  ·
                    refine ⟨196206435210006479392709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 523217160560017278380557 196206435210006479392709)
                    ·
                      rfl

theorem cell22_573166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_573166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573166 prefixEnd_573166 := by exact prefixLift 573166
  have htrace : WordTrace (prefixWord ++ tailWord_573166) baseStart_573166 baseEnd_573166 := by
    simpa [prefixWord, tailWord_573166, baseEnd_573166] using wordTrace_append hprefix tailTrace_573166
  have hstable : (prefixWord ++ tailWord_573166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573166).length < 2 ^ (prefixWord ++ tailWord_573166).sum := by decide
  have hdescent : baseEnd_573166 < baseStart_573166 := by decide
  rcases family_descends (prefixWord ++ tailWord_573166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573183 : List Nat := [1, 1, 2, 2, 1, 3, 6, 1, 2, 3]
def baseStart_573183 : Nat := 118140960795 + 573183 * 2 ^ 59
def prefixEnd_573183 : Nat := 4983230072969 + 3 ^ 40 * 573183 * 2
def baseEnd_573183 : Nat := 196212254657424101717657

theorem tailTrace_573183 : CollatzResearch.WordTrace tailWord_573183 prefixEnd_573183 196212254657424101717657 := by
  unfold tailWord_573183
  simp only [CollatzResearch.WordTrace]
  refine ⟨20905701482463357707940203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13937134321642238471960135 20905701482463357707940203)
  ·
    refine ⟨31358552223695036561910305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20905701482463357707940203 31358552223695036561910305)
    ·
      refine ⟨23518914167771277421432729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31358552223695036561910305 23518914167771277421432729)
      ·
        refine ⟨17639185625828458066074547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23518914167771277421432729 17639185625828458066074547)
        ·
          refine ⟨26458778438742687099111821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17639185625828458066074547 26458778438742687099111821)
          ·
            refine ⟨9922041914528507662166933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26458778438742687099111821 9922041914528507662166933)
            ·
              refine ⟨465095714743523796664075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9922041914528507662166933 465095714743523796664075)
              ·
                refine ⟨697643572115285694996113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465095714743523796664075 697643572115285694996113)
                ·
                  refine ⟨523232679086464271247085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 697643572115285694996113 523232679086464271247085)
                  ·
                    refine ⟨196212254657424101717657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 523232679086464271247085 196212254657424101717657)
                    ·
                      rfl

theorem cell22_573183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 2, 3].length) (baseStart_573183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573183 prefixEnd_573183 := by exact prefixLift 573183
  have htrace : WordTrace (prefixWord ++ tailWord_573183) baseStart_573183 baseEnd_573183 := by
    simpa [prefixWord, tailWord_573183, baseEnd_573183] using wordTrace_append hprefix tailTrace_573183
  have hstable : (prefixWord ++ tailWord_573183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573183).length < 2 ^ (prefixWord ++ tailWord_573183).sum := by decide
  have hdescent : baseEnd_573183 < baseStart_573183 := by decide
  rcases family_descends (prefixWord ++ tailWord_573183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573204 : List Nat := [2, 4, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_573204 : Nat := 118140960795 + 573204 * 2 ^ 59
def prefixEnd_573204 : Nat := 4983230072969 + 3 ^ 40 * 573204 * 2
def baseEnd_573204 : Nat := 196219443386587046942593

theorem tailTrace_573204 : CollatzResearch.WordTrace tailWord_573204 prefixEnd_573204 196219443386587046942593 := by
  unfold tailWord_573204
  simp only [CollatzResearch.WordTrace]
  refine ⟨10453233707693639147227333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13937644943591518862969777 10453233707693639147227333)
  ·
    refine ⟨1959981320192557340105125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10453233707693639147227333 1959981320192557340105125)
    ·
      refine ⟨367496497536104501269711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1959981320192557340105125 367496497536104501269711)
      ·
        refine ⟨551244746304156751904567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367496497536104501269711 551244746304156751904567)
        ·
          refine ⟨826867119456235127856851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551244746304156751904567 826867119456235127856851)
          ·
            refine ⟨1240300679184352691785277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826867119456235127856851 1240300679184352691785277)
            ·
              refine ⟨465112754694132259419479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1240300679184352691785277 465112754694132259419479)
              ·
                refine ⟨697669132041198389129219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465112754694132259419479 697669132041198389129219)
                ·
                  refine ⟨1046503698061797583693829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 697669132041198389129219 1046503698061797583693829)
                  ·
                    refine ⟨196219443386587046942593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1046503698061797583693829 196219443386587046942593)
                    ·
                      rfl

theorem cell22_573204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_573204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573204 prefixEnd_573204 := by exact prefixLift 573204
  have htrace : WordTrace (prefixWord ++ tailWord_573204) baseStart_573204 baseEnd_573204 := by
    simpa [prefixWord, tailWord_573204, baseEnd_573204] using wordTrace_append hprefix tailTrace_573204
  have hstable : (prefixWord ++ tailWord_573204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573204).length < 2 ^ (prefixWord ++ tailWord_573204).sum := by decide
  have hdescent : baseEnd_573204 < baseStart_573204 := by decide
  rcases family_descends (prefixWord ++ tailWord_573204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573230 : List Nat := [4, 1, 3, 2, 3, 1, 1, 7]
def baseStart_573230 : Nat := 118140960795 + 573230 * 2 ^ 59
def prefixEnd_573230 : Nat := 4983230072969 + 3 ^ 40 * 573230 * 2
def baseEnd_573230 : Nat := 21803149301992405088057

theorem tailTrace_573230 : CollatzResearch.WordTrace tailWord_573230 prefixEnd_573230 21803149301992405088057 := by
  unfold tailWord_573230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2613426964161635591862643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13938277142195389823267429 2613426964161635591862643)
  ·
    refine ⟨3920140446242453387793965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2613426964161635591862643 3920140446242453387793965)
    ·
      refine ⟨1470052667340920020422737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3920140446242453387793965 1470052667340920020422737)
      ·
        refine ⟨1102539500505690015317053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1470052667340920020422737 1102539500505690015317053)
        ·
          refine ⟨413452312689633755743895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1102539500505690015317053 413452312689633755743895)
          ·
            refine ⟨620178469034450633615843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413452312689633755743895 620178469034450633615843)
            ·
              refine ⟨930267703551675950423765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620178469034450633615843 930267703551675950423765)
              ·
                refine ⟨21803149301992405088057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 930267703551675950423765 21803149301992405088057)
                ·
                  rfl

theorem cell22_573230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_573230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573230 prefixEnd_573230 := by exact prefixLift 573230
  have htrace : WordTrace (prefixWord ++ tailWord_573230) baseStart_573230 baseEnd_573230 := by
    simpa [prefixWord, tailWord_573230, baseEnd_573230] using wordTrace_append hprefix tailTrace_573230
  have hstable : (prefixWord ++ tailWord_573230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573230).length < 2 ^ (prefixWord ++ tailWord_573230).sum := by decide
  have hdescent : baseEnd_573230 < baseStart_573230 := by decide
  rcases family_descends (prefixWord ++ tailWord_573230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573316 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_573316 : Nat := 118140960795 + 573316 * 2 ^ 59
def prefixEnd_573316 : Nat := 4983230072969 + 3 ^ 40 * 573316 * 2
def baseEnd_573316 : Nat := 196257783275456088142249

theorem tailTrace_573316 : CollatzResearch.WordTrace tailWord_573316 prefixEnd_573316 196257783275456088142249 := by
  unfold tailWord_573316
  simp only [CollatzResearch.WordTrace]
  refine ⟨10455276195490760711265901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13940368260654347615021201 10455276195490760711265901)
  ·
    refine ⟨3920728573309035266724713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10455276195490760711265901 3920728573309035266724713)
    ·
      refine ⟨2940546429981776450043535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3920728573309035266724713 2940546429981776450043535)
      ·
        refine ⟨4410819644972664675065303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2940546429981776450043535 4410819644972664675065303)
        ·
          refine ⟨6616229467458997012597955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4410819644972664675065303 6616229467458997012597955)
          ·
            refine ⟨9924344201188495518896933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6616229467458997012597955 9924344201188495518896933)
            ·
              refine ⟨1860814537722842909793175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9924344201188495518896933 1860814537722842909793175)
              ·
                refine ⟨2791221806584264364689763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1860814537722842909793175 2791221806584264364689763)
                ·
                  refine ⟨4186832709876396547034645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2791221806584264364689763 4186832709876396547034645)
                  ·
                    refine ⟨196257783275456088142249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4186832709876396547034645 196257783275456088142249)
                    ·
                      rfl

theorem cell22_573316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_573316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573316 prefixEnd_573316 := by exact prefixLift 573316
  have htrace : WordTrace (prefixWord ++ tailWord_573316) baseStart_573316 baseEnd_573316 := by
    simpa [prefixWord, tailWord_573316, baseEnd_573316] using wordTrace_append hprefix tailTrace_573316
  have hstable : (prefixWord ++ tailWord_573316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573316).length < 2 ^ (prefixWord ++ tailWord_573316).sum := by decide
  have hdescent : baseEnd_573316 < baseStart_573316 := by decide
  rcases family_descends (prefixWord ++ tailWord_573316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573391 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 2, 5]
def baseStart_573391 : Nat := 118140960795 + 573391 * 2 ^ 59
def prefixEnd_573391 : Nat := 4983230072969 + 3 ^ 40 * 573391 * 2
def baseEnd_573391 : Nat := 196283457308180892517019

theorem tailTrace_573391 : CollatzResearch.WordTrace tailWord_573391 prefixEnd_573391 196283457308180892517019 := by
  unfold tailWord_573391
  simp only [CollatzResearch.WordTrace]
  refine ⟨20913287865709809231512027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13942191910473206154341351 20913287865709809231512027)
  ·
    refine ⟨31369931798564713847268041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20913287865709809231512027 31369931798564713847268041)
    ·
      refine ⟨23527448848923535385451031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31369931798564713847268041 23527448848923535385451031)
      ·
        refine ⟨35291173273385303078176547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23527448848923535385451031 35291173273385303078176547)
        ·
          refine ⟨52936759910077954617264821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35291173273385303078176547 52936759910077954617264821)
          ·
            refine ⟨4962821241569808245368577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52936759910077954617264821 4962821241569808245368577)
            ·
              refine ⟨3722115931177356184026433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4962821241569808245368577 3722115931177356184026433)
              ·
                refine ⟨2791586948383017138019825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3722115931177356184026433 2791586948383017138019825)
                ·
                  refine ⟨2093690211287262853514869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2791586948383017138019825 2093690211287262853514869)
                  ·
                    refine ⟨196283457308180892517019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2093690211287262853514869 196283457308180892517019)
                    ·
                      rfl

theorem cell22_573391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_573391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573391 prefixEnd_573391 := by exact prefixLift 573391
  have htrace : WordTrace (prefixWord ++ tailWord_573391) baseStart_573391 baseEnd_573391 := by
    simpa [prefixWord, tailWord_573391, baseEnd_573391] using wordTrace_append hprefix tailTrace_573391
  have hstable : (prefixWord ++ tailWord_573391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573391).length < 2 ^ (prefixWord ++ tailWord_573391).sum := by decide
  have hdescent : baseEnd_573391 < baseStart_573391 := by decide
  rcases family_descends (prefixWord ++ tailWord_573391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573397 : List Nat := [1, 3, 2, 3, 2, 2, 1, 4, 1, 3]
def baseStart_573397 : Nat := 118140960795 + 573397 * 2 ^ 59
def prefixEnd_573397 : Nat := 4983230072969 + 3 ^ 40 * 573397 * 2
def baseEnd_573397 : Nat := 196285511230798876867001

theorem tailTrace_573397 : CollatzResearch.WordTrace tailWord_573397 prefixEnd_573397 196285511230798876867001 := by
  unfold tailWord_573397
  simp only [CollatzResearch.WordTrace]
  refine ⟨20913506703688072256230445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13942337802458714837486963 20913506703688072256230445)
  ·
    refine ⟨7842565013883027096086417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20913506703688072256230445 7842565013883027096086417)
    ·
      refine ⟨5881923760412270322064813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7842565013883027096086417 5881923760412270322064813)
      ·
        refine ⟨2205721410154601370774305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5881923760412270322064813 2205721410154601370774305)
        ·
          refine ⟨1654291057615951028080729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2205721410154601370774305 1654291057615951028080729)
          ·
            refine ⟨1240718293211963271060547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1654291057615951028080729 1240718293211963271060547)
            ·
              refine ⟨1861077439817944906590821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1240718293211963271060547 1861077439817944906590821)
              ·
                refine ⟨348952019965864669985779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1861077439817944906590821 348952019965864669985779)
                ·
                  refine ⟨523428029948797004978669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348952019965864669985779 523428029948797004978669)
                  ·
                    refine ⟨196285511230798876867001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 523428029948797004978669 196285511230798876867001)
                    ·
                      rfl

theorem cell22_573397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_573397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573397 prefixEnd_573397 := by exact prefixLift 573397
  have htrace : WordTrace (prefixWord ++ tailWord_573397) baseStart_573397 baseEnd_573397 := by
    simpa [prefixWord, tailWord_573397, baseEnd_573397] using wordTrace_append hprefix tailTrace_573397
  have hstable : (prefixWord ++ tailWord_573397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573397).length < 2 ^ (prefixWord ++ tailWord_573397).sum := by decide
  have hdescent : baseEnd_573397 < baseStart_573397 := by decide
  rcases family_descends (prefixWord ++ tailWord_573397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573423 : List Nat := [1, 1, 2, 1, 4, 2, 2, 4, 1, 4]
def baseStart_573423 : Nat := 118140960795 + 573423 * 2 ^ 59
def prefixEnd_573423 : Nat := 4983230072969 + 3 ^ 40 * 573423 * 2
def baseEnd_573423 : Nat := 196294411562143475716921

theorem tailTrace_573423 : CollatzResearch.WordTrace tailWord_573423 prefixEnd_573423 196294411562143475716921 := by
  unfold tailWord_573423
  simp only [CollatzResearch.WordTrace]
  refine ⟨20914455001593878696676923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13942970001062585797784615 20914455001593878696676923)
  ·
    refine ⟨31371682502390818045015385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20914455001593878696676923 31371682502390818045015385)
    ·
      refine ⟨23528761876793113533761539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31371682502390818045015385 23528761876793113533761539)
      ·
        refine ⟨35293142815189670300642309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23528761876793113533761539 35293142815189670300642309)
        ·
          refine ⟨6617464277848063181370433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35293142815189670300642309 6617464277848063181370433)
          ·
            refine ⟨4963098208386047386027825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6617464277848063181370433 4963098208386047386027825)
            ·
              refine ⟨3722323656289535539520869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4963098208386047386027825 3722323656289535539520869)
              ·
                refine ⟨697935685554287913660163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3722323656289535539520869 697935685554287913660163)
                ·
                  refine ⟨1046903528331431870490245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 697935685554287913660163 1046903528331431870490245)
                  ·
                    refine ⟨196294411562143475716921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1046903528331431870490245 196294411562143475716921)
                    ·
                      rfl

theorem cell22_573423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 4].length) (baseStart_573423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573423 prefixEnd_573423 := by exact prefixLift 573423
  have htrace : WordTrace (prefixWord ++ tailWord_573423) baseStart_573423 baseEnd_573423 := by
    simpa [prefixWord, tailWord_573423, baseEnd_573423] using wordTrace_append hprefix tailTrace_573423
  have hstable : (prefixWord ++ tailWord_573423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573423).length < 2 ^ (prefixWord ++ tailWord_573423).sum := by decide
  have hdescent : baseEnd_573423 < baseStart_573423 := by decide
  rcases family_descends (prefixWord ++ tailWord_573423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573444 : List Nat := [2, 3, 2, 4, 2, 1, 1, 2, 5]
def baseStart_573444 : Nat := 118140960795 + 573444 * 2 ^ 59
def prefixEnd_573444 : Nat := 4983230072969 + 3 ^ 40 * 573444 * 2
def baseEnd_573444 : Nat := 65433866763768806980619

theorem tailTrace_573444 : CollatzResearch.WordTrace tailWord_573444 prefixEnd_573444 65433866763768806980619 := by
  unfold tailWord_573444
  simp only [CollatzResearch.WordTrace]
  refine ⟨10457610467258899641595693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13943480623011866188794257 10457610467258899641595693)
  ·
    refine ⟨3921603925222087365598385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10457610467258899641595693 3921603925222087365598385)
    ·
      refine ⟨2941202943916565524198789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3921603925222087365598385 2941202943916565524198789)
      ·
        refine ⟨551475551984356035787273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2941202943916565524198789 551475551984356035787273)
        ·
          refine ⟨413606663988267026840455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 551475551984356035787273 413606663988267026840455)
          ·
            refine ⟨620409995982400540260683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413606663988267026840455 620409995982400540260683)
            ·
              refine ⟨930614993973600810391025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620409995982400540260683 930614993973600810391025)
              ·
                refine ⟨697961245480200607793269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 930614993973600810391025 697961245480200607793269)
                ·
                  refine ⟨65433866763768806980619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 697961245480200607793269 65433866763768806980619)
                  ·
                    rfl

theorem cell22_573444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_573444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573444 prefixEnd_573444 := by exact prefixLift 573444
  have htrace : WordTrace (prefixWord ++ tailWord_573444) baseStart_573444 baseEnd_573444 := by
    simpa [prefixWord, tailWord_573444, baseEnd_573444] using wordTrace_append hprefix tailTrace_573444
  have hstable : (prefixWord ++ tailWord_573444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573444).length < 2 ^ (prefixWord ++ tailWord_573444).sum := by decide
  have hdescent : baseEnd_573444 < baseStart_573444 := by decide
  rcases family_descends (prefixWord ++ tailWord_573444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573468 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 1, 6]
def baseStart_573468 : Nat := 118140960795 + 573468 * 2 ^ 59
def prefixEnd_573468 : Nat := 4983230072969 + 3 ^ 40 * 573468 * 2
def baseEnd_573468 : Nat := 196309815981778358341783

theorem tailTrace_573468 : CollatzResearch.WordTrace tailWord_573468 prefixEnd_573468 196309815981778358341783 := by
  unfold tailWord_573468
  simp only [CollatzResearch.WordTrace]
  refine ⟨10458048143215425691032529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13944064190953900921376705 10458048143215425691032529)
  ·
    refine ⟨7843536107411569268274397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10458048143215425691032529 7843536107411569268274397)
    ·
      refine ⟨2941326040279338475602899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7843536107411569268274397 2941326040279338475602899)
      ·
        refine ⟨4411989060419007713404349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2941326040279338475602899 4411989060419007713404349)
        ·
          refine ⟨1654495897657127892526631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4411989060419007713404349 1654495897657127892526631)
          ·
            refine ⟨2481743846485691838789947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1654495897657127892526631 2481743846485691838789947)
            ·
              refine ⟨3722615769728537758184921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2481743846485691838789947 3722615769728537758184921)
              ·
                refine ⟨2791961827296403318638691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3722615769728537758184921 2791961827296403318638691)
                ·
                  refine ⟨4187942740944604977958037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2791961827296403318638691 4187942740944604977958037)
                  ·
                    refine ⟨196309815981778358341783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4187942740944604977958037 196309815981778358341783)
                    ·
                      rfl

theorem cell22_573468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_573468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573468 prefixEnd_573468 := by exact prefixLift 573468
  have htrace : WordTrace (prefixWord ++ tailWord_573468) baseStart_573468 baseEnd_573468 := by
    simpa [prefixWord, tailWord_573468, baseEnd_573468] using wordTrace_append hprefix tailTrace_573468
  have hstable : (prefixWord ++ tailWord_573468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573468).length < 2 ^ (prefixWord ++ tailWord_573468).sum := by decide
  have hdescent : baseEnd_573468 < baseStart_573468 := by decide
  rcases family_descends (prefixWord ++ tailWord_573468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573502 : List Nat := [4, 2, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_573502 : Nat := 118140960795 + 573502 * 2 ^ 59
def prefixEnd_573502 : Nat := 4983230072969 + 3 ^ 40 * 573502 * 2
def baseEnd_573502 : Nat := 196321454876613602991679

theorem tailTrace_573502 : CollatzResearch.WordTrace tailWord_573502 prefixEnd_573502 196321454876613602991679 := by
  unfold tailWord_573502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2614667046038459398600345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13944890912205116792535173 2614667046038459398600345)
  ·
    refine ⟨1961000284528844548950259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2614667046038459398600345 1961000284528844548950259)
    ·
      refine ⟨2941500426793266823425389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1961000284528844548950259 2941500426793266823425389)
      ·
        refine ⟨1103062660047475058784521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2941500426793266823425389 1103062660047475058784521)
        ·
          refine ⟨827296995035606294088391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1103062660047475058784521 827296995035606294088391)
          ·
            refine ⟨1240945492553409441132587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827296995035606294088391 1240945492553409441132587)
            ·
              refine ⟨1861418238830114161698881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1240945492553409441132587 1861418238830114161698881)
              ·
                refine ⟨1396063679122585621274161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1861418238830114161698881 1396063679122585621274161)
                ·
                  refine ⟨1047047759341939215955621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1396063679122585621274161 1047047759341939215955621)
                  ·
                    refine ⟨196321454876613602991679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1047047759341939215955621 196321454876613602991679)
                    ·
                      rfl

theorem cell22_573502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_573502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573502 prefixEnd_573502 := by exact prefixLift 573502
  have htrace : WordTrace (prefixWord ++ tailWord_573502) baseStart_573502 baseEnd_573502 := by
    simpa [prefixWord, tailWord_573502, baseEnd_573502] using wordTrace_append hprefix tailTrace_573502
  have hstable : (prefixWord ++ tailWord_573502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573502).length < 2 ^ (prefixWord ++ tailWord_573502).sum := by decide
  have hdescent : baseEnd_573502 < baseStart_573502 := by decide
  rcases family_descends (prefixWord ++ tailWord_573502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573605 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 4, 3]
def baseStart_573605 : Nat := 118140960795 + 573605 * 2 ^ 59
def prefixEnd_573605 : Nat := 4983230072969 + 3 ^ 40 * 573605 * 2
def baseEnd_573605 : Nat := 196356713881555667666363

theorem tailTrace_573605 : CollatzResearch.WordTrace tailWord_573605 prefixEnd_573605 196356713881555667666363 := by
  unfold tailWord_573605
  simp only [CollatzResearch.WordTrace]
  refine ⟨20921093086934523779802269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13947395391289682519868179 20921093086934523779802269)
  ·
    refine ⟨7845409907600446417425851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20921093086934523779802269 7845409907600446417425851)
    ·
      refine ⟨11768114861400669626138777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7845409907600446417425851 11768114861400669626138777)
      ·
        refine ⟨8826086146050502219604083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11768114861400669626138777 8826086146050502219604083)
        ·
          refine ⟨13239129219075753329406125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8826086146050502219604083 13239129219075753329406125)
          ·
            refine ⟨4964673457153407498527297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13239129219075753329406125 4964673457153407498527297)
            ·
              refine ⟨3723505092865055623895473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4964673457153407498527297 3723505092865055623895473)
              ·
                refine ⟨2792628819648791717921605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3723505092865055623895473 2792628819648791717921605)
                ·
                  refine ⟨523617903684148447110301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2792628819648791717921605 523617903684148447110301)
                  ·
                    refine ⟨196356713881555667666363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 523617903684148447110301 196356713881555667666363)
                    ·
                      rfl

theorem cell22_573605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_573605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573605 prefixEnd_573605 := by exact prefixLift 573605
  have htrace : WordTrace (prefixWord ++ tailWord_573605) baseStart_573605 baseEnd_573605 := by
    simpa [prefixWord, tailWord_573605, baseEnd_573605] using wordTrace_append hprefix tailTrace_573605
  have hstable : (prefixWord ++ tailWord_573605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573605).length < 2 ^ (prefixWord ++ tailWord_573605).sum := by decide
  have hdescent : baseEnd_573605 < baseStart_573605 := by decide
  rcases family_descends (prefixWord ++ tailWord_573605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573618 : List Nat := [3, 2, 1, 1, 1, 3, 11]
def baseStart_573618 : Nat := 118140960795 + 573618 * 2 ^ 59
def prefixEnd_573618 : Nat := 4983230072969 + 3 ^ 40 * 573618 * 2
def baseEnd_573618 : Nat := 7272635705452887670049

theorem tailTrace_573618 : CollatzResearch.WordTrace tailWord_573618 prefixEnd_573618 7272635705452887670049 := by
  unfold tailWord_573618
  simp only [CollatzResearch.WordTrace]
  refine ⟨5230391808971856750006377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13947711490591618000017005 5230391808971856750006377)
  ·
    refine ⟨3922793856728892562504783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5230391808971856750006377 3922793856728892562504783)
    ·
      refine ⟨5884190785093338843757175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3922793856728892562504783 5884190785093338843757175)
      ·
        refine ⟨8826286177640008265635763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5884190785093338843757175 8826286177640008265635763)
        ·
          refine ⟨13239429266460012398453645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8826286177640008265635763 13239429266460012398453645)
          ·
            refine ⟨4964785974922504649420117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13239429266460012398453645 4964785974922504649420117)
            ·
              refine ⟨7272635705452887670049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4964785974922504649420117 7272635705452887670049)
              ·
                rfl

theorem cell22_573618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 11].length) (baseStart_573618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573618 prefixEnd_573618 := by exact prefixLift 573618
  have htrace : WordTrace (prefixWord ++ tailWord_573618) baseStart_573618 baseEnd_573618 := by
    simpa [prefixWord, tailWord_573618, baseEnd_573618] using wordTrace_append hprefix tailTrace_573618
  have hstable : (prefixWord ++ tailWord_573618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573618).length < 2 ^ (prefixWord ++ tailWord_573618).sum := by decide
  have hdescent : baseEnd_573618 < baseStart_573618 := by decide
  rcases family_descends (prefixWord ++ tailWord_573618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573735 : List Nat := [1, 1, 8, 1, 1, 1, 1, 4, 1, 3]
def baseStart_573735 : Nat := 118140960795 + 573735 * 2 ^ 59
def prefixEnd_573735 : Nat := 4983230072969 + 3 ^ 40 * 573735 * 2
def baseEnd_573735 : Nat := 196401215538278661915965

theorem tailTrace_573735 : CollatzResearch.WordTrace tailWord_573735 prefixEnd_573735 196401215538278661915965 := by
  unfold tailWord_573735
  simp only [CollatzResearch.WordTrace]
  refine ⟨20925834576463555982034659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13950556384309037321356439 20925834576463555982034659)
  ·
    refine ⟨31388751864695333973051989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20925834576463555982034659 31388751864695333973051989)
    ·
      refine ⟨367836935914398444996703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 31388751864695333973051989 367836935914398444996703)
      ·
        refine ⟨551755403871597667495055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367836935914398444996703 551755403871597667495055)
        ·
          refine ⟨827633105807396501242583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551755403871597667495055 827633105807396501242583)
          ·
            refine ⟨1241449658711094751863875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827633105807396501242583 1241449658711094751863875)
            ·
              refine ⟨1862174488066642127795813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1241449658711094751863875 1862174488066642127795813)
              ·
                refine ⟨349157716512495398961715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1862174488066642127795813 349157716512495398961715)
                ·
                  refine ⟨523736574768743098442573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349157716512495398961715 523736574768743098442573)
                  ·
                    refine ⟨196401215538278661915965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 523736574768743098442573 196401215538278661915965)
                    ·
                      rfl

theorem cell22_573735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_573735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573735 prefixEnd_573735 := by exact prefixLift 573735
  have htrace : WordTrace (prefixWord ++ tailWord_573735) baseStart_573735 baseEnd_573735 := by
    simpa [prefixWord, tailWord_573735, baseEnd_573735] using wordTrace_append hprefix tailTrace_573735
  have hstable : (prefixWord ++ tailWord_573735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573735).length < 2 ^ (prefixWord ++ tailWord_573735).sum := by decide
  have hdescent : baseEnd_573735 < baseStart_573735 := by decide
  rcases family_descends (prefixWord ++ tailWord_573735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573836 : List Nat := [2, 2, 1, 2, 1, 4, 3, 3, 1, 3]
def baseStart_573836 : Nat := 118140960795 + 573836 * 2 ^ 59
def prefixEnd_573836 : Nat := 4983230072969 + 3 ^ 40 * 573836 * 2
def baseEnd_573836 : Nat := 196435789902348065140655

theorem tailTrace_573836 : CollatzResearch.WordTrace tailWord_573836 prefixEnd_573836 196435789902348065140655 := by
  unfold tailWord_573836
  simp only [CollatzResearch.WordTrace]
  refine ⟨10464759174548825115730681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13953012232731766820974241 10464759174548825115730681)
  ·
    refine ⟨7848569380911618836798011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10464759174548825115730681 7848569380911618836798011)
    ·
      refine ⟨11772854071367428255197017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7848569380911618836798011 11772854071367428255197017)
      ·
        refine ⟨8829640553525571191397763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11772854071367428255197017 8829640553525571191397763)
        ·
          refine ⟨13244460830288356787096645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8829640553525571191397763 13244460830288356787096645)
          ·
            refine ⟨2483336405679066897580621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13244460830288356787096645 2483336405679066897580621)
            ·
              refine ⟨931251152129650086592733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2483336405679066897580621 931251152129650086592733)
              ·
                refine ⟨349219182048618782472275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 931251152129650086592733 349219182048618782472275)
                ·
                  refine ⟨523828773072928173708413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349219182048618782472275 523828773072928173708413)
                  ·
                    refine ⟨196435789902348065140655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 523828773072928173708413 196435789902348065140655)
                    ·
                      rfl

theorem cell22_573836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 1, 3].length) (baseStart_573836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573836 prefixEnd_573836 := by exact prefixLift 573836
  have htrace : WordTrace (prefixWord ++ tailWord_573836) baseStart_573836 baseEnd_573836 := by
    simpa [prefixWord, tailWord_573836, baseEnd_573836] using wordTrace_append hprefix tailTrace_573836
  have hstable : (prefixWord ++ tailWord_573836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573836).length < 2 ^ (prefixWord ++ tailWord_573836).sum := by decide
  have hdescent : baseEnd_573836 < baseStart_573836 := by decide
  rcases family_descends (prefixWord ++ tailWord_573836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573853 : List Nat := [1, 4, 2, 1, 5, 1, 1, 1, 3, 3]
def baseStart_573853 : Nat := 118140960795 + 573853 * 2 ^ 59
def prefixEnd_573853 : Nat := 4983230072969 + 3 ^ 40 * 573853 * 2
def baseEnd_573853 : Nat := 196441609349765687465603

theorem tailTrace_573853 : CollatzResearch.WordTrace tailWord_573853 prefixEnd_573853 196441609349765687465603 := by
  unfold tailWord_573853
  simp only [CollatzResearch.WordTrace]
  refine ⟨20930138390036062134830213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13953425593357374756553475 20930138390036062134830213)
  ·
    refine ⟨3924400948131761650280665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20930138390036062134830213 3924400948131761650280665)
    ·
      refine ⟨2943300711098821237710499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3924400948131761650280665 2943300711098821237710499)
      ·
        refine ⟨4414951066648231856565749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2943300711098821237710499 4414951066648231856565749)
        ·
          refine ⟨413901662498271736553039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4414951066648231856565749 413901662498271736553039)
          ·
            refine ⟨620852493747407604829559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413901662498271736553039 620852493747407604829559)
            ·
              refine ⟨931278740621111407244339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620852493747407604829559 931278740621111407244339)
              ·
                refine ⟨1396918110931667110866509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931278740621111407244339 1396918110931667110866509)
                ·
                  refine ⟨523844291599375166574941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1396918110931667110866509 523844291599375166574941)
                  ·
                    refine ⟨196441609349765687465603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 523844291599375166574941 196441609349765687465603)
                    ·
                      rfl

theorem cell22_573853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_573853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573853 prefixEnd_573853 := by exact prefixLift 573853
  have htrace : WordTrace (prefixWord ++ tailWord_573853) baseStart_573853 baseEnd_573853 := by
    simpa [prefixWord, tailWord_573853, baseEnd_573853] using wordTrace_append hprefix tailTrace_573853
  have hstable : (prefixWord ++ tailWord_573853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573853).length < 2 ^ (prefixWord ++ tailWord_573853).sum := by decide
  have hdescent : baseEnd_573853 < baseStart_573853 := by decide
  rcases family_descends (prefixWord ++ tailWord_573853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573879 : List Nat := [1, 1, 3, 1, 3, 3, 3, 2, 1, 4]
def baseStart_573879 : Nat := 118140960795 + 573879 * 2 ^ 59
def prefixEnd_573879 : Nat := 4983230072969 + 3 ^ 40 * 573879 * 2
def baseEnd_573879 : Nat := 196450509681110286315523

theorem tailTrace_573879 : CollatzResearch.WordTrace tailWord_573879 prefixEnd_573879 196450509681110286315523 := by
  unfold tailWord_573879
  simp only [CollatzResearch.WordTrace]
  refine ⟨20931086687941868575276691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13954057791961245716851127 20931086687941868575276691)
  ·
    refine ⟨31396630031912802862915037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20931086687941868575276691 31396630031912802862915037)
    ·
      refine ⟨11773736261967301073593139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31396630031912802862915037 11773736261967301073593139)
      ·
        refine ⟨17660604392950951610389709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11773736261967301073593139 17660604392950951610389709)
        ·
          refine ⟨6622726647356606853896141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17660604392950951610389709 6622726647356606853896141)
          ·
            refine ⟨2483522492758727570211053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6622726647356606853896141 2483522492758727570211053)
            ·
              refine ⟨931320934784522838829145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2483522492758727570211053 931320934784522838829145)
              ·
                refine ⟨698490701088392129121859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 931320934784522838829145 698490701088392129121859)
                ·
                  refine ⟨1047736051632588193682789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698490701088392129121859 1047736051632588193682789)
                  ·
                    refine ⟨196450509681110286315523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1047736051632588193682789 196450509681110286315523)
                    ·
                      rfl

theorem cell22_573879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_573879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573879 prefixEnd_573879 := by exact prefixLift 573879
  have htrace : WordTrace (prefixWord ++ tailWord_573879) baseStart_573879 baseEnd_573879 := by
    simpa [prefixWord, tailWord_573879, baseEnd_573879] using wordTrace_append hprefix tailTrace_573879
  have hstable : (prefixWord ++ tailWord_573879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573879).length < 2 ^ (prefixWord ++ tailWord_573879).sum := by decide
  have hdescent : baseEnd_573879 < baseStart_573879 := by decide
  rcases family_descends (prefixWord ++ tailWord_573879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573896 : List Nat := [2, 1, 3, 1, 3, 3, 3, 1, 1, 4]
def baseStart_573896 : Nat := 118140960795 + 573896 * 2 ^ 59
def prefixEnd_573896 : Nat := 4983230072969 + 3 ^ 40 * 573896 * 2
def baseEnd_573896 : Nat := 196456329128527908640471

theorem tailTrace_573896 : CollatzResearch.WordTrace tailWord_573896 prefixEnd_573896 196456329128527908640471 := by
  unfold tailWord_573896
  simp only [CollatzResearch.WordTrace]
  refine ⟨10465853364440140239322771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13954471152586853652430361 10465853364440140239322771)
  ·
    refine ⟨15698780046660210358984157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10465853364440140239322771 15698780046660210358984157)
    ·
      refine ⟨5887042517497578884619059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15698780046660210358984157 5887042517497578884619059)
      ·
        refine ⟨8830563776246368326928589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5887042517497578884619059 8830563776246368326928589)
        ·
          refine ⟨3311461416092388122598221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8830563776246368326928589 3311461416092388122598221)
          ·
            refine ⟨1241798031034645545974333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3311461416092388122598221 1241798031034645545974333)
            ·
              refine ⟨465674261637992079740375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1241798031034645545974333 465674261637992079740375)
              ·
                refine ⟨698511392456988119610563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465674261637992079740375 698511392456988119610563)
                ·
                  refine ⟨1047767088685482179415845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698511392456988119610563 1047767088685482179415845)
                  ·
                    refine ⟨196456329128527908640471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1047767088685482179415845 196456329128527908640471)
                    ·
                      rfl

theorem cell22_573896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_573896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573896 prefixEnd_573896 := by exact prefixLift 573896
  have htrace : WordTrace (prefixWord ++ tailWord_573896) baseStart_573896 baseEnd_573896 := by
    simpa [prefixWord, tailWord_573896, baseEnd_573896] using wordTrace_append hprefix tailTrace_573896
  have hstable : (prefixWord ++ tailWord_573896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573896).length < 2 ^ (prefixWord ++ tailWord_573896).sum := by decide
  have hdescent : baseEnd_573896 < baseStart_573896 := by decide
  rcases family_descends (prefixWord ++ tailWord_573896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573941 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 1, 6]
def baseStart_573941 : Nat := 118140960795 + 573941 * 2 ^ 59
def prefixEnd_573941 : Nat := 4983230072969 + 3 ^ 40 * 573941 * 2
def baseEnd_573941 : Nat := 196471733548162791265333

theorem tailTrace_573941 : CollatzResearch.WordTrace tailWord_573941 prefixEnd_573941 196471733548162791265333 := by
  unfold tailWord_573941
  simp only [CollatzResearch.WordTrace]
  refine ⟨20933348013717253164033677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13955565342478168776022451 20933348013717253164033677)
  ·
    refine ⟨7850005505143969936512629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20933348013717253164033677 7850005505143969936512629)
    ·
      refine ⟨735938016107247181548059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7850005505143969936512629 735938016107247181548059)
      ·
        refine ⟨1103907024160870772322089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 735938016107247181548059 1103907024160870772322089)
        ·
          refine ⟨827930268120653079241567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1103907024160870772322089 827930268120653079241567)
          ·
            refine ⟨1241895402180979618862351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827930268120653079241567 1241895402180979618862351)
            ·
              refine ⟨1862843103271469428293527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1241895402180979618862351 1862843103271469428293527)
              ·
                refine ⟨2794264654907204142440291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1862843103271469428293527 2794264654907204142440291)
                ·
                  refine ⟨4191396982360806213660437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2794264654907204142440291 4191396982360806213660437)
                  ·
                    refine ⟨196471733548162791265333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4191396982360806213660437 196471733548162791265333)
                    ·
                      rfl

theorem cell22_573941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_573941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573941 prefixEnd_573941 := by exact prefixLift 573941
  have htrace : WordTrace (prefixWord ++ tailWord_573941) baseStart_573941 baseEnd_573941 := by
    simpa [prefixWord, tailWord_573941, baseEnd_573941] using wordTrace_append hprefix tailTrace_573941
  have hstable : (prefixWord ++ tailWord_573941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573941).length < 2 ^ (prefixWord ++ tailWord_573941).sum := by decide
  have hdescent : baseEnd_573941 < baseStart_573941 := by decide
  rcases family_descends (prefixWord ++ tailWord_573941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573971 : List Nat := [1, 1, 1, 2, 1, 5, 1, 6, 1, 3]
def baseStart_573971 : Nat := 118140960795 + 573971 * 2 ^ 59
def prefixEnd_573971 : Nat := 4983230072969 + 3 ^ 40 * 573971 * 2
def baseEnd_573971 : Nat := 196482003161252713015241

theorem tailTrace_573971 : CollatzResearch.WordTrace tailWord_573971 prefixEnd_573971 196482003161252713015241 := by
  unfold tailWord_573971
  simp only [CollatzResearch.WordTrace]
  refine ⟨20934442203608568287625767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13956294802405712191750511 20934442203608568287625767)
  ·
    refine ⟨31401663305412852431438651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20934442203608568287625767 31401663305412852431438651)
    ·
      refine ⟨47102494958119278647157977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31401663305412852431438651 47102494958119278647157977)
      ·
        refine ⟨35326871218589458985368483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47102494958119278647157977 35326871218589458985368483)
        ·
          refine ⟨52990306827884188478052725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35326871218589458985368483 52990306827884188478052725)
          ·
            refine ⟨4967841265114142669817443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52990306827884188478052725 4967841265114142669817443)
            ·
              refine ⟨7451761897671214004726165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4967841265114142669817443 7451761897671214004726165)
              ·
                refine ⟨349301338953338156471539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7451761897671214004726165 349301338953338156471539)
                ·
                  refine ⟨523952008430007234707309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349301338953338156471539 523952008430007234707309)
                  ·
                    refine ⟨196482003161252713015241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 523952008430007234707309 196482003161252713015241)
                    ·
                      rfl

theorem cell22_573971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 1, 3].length) (baseStart_573971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_573971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_573971 prefixEnd_573971 := by exact prefixLift 573971
  have htrace : WordTrace (prefixWord ++ tailWord_573971) baseStart_573971 baseEnd_573971 := by
    simpa [prefixWord, tailWord_573971, baseEnd_573971] using wordTrace_append hprefix tailTrace_573971
  have hstable : (prefixWord ++ tailWord_573971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573971).length < 2 ^ (prefixWord ++ tailWord_573971).sum := by decide
  have hdescent : baseEnd_573971 < baseStart_573971 := by decide
  rcases family_descends (prefixWord ++ tailWord_573971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574061 : List Nat := [1, 5, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_574061 : Nat := 118140960795 + 574061 * 2 ^ 59
def prefixEnd_574061 : Nat := 4983230072969 + 3 ^ 40 * 574061 * 2
def baseEnd_574061 : Nat := 196512812000522478264965

theorem tailTrace_574061 : CollatzResearch.WordTrace tailWord_574061 prefixEnd_574061 196512812000522478264965 := by
  unfold tailWord_574061
  simp only [CollatzResearch.WordTrace]
  refine ⟨20937724773282513658402037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13958483182188342438934691 20937724773282513658402037)
  ·
    refine ⟨1962911697495235655475191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20937724773282513658402037 1962911697495235655475191)
    ·
      refine ⟨2944367546242853483212787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1962911697495235655475191 2944367546242853483212787)
      ·
        refine ⟨4416551319364280224819181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2944367546242853483212787 4416551319364280224819181)
        ·
          refine ⟨1656206744761605084307193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4416551319364280224819181 1656206744761605084307193)
          ·
            refine ⟨1242155058571203813230395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1656206744761605084307193 1242155058571203813230395)
            ·
              refine ⟨1863232587856805719845593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242155058571203813230395 1863232587856805719845593)
              ·
                refine ⟨1397424440892604289884195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1863232587856805719845593 1397424440892604289884195)
                ·
                  refine ⟨2096136661338906434826293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1397424440892604289884195 2096136661338906434826293)
                  ·
                    refine ⟨196512812000522478264965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2096136661338906434826293 196512812000522478264965)
                    ·
                      rfl

theorem cell22_574061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_574061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574061 prefixEnd_574061 := by exact prefixLift 574061
  have htrace : WordTrace (prefixWord ++ tailWord_574061) baseStart_574061 baseEnd_574061 := by
    simpa [prefixWord, tailWord_574061, baseEnd_574061] using wordTrace_append hprefix tailTrace_574061
  have hstable : (prefixWord ++ tailWord_574061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574061).length < 2 ^ (prefixWord ++ tailWord_574061).sum := by decide
  have hdescent : baseEnd_574061 < baseStart_574061 := by decide
  rcases family_descends (prefixWord ++ tailWord_574061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574104 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 2, 6]
def baseStart_574104 : Nat := 118140960795 + 574104 * 2 ^ 59
def prefixEnd_574104 : Nat := 4983230072969 + 3 ^ 40 * 574104 * 2
def baseEnd_574104 : Nat := 196527531779284699439833

theorem tailTrace_574104 : CollatzResearch.WordTrace tailWord_574104 prefixEnd_574104 196527531779284699439833 := by
  unfold tailWord_574104
  simp only [CollatzResearch.WordTrace]
  refine ⟨10469646556063366001108683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13959528741417821334811577 10469646556063366001108683)
  ·
    refine ⟨15704469834095049001663025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10469646556063366001108683 15704469834095049001663025)
    ·
      refine ⟨11778352375571286751247269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15704469834095049001663025 11778352375571286751247269)
      ·
        refine ⟨2208441070419616265858863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11778352375571286751247269 2208441070419616265858863)
        ·
          refine ⟨3312661605629424398788295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2208441070419616265858863 3312661605629424398788295)
          ·
            refine ⟨4968992408444136598182443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3312661605629424398788295 4968992408444136598182443)
            ·
              refine ⟨7453488612666204897273665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4968992408444136598182443 7453488612666204897273665)
              ·
                refine ⟨5590116459499653672955249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7453488612666204897273665 5590116459499653672955249)
                ·
                  refine ⟨4192587344624740254716437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5590116459499653672955249 4192587344624740254716437)
                  ·
                    refine ⟨196527531779284699439833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4192587344624740254716437 196527531779284699439833)
                    ·
                      rfl

theorem cell22_574104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_574104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574104 prefixEnd_574104 := by exact prefixLift 574104
  have htrace : WordTrace (prefixWord ++ tailWord_574104) baseStart_574104 baseEnd_574104 := by
    simpa [prefixWord, tailWord_574104, baseEnd_574104] using wordTrace_append hprefix tailTrace_574104
  have hstable : (prefixWord ++ tailWord_574104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574104).length < 2 ^ (prefixWord ++ tailWord_574104).sum := by decide
  have hdescent : baseEnd_574104 < baseStart_574104 := by decide
  rcases family_descends (prefixWord ++ tailWord_574104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574258 : List Nat := [3, 2, 1, 1, 3, 1, 2, 3, 3, 3]
def baseStart_574258 : Nat := 118140960795 + 574258 * 2 ^ 59
def prefixEnd_574258 : Nat := 4983230072969 + 3 ^ 40 * 574258 * 2
def baseEnd_574258 : Nat := 196580249126479631089361

theorem tailTrace_574258 : CollatzResearch.WordTrace tailWord_574258 prefixEnd_574258 196580249126479631089361 := by
  unfold tailWord_574258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5236227488392204075830857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13963273302379210868882285 5236227488392204075830857)
  ·
    refine ⟨3927170616294153056873143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5236227488392204075830857 3927170616294153056873143)
    ·
      refine ⟨5890755924441229585309715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3927170616294153056873143 5890755924441229585309715)
      ·
        refine ⟨8836133886661844377964573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5890755924441229585309715 8836133886661844377964573)
        ·
          refine ⟨3313550207498191641736715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8836133886661844377964573 3313550207498191641736715)
          ·
            refine ⟨4970325311247287462605073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3313550207498191641736715 4970325311247287462605073)
            ·
              refine ⟨3727743983435465596953805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4970325311247287462605073 3727743983435465596953805)
              ·
                refine ⟨1397903993788299598857677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3727743983435465596953805 1397903993788299598857677)
                ·
                  refine ⟨524213997670612349571629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1397903993788299598857677 524213997670612349571629)
                  ·
                    refine ⟨196580249126479631089361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 524213997670612349571629 196580249126479631089361)
                    ·
                      rfl

theorem cell22_574258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_574258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574258 prefixEnd_574258 := by exact prefixLift 574258
  have htrace : WordTrace (prefixWord ++ tailWord_574258) baseStart_574258 baseEnd_574258 := by
    simpa [prefixWord, tailWord_574258, baseEnd_574258] using wordTrace_append hprefix tailTrace_574258
  have hstable : (prefixWord ++ tailWord_574258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574258).length < 2 ^ (prefixWord ++ tailWord_574258).sum := by decide
  have hdescent : baseEnd_574258 < baseStart_574258 := by decide
  rcases family_descends (prefixWord ++ tailWord_574258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574260 : List Nat := [2, 5, 1, 1, 3, 2, 1, 7]
def baseStart_574260 : Nat := 118140960795 + 574260 * 2 ^ 59
def prefixEnd_574260 : Nat := 4983230072969 + 3 ^ 40 * 574260 * 2
def baseEnd_574260 : Nat := 21842325974150254726595

theorem tailTrace_574260 : CollatzResearch.WordTrace tailWord_574260 prefixEnd_574260 21842325974150254726595 := by
  unfold tailWord_574260
  simp only [CollatzResearch.WordTrace]
  refine ⟨10472491449780785322448117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13963321933041047096597489 10472491449780785322448117)
  ·
    refine ⟨981796073416948623979511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10472491449780785322448117 981796073416948623979511)
    ·
      refine ⟨1472694110125422935969267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 981796073416948623979511 1472694110125422935969267)
      ·
        refine ⟨2209041165188134403953901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1472694110125422935969267 2209041165188134403953901)
        ·
          refine ⟨828390436945550401482713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2209041165188134403953901 828390436945550401482713)
          ·
            refine ⟨621292827709162801112035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 828390436945550401482713 621292827709162801112035)
            ·
              refine ⟨931939241563744201668053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621292827709162801112035 931939241563744201668053)
              ·
                refine ⟨21842325974150254726595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 931939241563744201668053 21842325974150254726595)
                ·
                  rfl

theorem cell22_574260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 7].length) (baseStart_574260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574260 prefixEnd_574260 := by exact prefixLift 574260
  have htrace : WordTrace (prefixWord ++ tailWord_574260) baseStart_574260 baseEnd_574260 := by
    simpa [prefixWord, tailWord_574260, baseEnd_574260] using wordTrace_append hprefix tailTrace_574260
  have hstable : (prefixWord ++ tailWord_574260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574260).length < 2 ^ (prefixWord ++ tailWord_574260).sum := by decide
  have hdescent : baseEnd_574260 < baseStart_574260 := by decide
  rcases family_descends (prefixWord ++ tailWord_574260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574348 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 4, 3]
def baseStart_574348 : Nat := 118140960795 + 574348 * 2 ^ 59
def prefixEnd_574348 : Nat := 4983230072969 + 3 ^ 40 * 574348 * 2
def baseEnd_574348 : Nat := 196611057965749396339085

theorem tailTrace_574348 : CollatzResearch.WordTrace tailWord_574348 prefixEnd_574348 196611057965749396339085 := by
  unfold tailWord_574348
  simp only [CollatzResearch.WordTrace]
  refine ⟨10474096261621380837049849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13965461682161841116066465 10474096261621380837049849)
  ·
    refine ⟨7855572196216035627787387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10474096261621380837049849 7855572196216035627787387)
    ·
      refine ⟨11783358294324053441681081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7855572196216035627787387 11783358294324053441681081)
      ·
        refine ⟨8837518720743040081260811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11783358294324053441681081 8837518720743040081260811)
        ·
          refine ⟨13256278081114560121891217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8837518720743040081260811 13256278081114560121891217)
          ·
            refine ⟨9942208560835920091418413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13256278081114560121891217 9942208560835920091418413)
            ·
              refine ⟨3728328210313470034281905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9942208560835920091418413 3728328210313470034281905)
              ·
                refine ⟨2796246157735102525711429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3728328210313470034281905 2796246157735102525711429)
                ·
                  refine ⟨524296154575331723570893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2796246157735102525711429 524296154575331723570893)
                  ·
                    refine ⟨196611057965749396339085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 524296154575331723570893 196611057965749396339085)
                    ·
                      rfl

theorem cell22_574348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_574348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574348 prefixEnd_574348 := by exact prefixLift 574348
  have htrace : WordTrace (prefixWord ++ tailWord_574348) baseStart_574348 baseEnd_574348 := by
    simpa [prefixWord, tailWord_574348, baseEnd_574348] using wordTrace_append hprefix tailTrace_574348
  have hstable : (prefixWord ++ tailWord_574348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574348).length < 2 ^ (prefixWord ++ tailWord_574348).sum := by decide
  have hdescent : baseEnd_574348 < baseStart_574348 := by decide
  rcases family_descends (prefixWord ++ tailWord_574348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574365 : List Nat := [1, 4, 2, 1, 2, 1, 2, 4, 2, 3]
def baseStart_574365 : Nat := 118140960795 + 574365 * 2 ^ 59
def prefixEnd_574365 : Nat := 4983230072969 + 3 ^ 40 * 574365 * 2
def baseEnd_574365 : Nat := 196616877413167018664033

theorem tailTrace_574365 : CollatzResearch.WordTrace tailWord_574365 prefixEnd_574365 196616877413167018664033 := by
  unfold tailWord_574365
  simp only [CollatzResearch.WordTrace]
  refine ⟨20948812564181173577468549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13965875042787449051645699 20948812564181173577468549)
  ·
    refine ⟨3927902355783970045775353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20948812564181173577468549 3927902355783970045775353)
    ·
      refine ⟨2945926766837977534331515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3927902355783970045775353 2945926766837977534331515)
      ·
        refine ⟨4418890150256966301497273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2945926766837977534331515 4418890150256966301497273)
        ·
          refine ⟨3314167612692724726122955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4418890150256966301497273 3314167612692724726122955)
          ·
            refine ⟨4971251419039087089184433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3314167612692724726122955 4971251419039087089184433)
            ·
              refine ⟨3728438564279315316888325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4971251419039087089184433 3728438564279315316888325)
              ·
                refine ⟨699082230802371621916561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3728438564279315316888325 699082230802371621916561)
                ·
                  refine ⟨524311673101778716437421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 699082230802371621916561 524311673101778716437421)
                  ·
                    refine ⟨196616877413167018664033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 524311673101778716437421 196616877413167018664033)
                    ·
                      rfl

theorem cell22_574365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_574365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574365 prefixEnd_574365 := by exact prefixLift 574365
  have htrace : WordTrace (prefixWord ++ tailWord_574365) baseStart_574365 baseEnd_574365 := by
    simpa [prefixWord, tailWord_574365, baseEnd_574365] using wordTrace_append hprefix tailTrace_574365
  have hstable : (prefixWord ++ tailWord_574365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574365).length < 2 ^ (prefixWord ++ tailWord_574365).sum := by decide
  have hdescent : baseEnd_574365 < baseStart_574365 := by decide
  rcases family_descends (prefixWord ++ tailWord_574365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574367 : List Nat := [1, 1, 2, 5, 2, 2, 3, 2, 4]
def baseStart_574367 : Nat := 118140960795 + 574367 * 2 ^ 59
def prefixEnd_574367 : Nat := 4983230072969 + 3 ^ 40 * 574367 * 2
def baseEnd_574367 : Nat := 65539187351346560038009

theorem tailTrace_574367 : CollatzResearch.WordTrace tailWord_574367 prefixEnd_574367 65539187351346560038009 := by
  unfold tailWord_574367
  simp only [CollatzResearch.WordTrace]
  refine ⟨20948885510173927919041355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13965923673449285279360903 20948885510173927919041355)
  ·
    refine ⟨31423328265260891878562033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20948885510173927919041355 31423328265260891878562033)
    ·
      refine ⟨23567496198945668908921525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31423328265260891878562033 23567496198945668908921525)
      ·
        refine ⟨2209452768651156460211393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23567496198945668908921525 2209452768651156460211393)
        ·
          refine ⟨1657089576488367345158545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2209452768651156460211393 1657089576488367345158545)
          ·
            refine ⟨1242817182366275508868909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1657089576488367345158545 1242817182366275508868909)
            ·
              refine ⟨466056443387353315825841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1242817182366275508868909 466056443387353315825841)
              ·
                refine ⟨349542332540514986869381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466056443387353315825841 349542332540514986869381)
                ·
                  refine ⟨65539187351346560038009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 349542332540514986869381 65539187351346560038009)
                  ·
                    rfl

theorem cell22_574367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 4].length) (baseStart_574367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574367 prefixEnd_574367 := by exact prefixLift 574367
  have htrace : WordTrace (prefixWord ++ tailWord_574367) baseStart_574367 baseEnd_574367 := by
    simpa [prefixWord, tailWord_574367, baseEnd_574367] using wordTrace_append hprefix tailTrace_574367
  have hstable : (prefixWord ++ tailWord_574367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574367).length < 2 ^ (prefixWord ++ tailWord_574367).sum := by decide
  have hdescent : baseEnd_574367 < baseStart_574367 := by decide
  rcases family_descends (prefixWord ++ tailWord_574367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574485 : List Nat := [1, 3, 2, 1, 4, 2, 2, 1, 6]
def baseStart_574485 : Nat := 118140960795 + 574485 * 2 ^ 59
def prefixEnd_574485 : Nat := 4983230072969 + 3 ^ 40 * 574485 * 2
def baseEnd_574485 : Nat := 65552651955175568554555

theorem tailTrace_574485 : CollatzResearch.WordTrace tailWord_574485 prefixEnd_574485 65552651955175568554555 := by
  unfold tailWord_574485
  simp only [CollatzResearch.WordTrace]
  refine ⟨20953189323746434071836909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13968792882497622714557939 20953189323746434071836909)
  ·
    refine ⟨7857445996404912776938841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20953189323746434071836909 7857445996404912776938841)
    ·
      refine ⟨5893084497303684582704131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7857445996404912776938841 5893084497303684582704131)
      ·
        refine ⟨8839626745955526874056197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5893084497303684582704131 8839626745955526874056197)
        ·
          refine ⟨1657430014866661288885537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8839626745955526874056197 1657430014866661288885537)
          ·
            refine ⟨1243072511149995966664153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1657430014866661288885537 1243072511149995966664153)
            ·
              refine ⟨932304383362496974998115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1243072511149995966664153 932304383362496974998115)
              ·
                refine ⟨1398456575043745462497173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 932304383362496974998115 1398456575043745462497173)
                ·
                  refine ⟨65552651955175568554555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1398456575043745462497173 65552651955175568554555)
                  ·
                    rfl

theorem cell22_574485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_574485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574485 prefixEnd_574485 := by exact prefixLift 574485
  have htrace : WordTrace (prefixWord ++ tailWord_574485) baseStart_574485 baseEnd_574485 := by
    simpa [prefixWord, tailWord_574485, baseEnd_574485] using wordTrace_append hprefix tailTrace_574485
  have hstable : (prefixWord ++ tailWord_574485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574485).length < 2 ^ (prefixWord ++ tailWord_574485).sum := by decide
  have hdescent : baseEnd_574485 < baseStart_574485 := by decide
  rcases family_descends (prefixWord ++ tailWord_574485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574513 : List Nat := [1, 2, 2, 3, 1, 2, 3, 8]
def baseStart_574513 : Nat := 118140960795 + 574513 * 2 ^ 59
def prefixEnd_574513 : Nat := 4983230072969 + 3 ^ 40 * 574513 * 2
def baseEnd_574513 : Nat := 21851948981971551773731

theorem tailTrace_574513 : CollatzResearch.WordTrace tailWord_574513 prefixEnd_574513 21851948981971551773731 := by
  unfold tailWord_574513
  simp only [CollatzResearch.WordTrace]
  refine ⟨20954210567644994853856193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13969473711763329902570795 20954210567644994853856193)
  ·
    refine ⟨15715657925733746140392145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20954210567644994853856193 15715657925733746140392145)
    ·
      refine ⟨11786743444300309605294109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15715657925733746140392145 11786743444300309605294109)
      ·
        refine ⟨4420028791612616101985291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11786743444300309605294109 4420028791612616101985291)
        ·
          refine ⟨6630043187418924152977937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4420028791612616101985291 6630043187418924152977937)
          ·
            refine ⟨4972532390564193114733453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6630043187418924152977937 4972532390564193114733453)
            ·
              refine ⟨1864699646461572418025045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4972532390564193114733453 1864699646461572418025045)
              ·
                refine ⟨21851948981971551773731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1864699646461572418025045 21851948981971551773731)
                ·
                  rfl

theorem cell22_574513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 8].length) (baseStart_574513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574513 prefixEnd_574513 := by exact prefixLift 574513
  have htrace : WordTrace (prefixWord ++ tailWord_574513) baseStart_574513 baseEnd_574513 := by
    simpa [prefixWord, tailWord_574513, baseEnd_574513] using wordTrace_append hprefix tailTrace_574513
  have hstable : (prefixWord ++ tailWord_574513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574513).length < 2 ^ (prefixWord ++ tailWord_574513).sum := by decide
  have hdescent : baseEnd_574513 < baseStart_574513 := by decide
  rcases family_descends (prefixWord ++ tailWord_574513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574534 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_574534 : Nat := 118140960795 + 574534 * 2 ^ 59
def prefixEnd_574534 : Nat := 4983230072969 + 3 ^ 40 * 574534 * 2
def baseEnd_574534 : Nat := 196674729566906911188515

theorem tailTrace_574534 : CollatzResearch.WordTrace tailWord_574534 prefixEnd_574534 196674729566906911188515 := by
  unfold tailWord_574534
  simp only [CollatzResearch.WordTrace]
  refine ⟨654843015642778607511583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13969984333712610293580437 654843015642778607511583)
  ·
    refine ⟨982264523464167911267375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 654843015642778607511583 982264523464167911267375)
    ·
      refine ⟨1473396785196251866901063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 982264523464167911267375 1473396785196251866901063)
      ·
        refine ⟨2210095177794377800351595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1473396785196251866901063 2210095177794377800351595)
        ·
          refine ⟨3315142766691566700527393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2210095177794377800351595 3315142766691566700527393)
          ·
            refine ⟨2486357075018675025395545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3315142766691566700527393 2486357075018675025395545)
            ·
              refine ⟨1864767806264006269046659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2486357075018675025395545 1864767806264006269046659)
              ·
                refine ⟨2797151709396009403569989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1864767806264006269046659 2797151709396009403569989)
                ·
                  refine ⟨524465945511751763169373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2797151709396009403569989 524465945511751763169373)
                  ·
                    refine ⟨196674729566906911188515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 524465945511751763169373 196674729566906911188515)
                    ·
                      rfl

theorem cell22_574534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_574534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574534 prefixEnd_574534 := by exact prefixLift 574534
  have htrace : WordTrace (prefixWord ++ tailWord_574534) baseStart_574534 baseEnd_574534 := by
    simpa [prefixWord, tailWord_574534, baseEnd_574534] using wordTrace_append hprefix tailTrace_574534
  have hstable : (prefixWord ++ tailWord_574534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574534).length < 2 ^ (prefixWord ++ tailWord_574534).sum := by decide
  have hdescent : baseEnd_574534 < baseStart_574534 := by decide
  rcases family_descends (prefixWord ++ tailWord_574534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574596 : List Nat := [2, 3, 2, 1, 2, 2, 4, 2, 1, 3]
def baseStart_574596 : Nat := 118140960795 + 574596 * 2 ^ 59
def prefixEnd_574596 : Nat := 4983230072969 + 3 ^ 40 * 574596 * 2
def baseEnd_574596 : Nat := 196695953433959416138325

theorem tailTrace_574596 : CollatzResearch.WordTrace tailWord_574596 prefixEnd_574596 196695953433959416138325 := by
  unfold tailWord_574596
  simp only [CollatzResearch.WordTrace]
  refine ⟨10478618913172150014563821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13971491884229533352751761 10478618913172150014563821)
  ·
    refine ⟨3929482092439556255461433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10478618913172150014563821 3929482092439556255461433)
    ·
      refine ⟨2947111569329667191596075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3929482092439556255461433 2947111569329667191596075)
      ·
        refine ⟨4420667353994500787394113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2947111569329667191596075 4420667353994500787394113)
        ·
          refine ⟨3315500515495875590545585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4420667353994500787394113 3315500515495875590545585)
          ·
            refine ⟨2486625386621906692909189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3315500515495875590545585 2486625386621906692909189)
            ·
              refine ⟨466242259991607504920473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2486625386621906692909189 466242259991607504920473)
              ·
                refine ⟨349681694993705628690355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466242259991607504920473 349681694993705628690355)
                ·
                  refine ⟨524522542490558443035533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349681694993705628690355 524522542490558443035533)
                  ·
                    refine ⟨196695953433959416138325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 524522542490558443035533 196695953433959416138325)
                    ·
                      rfl

theorem cell22_574596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_574596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574596 prefixEnd_574596 := by exact prefixLift 574596
  have htrace : WordTrace (prefixWord ++ tailWord_574596) baseStart_574596 baseEnd_574596 := by
    simpa [prefixWord, tailWord_574596, baseEnd_574596] using wordTrace_append hprefix tailTrace_574596
  have hstable : (prefixWord ++ tailWord_574596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574596).length < 2 ^ (prefixWord ++ tailWord_574596).sum := by decide
  have hdescent : baseEnd_574596 < baseStart_574596 := by decide
  rcases family_descends (prefixWord ++ tailWord_574596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574603 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 10]
def baseStart_574603 : Nat := 118140960795 + 574603 * 2 ^ 59
def prefixEnd_574603 : Nat := 4983230072969 + 3 ^ 40 * 574603 * 2
def baseEnd_574603 : Nat := 65566116559004577071101

theorem tailTrace_574603 : CollatzResearch.WordTrace tailWord_574603 prefixEnd_574603 65566116559004577071101 := by
  unfold tailWord_574603
  simp only [CollatzResearch.WordTrace]
  refine ⟨20957493137318940224632463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13971662091545960149754975 20957493137318940224632463)
  ·
    refine ⟨31436239705978410336948695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20957493137318940224632463 31436239705978410336948695)
    ·
      refine ⟨47154359558967615505423043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31436239705978410336948695 47154359558967615505423043)
      ·
        refine ⟨70731539338451423258134565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47154359558967615505423043 70731539338451423258134565)
        ·
          refine ⟨13262163625959641860900231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70731539338451423258134565 13262163625959641860900231)
          ·
            refine ⟨19893245438939462791350347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13262163625959641860900231 19893245438939462791350347)
            ·
              refine ⟨29839868158409194187025521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19893245438939462791350347 29839868158409194187025521)
              ·
                refine ⟨22379901118806895640269141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29839868158409194187025521 22379901118806895640269141)
                ·
                  refine ⟨65566116559004577071101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 22379901118806895640269141 65566116559004577071101)
                  ·
                    rfl

theorem cell22_574603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 10].length) (baseStart_574603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574603 prefixEnd_574603 := by exact prefixLift 574603
  have htrace : WordTrace (prefixWord ++ tailWord_574603) baseStart_574603 baseEnd_574603 := by
    simpa [prefixWord, tailWord_574603, baseEnd_574603] using wordTrace_append hprefix tailTrace_574603
  have hstable : (prefixWord ++ tailWord_574603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574603).length < 2 ^ (prefixWord ++ tailWord_574603).sum := by decide
  have hdescent : baseEnd_574603 < baseStart_574603 := by decide
  rcases family_descends (prefixWord ++ tailWord_574603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574620 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 8]
def baseStart_574620 : Nat := 118140960795 + 574620 * 2 ^ 59
def prefixEnd_574620 : Nat := 4983230072969 + 3 ^ 40 * 574620 * 2
def baseEnd_574620 : Nat := 65568056374810451179417

theorem tailTrace_574620 : CollatzResearch.WordTrace tailWord_574620 prefixEnd_574620 65568056374810451179417 := by
  unfold tailWord_574620
  simp only [CollatzResearch.WordTrace]
  refine ⟨10479056589128676064000657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13972075452171568085334209 10479056589128676064000657)
  ·
    refine ⟨7859292441846507048000493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10479056589128676064000657 7859292441846507048000493)
    ·
      refine ⟨2947234665692440143000185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7859292441846507048000493 2947234665692440143000185)
      ·
        refine ⟨2210425999269330107250139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2947234665692440143000185 2210425999269330107250139)
        ·
          refine ⟨3315638998903995160875209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2210425999269330107250139 3315638998903995160875209)
          ·
            refine ⟨2486729249177996370656407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3315638998903995160875209 2486729249177996370656407)
            ·
              refine ⟨3730093873766994555984611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2486729249177996370656407 3730093873766994555984611)
              ·
                refine ⟨5595140810650491833976917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3730093873766994555984611 5595140810650491833976917)
                ·
                  refine ⟨65568056374810451179417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5595140810650491833976917 65568056374810451179417)
                  ·
                    rfl

theorem cell22_574620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_574620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574620 prefixEnd_574620 := by exact prefixLift 574620
  have htrace : WordTrace (prefixWord ++ tailWord_574620) baseStart_574620 baseEnd_574620 := by
    simpa [prefixWord, tailWord_574620, baseEnd_574620] using wordTrace_append hprefix tailTrace_574620
  have hstable : (prefixWord ++ tailWord_574620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574620).length < 2 ^ (prefixWord ++ tailWord_574620).sum := by decide
  have hdescent : baseEnd_574620 < baseStart_574620 := by decide
  rcases family_descends (prefixWord ++ tailWord_574620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574650 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 4, 4]
def baseStart_574650 : Nat := 118140960795 + 574650 * 2 ^ 59
def prefixEnd_574650 : Nat := 4983230072969 + 3 ^ 40 * 574650 * 2
def baseEnd_574650 : Nat := 196714438737521275288159

theorem tailTrace_574650 : CollatzResearch.WordTrace tailWord_574650 prefixEnd_574650 196714438737521275288159 := by
  unfold tailWord_574650
  simp only [CollatzResearch.WordTrace]
  refine ⟨5239801842037166812898351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13972804912099111501062269 5239801842037166812898351)
  ·
    refine ⟨7859702763055750219347527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5239801842037166812898351 7859702763055750219347527)
    ·
      refine ⟨11789554144583625329021291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7859702763055750219347527 11789554144583625329021291)
      ·
        refine ⟨17684331216875437993531937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11789554144583625329021291 17684331216875437993531937)
        ·
          refine ⟨13263248412656578495148953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17684331216875437993531937 13263248412656578495148953)
          ·
            refine ⟨9947436309492433871361715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13263248412656578495148953 9947436309492433871361715)
            ·
              refine ⟨14921154464238650807042573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9947436309492433871361715 14921154464238650807042573)
              ·
                refine ⟨5595432924089494052640965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14921154464238650807042573 5595432924089494052640965)
                ·
                  refine ⟨1049143673266780134870181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5595432924089494052640965 1049143673266780134870181)
                  ·
                    refine ⟨196714438737521275288159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1049143673266780134870181 196714438737521275288159)
                    ·
                      rfl

theorem cell22_574650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_574650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574650 prefixEnd_574650 := by exact prefixLift 574650
  have htrace : WordTrace (prefixWord ++ tailWord_574650) baseStart_574650 baseEnd_574650 := by
    simpa [prefixWord, tailWord_574650, baseEnd_574650] using wordTrace_append hprefix tailTrace_574650
  have hstable : (prefixWord ++ tailWord_574650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574650).length < 2 ^ (prefixWord ++ tailWord_574650).sum := by decide
  have hdescent : baseEnd_574650 < baseStart_574650 := by decide
  rcases family_descends (prefixWord ++ tailWord_574650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574654 : List Nat := [4, 2, 1, 1, 3, 1, 2, 4, 4]
def baseStart_574654 : Nat := 118140960795 + 574654 * 2 ^ 59
def prefixEnd_574654 : Nat := 4983230072969 + 3 ^ 40 * 574654 * 2
def baseEnd_574654 : Nat := 65571936006422199396049

theorem tailTrace_574654 : CollatzResearch.WordTrace tailWord_574654 prefixEnd_574654 65571936006422199396049 := by
  unfold tailWord_574654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2619919157516771991842377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13972902173422783956492677 2619919157516771991842377)
  ·
    refine ⟨1964939368137578993881783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2619919157516771991842377 1964939368137578993881783)
    ·
      refine ⟨2947409052206368490822675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1964939368137578993881783 2947409052206368490822675)
      ·
        refine ⟨4421113578309552736234013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2947409052206368490822675 4421113578309552736234013)
        ·
          refine ⟨1657917591866082276087755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4421113578309552736234013 1657917591866082276087755)
          ·
            refine ⟨2486876387799123414131633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657917591866082276087755 2486876387799123414131633)
            ·
              refine ⟨1865157290849342560598725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2486876387799123414131633 1865157290849342560598725)
              ·
                refine ⟨349716992034251730112261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1865157290849342560598725 349716992034251730112261)
                ·
                  refine ⟨65571936006422199396049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 349716992034251730112261 65571936006422199396049)
                  ·
                    rfl

theorem cell22_574654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_574654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574654 prefixEnd_574654 := by exact prefixLift 574654
  have htrace : WordTrace (prefixWord ++ tailWord_574654) baseStart_574654 baseEnd_574654 := by
    simpa [prefixWord, tailWord_574654, baseEnd_574654] using wordTrace_append hprefix tailTrace_574654
  have hstable : (prefixWord ++ tailWord_574654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574654).length < 2 ^ (prefixWord ++ tailWord_574654).sum := by decide
  have hdescent : baseEnd_574654 < baseStart_574654 := by decide
  rcases family_descends (prefixWord ++ tailWord_574654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574725 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 1, 7]
def baseStart_574725 : Nat := 118140960795 + 574725 * 2 ^ 59
def prefixEnd_574725 : Nat := 4983230072969 + 3 ^ 40 * 574725 * 2
def baseEnd_574725 : Nat := 196740112770246079662929

theorem tailTrace_574725 : CollatzResearch.WordTrace tailWord_574725 prefixEnd_574725 196740112770246079662929 := by
  unfold tailWord_574725
  simp only [CollatzResearch.WordTrace]
  refine ⟨20961942842876955060573629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13974628561917970040382419 20961942842876955060573629)
  ·
    refine ⟨7860728566078858147715111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20961942842876955060573629 7860728566078858147715111)
    ·
      refine ⟨11791092849118287221572667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7860728566078858147715111 11791092849118287221572667)
      ·
        refine ⟨17686639273677430832359001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11791092849118287221572667 17686639273677430832359001)
        ·
          refine ⟨13264979455258073124269251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17686639273677430832359001 13264979455258073124269251)
          ·
            refine ⟨19897469182887109686403877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13264979455258073124269251 19897469182887109686403877)
            ·
              refine ⟨3730775471791333066200727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19897469182887109686403877 3730775471791333066200727)
              ·
                refine ⟨5596163207686999599301091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3730775471791333066200727 5596163207686999599301091)
                ·
                  refine ⟨8394244811530499398951637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5596163207686999599301091 8394244811530499398951637)
                  ·
                    refine ⟨196740112770246079662929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8394244811530499398951637 196740112770246079662929)
                    ·
                      rfl

theorem cell22_574725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_574725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574725 prefixEnd_574725 := by exact prefixLift 574725
  have htrace : WordTrace (prefixWord ++ tailWord_574725) baseStart_574725 baseEnd_574725 := by
    simpa [prefixWord, tailWord_574725, baseEnd_574725] using wordTrace_append hprefix tailTrace_574725
  have hstable : (prefixWord ++ tailWord_574725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574725).length < 2 ^ (prefixWord ++ tailWord_574725).sum := by decide
  have hdescent : baseEnd_574725 < baseStart_574725 := by decide
  rcases family_descends (prefixWord ++ tailWord_574725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574765 : List Nat := [1, 5, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_574765 : Nat := 118140960795 + 574765 * 2 ^ 59
def prefixEnd_574765 : Nat := 4983230072969 + 3 ^ 40 * 574765 * 2
def baseEnd_574765 : Nat := 196753805587699308662807

theorem tailTrace_574765 : CollatzResearch.WordTrace tailWord_574765 prefixEnd_574765 196753805587699308662807 := by
  unfold tailWord_574765
  simp only [CollatzResearch.WordTrace]
  refine ⟨20963401762732041892029749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13975601175154694594686499 20963401762732041892029749)
  ·
    refine ⟨1965318915256128927377789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20963401762732041892029749 1965318915256128927377789)
    ·
      refine ⟨736994593221048347766671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1965318915256128927377789 736994593221048347766671)
      ·
        refine ⟨1105491889831572521650007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736994593221048347766671 1105491889831572521650007)
        ·
          refine ⟨1658237834747358782475011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1105491889831572521650007 1658237834747358782475011)
          ·
            refine ⟨2487356752121038173712517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1658237834747358782475011 2487356752121038173712517)
            ·
              refine ⟨466379391022694657571097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2487356752121038173712517 466379391022694657571097)
              ·
                refine ⟨349784543267020993178323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466379391022694657571097 349784543267020993178323)
                ·
                  refine ⟨524676814900531489767485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349784543267020993178323 524676814900531489767485)
                  ·
                    refine ⟨196753805587699308662807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 524676814900531489767485 196753805587699308662807)
                    ·
                      rfl

theorem cell22_574765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_574765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574765 prefixEnd_574765 := by exact prefixLift 574765
  have htrace : WordTrace (prefixWord ++ tailWord_574765) baseStart_574765 baseEnd_574765 := by
    simpa [prefixWord, tailWord_574765, baseEnd_574765] using wordTrace_append hprefix tailTrace_574765
  have hstable : (prefixWord ++ tailWord_574765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574765).length < 2 ^ (prefixWord ++ tailWord_574765).sum := by decide
  have hdescent : baseEnd_574765 < baseStart_574765 := by decide
  rcases family_descends (prefixWord ++ tailWord_574765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574787 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 6, 3]
def baseStart_574787 : Nat := 118140960795 + 574787 * 2 ^ 59
def prefixEnd_574787 : Nat := 4983230072969 + 3 ^ 40 * 574787 * 2
def baseEnd_574787 : Nat := 196761336637298584612739

theorem tailTrace_574787 : CollatzResearch.WordTrace tailWord_574787 prefixEnd_574787 196761336637298584612739 := by
  unfold tailWord_574787
  simp only [CollatzResearch.WordTrace]
  refine ⟨20964204168652339649330615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13976136112434893099553743 20964204168652339649330615)
  ·
    refine ⟨31446306252978509473995923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20964204168652339649330615 31446306252978509473995923)
    ·
      refine ⟨47169459379467764210993885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31446306252978509473995923 47169459379467764210993885)
      ·
        refine ⟨17688547267300411579122707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47169459379467764210993885 17688547267300411579122707)
        ·
          refine ⟨26532820900950617368684061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17688547267300411579122707 26532820900950617368684061)
          ·
            refine ⟨9949807837856481513256523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26532820900950617368684061 9949807837856481513256523)
            ·
              refine ⟨14924711756784722269884785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9949807837856481513256523 14924711756784722269884785)
              ·
                refine ⟨11193533817588541702413589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14924711756784722269884785 11193533817588541702413589)
                ·
                  refine ⟨524696897699462892300637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11193533817588541702413589 524696897699462892300637)
                  ·
                    refine ⟨196761336637298584612739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 524696897699462892300637 196761336637298584612739)
                    ·
                      rfl

theorem cell22_574787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 3].length) (baseStart_574787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574787 prefixEnd_574787 := by exact prefixLift 574787
  have htrace : WordTrace (prefixWord ++ tailWord_574787) baseStart_574787 baseEnd_574787 := by
    simpa [prefixWord, tailWord_574787, baseEnd_574787] using wordTrace_append hprefix tailTrace_574787
  have hstable : (prefixWord ++ tailWord_574787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574787).length < 2 ^ (prefixWord ++ tailWord_574787).sum := by decide
  have hdescent : baseEnd_574787 < baseStart_574787 := by decide
  rcases family_descends (prefixWord ++ tailWord_574787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574804 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_574804 : Nat := 118140960795 + 574804 * 2 ^ 59
def prefixEnd_574804 : Nat := 4983230072969 + 3 ^ 40 * 574804 * 2
def baseEnd_574804 : Nat := 196767156084716206937687

theorem tailTrace_574804 : CollatzResearch.WordTrace tailWord_574804 prefixEnd_574804 196767156084716206937687 := by
  unfold tailWord_574804
  simp only [CollatzResearch.WordTrace]
  refine ⟨10482412104795375776349733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13976549473060501035132977 10482412104795375776349733)
  ·
    refine ⟨1965452269649132958065575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10482412104795375776349733 1965452269649132958065575)
    ·
      refine ⟨2948178404473699437098363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1965452269649132958065575 2948178404473699437098363)
      ·
        refine ⟨4422267606710549155647545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2948178404473699437098363 4422267606710549155647545)
        ·
          refine ⟨3316700705032911866735659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4422267606710549155647545 3316700705032911866735659)
          ·
            refine ⟨4975051057549367800103489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3316700705032911866735659 4975051057549367800103489)
            ·
              refine ⟨3731288293162025850077617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4975051057549367800103489 3731288293162025850077617)
              ·
                refine ⟨2798466219871519387558213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3731288293162025850077617 2798466219871519387558213)
                ·
                  refine ⟨524712416225909885167165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2798466219871519387558213 524712416225909885167165)
                  ·
                    refine ⟨196767156084716206937687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 524712416225909885167165 196767156084716206937687)
                    ·
                      rfl

theorem cell22_574804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_574804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574804 prefixEnd_574804 := by exact prefixLift 574804
  have htrace : WordTrace (prefixWord ++ tailWord_574804) baseStart_574804 baseEnd_574804 := by
    simpa [prefixWord, tailWord_574804, baseEnd_574804] using wordTrace_append hprefix tailTrace_574804
  have hstable : (prefixWord ++ tailWord_574804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574804).length < 2 ^ (prefixWord ++ tailWord_574804).sum := by decide
  have hdescent : baseEnd_574804 < baseStart_574804 := by decide
  rcases family_descends (prefixWord ++ tailWord_574804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574883 : List Nat := [1, 1, 1, 4, 1, 3, 5, 2, 1, 3]
def baseStart_574883 : Nat := 118140960795 + 574883 * 2 ^ 59
def prefixEnd_574883 : Nat := 4983230072969 + 3 ^ 40 * 574883 * 2
def baseEnd_574883 : Nat := 196794199399186334212445

theorem tailTrace_574883 : CollatzResearch.WordTrace tailWord_574883 prefixEnd_574883 196794199399186334212445 := by
  unfold tailWord_574883
  simp only [CollatzResearch.WordTrace]
  refine ⟨20967705576304548044825303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13978470384203032029883535 20967705576304548044825303)
  ·
    refine ⟨31451558364456822067237955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20967705576304548044825303 31451558364456822067237955)
    ·
      refine ⟨47177337546685233100856933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31451558364456822067237955 47177337546685233100856933)
      ·
        refine ⟨8845750790003481206410675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47177337546685233100856933 8845750790003481206410675)
        ·
          refine ⟨13268626185005221809616013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8845750790003481206410675 13268626185005221809616013)
          ·
            refine ⟨4975734819376958178606005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13268626185005221809616013 4975734819376958178606005)
            ·
              refine ⟨466475139316589829244313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4975734819376958178606005 466475139316589829244313)
              ·
                refine ⟨349856354487442371933235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466475139316589829244313 349856354487442371933235)
                ·
                  refine ⟨524784531731163557899853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349856354487442371933235 524784531731163557899853)
                  ·
                    refine ⟨196794199399186334212445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 524784531731163557899853 196794199399186334212445)
                    ·
                      rfl

theorem cell22_574883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 1, 3].length) (baseStart_574883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574883 prefixEnd_574883 := by exact prefixLift 574883
  have htrace : WordTrace (prefixWord ++ tailWord_574883) baseStart_574883 baseEnd_574883 := by
    simpa [prefixWord, tailWord_574883, baseEnd_574883] using wordTrace_append hprefix tailTrace_574883
  have hstable : (prefixWord ++ tailWord_574883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574883).length < 2 ^ (prefixWord ++ tailWord_574883).sum := by decide
  have hdescent : baseEnd_574883 < baseStart_574883 := by decide
  rcases family_descends (prefixWord ++ tailWord_574883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574909 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_574909 : Nat := 118140960795 + 574909 * 2 ^ 59
def prefixEnd_574909 : Nat := 4983230072969 + 3 ^ 40 * 574909 * 2
def baseEnd_574909 : Nat := 196803099730530933062365

theorem tailTrace_574909 : CollatzResearch.WordTrace tailWord_574909 prefixEnd_574909 196803099730530933062365 := by
  unfold tailWord_574909
  simp only [CollatzResearch.WordTrace]
  refine ⟨20968653874210354485271781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13979102582806902990181187 20968653874210354485271781)
  ·
    refine ⟨3931622601414441465988459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20968653874210354485271781 3931622601414441465988459)
    ·
      refine ⟨5897433902121662198982689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3931622601414441465988459 5897433902121662198982689)
      ·
        refine ⟨4423075426591246649237017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5897433902121662198982689 4423075426591246649237017)
        ·
          refine ⟨3317306569943434986927763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4423075426591246649237017 3317306569943434986927763)
          ·
            refine ⟨4975959854915152480391645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3317306569943434986927763 4975959854915152480391645)
            ·
              refine ⟨1865984945593182180146867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4975959854915152480391645 1865984945593182180146867)
              ·
                refine ⟨2798977418389773270220301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1865984945593182180146867 2798977418389773270220301)
                ·
                  refine ⟨1049616531896164976332613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2798977418389773270220301 1049616531896164976332613)
                  ·
                    refine ⟨196803099730530933062365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1049616531896164976332613 196803099730530933062365)
                    ·
                      rfl

theorem cell22_574909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_574909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574909 prefixEnd_574909 := by exact prefixLift 574909
  have htrace : WordTrace (prefixWord ++ tailWord_574909) baseStart_574909 baseEnd_574909 := by
    simpa [prefixWord, tailWord_574909, baseEnd_574909] using wordTrace_append hprefix tailTrace_574909
  have hstable : (prefixWord ++ tailWord_574909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574909).length < 2 ^ (prefixWord ++ tailWord_574909).sum := by decide
  have hdescent : baseEnd_574909 < baseStart_574909 := by decide
  rcases family_descends (prefixWord ++ tailWord_574909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574967 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 1, 9]
def baseStart_574967 : Nat := 118140960795 + 574967 * 2 ^ 59
def prefixEnd_574967 : Nat := 4983230072969 + 3 ^ 40 * 574967 * 2
def baseEnd_574967 : Nat := 196822954315838115112187

theorem tailTrace_574967 : CollatzResearch.WordTrace tailWord_574967 prefixEnd_574967 196822954315838115112187 := by
  unfold tailWord_574967
  simp only [CollatzResearch.WordTrace]
  refine ⟨20970769308000230390883155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13980512872000153593922103 20970769308000230390883155)
  ·
    refine ⟨31456153962000345586324733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20970769308000230390883155 31456153962000345586324733)
    ·
      refine ⟨11796057735750129594871775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31456153962000345586324733 11796057735750129594871775)
      ·
        refine ⟨17694086603625194392307663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11796057735750129594871775 17694086603625194392307663)
        ·
          refine ⟨26541129905437791588461495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17694086603625194392307663 26541129905437791588461495)
          ·
            refine ⟨39811694858156687382692243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26541129905437791588461495 39811694858156687382692243)
            ·
              refine ⟨59717542287235031074038365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39811694858156687382692243 59717542287235031074038365)
              ·
                refine ⟨22394078357713136652764387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59717542287235031074038365 22394078357713136652764387)
                ·
                  refine ⟨33591117536569704979146581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22394078357713136652764387 33591117536569704979146581)
                  ·
                    refine ⟨196822954315838115112187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 33591117536569704979146581 196822954315838115112187)
                    ·
                      rfl

theorem cell22_574967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_574967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574967 prefixEnd_574967 := by exact prefixLift 574967
  have htrace : WordTrace (prefixWord ++ tailWord_574967) baseStart_574967 baseEnd_574967 := by
    simpa [prefixWord, tailWord_574967, baseEnd_574967] using wordTrace_append hprefix tailTrace_574967
  have hstable : (prefixWord ++ tailWord_574967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574967).length < 2 ^ (prefixWord ++ tailWord_574967).sum := by decide
  have hdescent : baseEnd_574967 < baseStart_574967 := by decide
  rcases family_descends (prefixWord ++ tailWord_574967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574990 : List Nat := [4, 1, 1, 2, 4, 2, 1, 2, 2, 3]
def baseStart_574990 : Nat := 118140960795 + 574990 * 2 ^ 59
def prefixEnd_574990 : Nat := 4983230072969 + 3 ^ 40 * 574990 * 2
def baseEnd_574990 : Nat := 196830827685873721787117

theorem tailTrace_574990 : CollatzResearch.WordTrace tailWord_574990 prefixEnd_574990 196830827685873721787117 := by
  unfold tailWord_574990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2621451023364613164871303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13981072124611270212646949 2621451023364613164871303)
  ·
    refine ⟨3932176535046919747306955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2621451023364613164871303 3932176535046919747306955)
    ·
      refine ⟨5898264802570379620960433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3932176535046919747306955 5898264802570379620960433)
      ·
        refine ⟨4423698601927784715720325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5898264802570379620960433 4423698601927784715720325)
        ·
          refine ⟨829443487861459634197561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4423698601927784715720325 829443487861459634197561)
          ·
            refine ⟨622082615896094725648171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 829443487861459634197561 622082615896094725648171)
            ·
              refine ⟨933123923844142088472257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622082615896094725648171 933123923844142088472257)
              ·
                refine ⟨699842942883106566354193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 933123923844142088472257 699842942883106566354193)
                ·
                  refine ⟨524882207162329924765645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 699842942883106566354193 524882207162329924765645)
                  ·
                    refine ⟨196830827685873721787117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 524882207162329924765645 196830827685873721787117)
                    ·
                      rfl

theorem cell22_574990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_574990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_574990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_574990 prefixEnd_574990 := by exact prefixLift 574990
  have htrace : WordTrace (prefixWord ++ tailWord_574990) baseStart_574990 baseEnd_574990 := by
    simpa [prefixWord, tailWord_574990, baseEnd_574990] using wordTrace_append hprefix tailTrace_574990
  have hstable : (prefixWord ++ tailWord_574990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574990).length < 2 ^ (prefixWord ++ tailWord_574990).sum := by decide
  have hdescent : baseEnd_574990 < baseStart_574990 := by decide
  rcases family_descends (prefixWord ++ tailWord_574990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575089 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 1, 6]
def baseStart_575089 : Nat := 118140960795 + 575089 * 2 ^ 59
def prefixEnd_575089 : Nat := 4983230072969 + 3 ^ 40 * 575089 * 2
def baseEnd_575089 : Nat := 196864717409070463561813

theorem tailTrace_575089 : CollatzResearch.WordTrace tailWord_575089 prefixEnd_575089 196864717409070463561813 := by
  unfold tailWord_575089
  simp only [CollatzResearch.WordTrace]
  refine ⟨20975219013558245226824321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13983479342372163484549547 20975219013558245226824321)
  ·
    refine ⟨15731414260168683920118241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20975219013558245226824321 15731414260168683920118241)
    ·
      refine ⟨11798560695126512940088681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15731414260168683920118241 11798560695126512940088681)
      ·
        refine ⟨8848920521344884705066511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11798560695126512940088681 8848920521344884705066511)
        ·
          refine ⟨13273380782017327057599767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8848920521344884705066511 13273380782017327057599767)
          ·
            refine ⟨19910071173025990586399651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13273380782017327057599767 19910071173025990586399651)
            ·
              refine ⟨29865106759538985879599477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19910071173025990586399651 29865106759538985879599477)
              ·
                refine ⟨2799853758706779926212451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29865106759538985879599477 2799853758706779926212451)
                ·
                  refine ⟨4199780638060169889318677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2799853758706779926212451 4199780638060169889318677)
                  ·
                    refine ⟨196864717409070463561813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4199780638060169889318677 196864717409070463561813)
                    ·
                      rfl

theorem cell22_575089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_575089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575089 prefixEnd_575089 := by exact prefixLift 575089
  have htrace : WordTrace (prefixWord ++ tailWord_575089) baseStart_575089 baseEnd_575089 := by
    simpa [prefixWord, tailWord_575089, baseEnd_575089] using wordTrace_append hprefix tailTrace_575089
  have hstable : (prefixWord ++ tailWord_575089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575089).length < 2 ^ (prefixWord ++ tailWord_575089).sum := by decide
  have hdescent : baseEnd_575089 < baseStart_575089 := by decide
  rcases family_descends (prefixWord ++ tailWord_575089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575144 : List Nat := [2, 1, 7, 1, 1, 1, 2, 3, 4]
def baseStart_575144 : Nat := 118140960795 + 575144 * 2 ^ 59
def prefixEnd_575144 : Nat := 4983230072969 + 3 ^ 40 * 575144 * 2
def baseEnd_575144 : Nat := 65627848344356217812215

theorem tailTrace_575144 : CollatzResearch.WordTrace tailWord_575144 prefixEnd_575144 65627848344356217812215 := by
  unfold tailWord_575144
  simp only [CollatzResearch.WordTrace]
  refine ⟨10488612514179494810038243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13984816685572659746717657 10488612514179494810038243)
  ·
    refine ⟨15732918771269242215057365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10488612514179494810038243 15732918771269242215057365)
    ·
      refine ⟨368740283701622864415407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 15732918771269242215057365 368740283701622864415407)
      ·
        refine ⟨553110425552434296623111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368740283701622864415407 553110425552434296623111)
        ·
          refine ⟨829665638328651444934667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553110425552434296623111 829665638328651444934667)
          ·
            refine ⟨1244498457492977167402001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829665638328651444934667 1244498457492977167402001)
            ·
              refine ⟨933373843119732875551501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1244498457492977167402001 933373843119732875551501)
              ·
                refine ⟨350015191169899828331813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 933373843119732875551501 350015191169899828331813)
                ·
                  refine ⟨65627848344356217812215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 350015191169899828331813 65627848344356217812215)
                  ·
                    rfl

theorem cell22_575144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 4].length) (baseStart_575144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575144 prefixEnd_575144 := by exact prefixLift 575144
  have htrace : WordTrace (prefixWord ++ tailWord_575144) baseStart_575144 baseEnd_575144 := by
    simpa [prefixWord, tailWord_575144, baseEnd_575144] using wordTrace_append hprefix tailTrace_575144
  have hstable : (prefixWord ++ tailWord_575144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575144).length < 2 ^ (prefixWord ++ tailWord_575144).sum := by decide
  have hdescent : baseEnd_575144 < baseStart_575144 := by decide
  rcases family_descends (prefixWord ++ tailWord_575144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575241 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 6, 4]
def baseStart_575241 : Nat := 118140960795 + 575241 * 2 ^ 59
def prefixEnd_575241 : Nat := 4983230072969 + 3 ^ 40 * 575241 * 2
def baseEnd_575241 : Nat := 196916750115392733761347

theorem tailTrace_575241 : CollatzResearch.WordTrace tailWord_575241 prefixEnd_575241 196916750115392733761347 := by
  unfold tailWord_575241
  simp only [CollatzResearch.WordTrace]
  refine ⟨20980762909007575186357577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13987175272671716790905051 20980762909007575186357577)
  ·
    refine ⟨15735572181755681389768183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20980762909007575186357577 15735572181755681389768183)
    ·
      refine ⟨23603358272633522084652275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15735572181755681389768183 23603358272633522084652275)
      ·
        refine ⟨35405037408950283126978413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23603358272633522084652275 35405037408950283126978413)
        ·
          refine ⟨13276889028356356172616905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35405037408950283126978413 13276889028356356172616905)
          ·
            refine ⟨9957666771267267129462679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13276889028356356172616905 9957666771267267129462679)
            ·
              refine ⟨14936500156900900694194019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9957666771267267129462679 14936500156900900694194019)
              ·
                refine ⟨22404750235351351041291029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14936500156900900694194019 22404750235351351041291029)
                ·
                  refine ⟨1050222667282094580060517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22404750235351351041291029 1050222667282094580060517)
                  ·
                    refine ⟨196916750115392733761347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1050222667282094580060517 196916750115392733761347)
                    ·
                      rfl

theorem cell22_575241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_575241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575241 prefixEnd_575241 := by exact prefixLift 575241
  have htrace : WordTrace (prefixWord ++ tailWord_575241) baseStart_575241 baseEnd_575241 := by
    simpa [prefixWord, tailWord_575241, baseEnd_575241] using wordTrace_append hprefix tailTrace_575241
  have hstable : (prefixWord ++ tailWord_575241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575241).length < 2 ^ (prefixWord ++ tailWord_575241).sum := by decide
  have hdescent : baseEnd_575241 < baseStart_575241 := by decide
  rcases family_descends (prefixWord ++ tailWord_575241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575256 : List Nat := [2, 1, 2, 3, 1, 1, 4, 8]
def baseStart_575256 : Nat := 118140960795 + 575256 * 2 ^ 59
def prefixEnd_575256 : Nat := 4983230072969 + 3 ^ 40 * 575256 * 2
def baseEnd_575256 : Nat := 21880209435770854959589

theorem tailTrace_575256 : CollatzResearch.WordTrace tailWord_575256 prefixEnd_575256 21880209435770854959589 := by
  unfold tailWord_575256
  simp only [CollatzResearch.WordTrace]
  refine ⟨10490655001976616374076811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13987540002635488498769081 10490655001976616374076811)
  ·
    refine ⟨15735982502964924561115217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10490655001976616374076811 15735982502964924561115217)
    ·
      refine ⟨11801986877223693420836413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15735982502964924561115217 11801986877223693420836413)
      ·
        refine ⟨4425745078958885032813655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11801986877223693420836413 4425745078958885032813655)
        ·
          refine ⟨6638617618438327549220483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4425745078958885032813655 6638617618438327549220483)
          ·
            refine ⟨9957926427657491323830725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6638617618438327549220483 9957926427657491323830725)
            ·
              refine ⟨1867111205185779623218261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9957926427657491323830725 1867111205185779623218261)
              ·
                refine ⟨21880209435770854959589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1867111205185779623218261 21880209435770854959589)
                ·
                  rfl

theorem cell22_575256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 8].length) (baseStart_575256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575256 prefixEnd_575256 := by exact prefixLift 575256
  have htrace : WordTrace (prefixWord ++ tailWord_575256) baseStart_575256 baseEnd_575256 := by
    simpa [prefixWord, tailWord_575256, baseEnd_575256] using wordTrace_append hprefix tailTrace_575256
  have hstable : (prefixWord ++ tailWord_575256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575256).length < 2 ^ (prefixWord ++ tailWord_575256).sum := by decide
  have hdescent : baseEnd_575256 < baseStart_575256 := by decide
  rcases family_descends (prefixWord ++ tailWord_575256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575258 : List Nat := [3, 1, 1, 3, 2, 2, 1, 3, 2, 4]
def baseStart_575258 : Nat := 118140960795 + 575258 * 2 ^ 59
def prefixEnd_575258 : Nat := 4983230072969 + 3 ^ 40 * 575258 * 2
def baseEnd_575258 : Nat := 196922569562810356086295

theorem tailTrace_575258 : CollatzResearch.WordTrace tailWord_575258 prefixEnd_575258 196922569562810356086295 := by
  unfold tailWord_575258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5245345737486496772431607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13987588633297324726484285 5245345737486496772431607)
  ·
    refine ⟨7868018606229745158647411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5245345737486496772431607 7868018606229745158647411)
    ·
      refine ⟨11802027909344617737971117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7868018606229745158647411 11802027909344617737971117)
      ·
        refine ⟨4425760466004231651739169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11802027909344617737971117 4425760466004231651739169)
        ·
          refine ⟨3319320349503173738804377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4425760466004231651739169 3319320349503173738804377)
          ·
            refine ⟨2489490262127380304103283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3319320349503173738804377 2489490262127380304103283)
            ·
              refine ⟨3734235393191070456154925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2489490262127380304103283 3734235393191070456154925)
              ·
                refine ⟨1400338272446651421058097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3734235393191070456154925 1400338272446651421058097)
                ·
                  refine ⟨1050253704334988565793573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1400338272446651421058097 1050253704334988565793573)
                  ·
                    refine ⟨196922569562810356086295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1050253704334988565793573 196922569562810356086295)
                    ·
                      rfl

theorem cell22_575258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_575258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575258 prefixEnd_575258 := by exact prefixLift 575258
  have htrace : WordTrace (prefixWord ++ tailWord_575258) baseStart_575258 baseEnd_575258 := by
    simpa [prefixWord, tailWord_575258, baseEnd_575258] using wordTrace_append hprefix tailTrace_575258
  have hstable : (prefixWord ++ tailWord_575258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575258).length < 2 ^ (prefixWord ++ tailWord_575258).sum := by decide
  have hdescent : baseEnd_575258 < baseStart_575258 := by decide
  rcases family_descends (prefixWord ++ tailWord_575258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575322 : List Nat := [3, 1, 1, 2, 1, 3, 4, 3, 1, 3]
def baseStart_575322 : Nat := 118140960795 + 575322 * 2 ^ 59
def prefixEnd_575322 : Nat := 4983230072969 + 3 ^ 40 * 575322 * 2
def baseEnd_575322 : Nat := 196944478070735522486099

theorem tailTrace_575322 : CollatzResearch.WordTrace tailWord_575322 prefixEnd_575322 196944478070735522486099 := by
  unfold tailWord_575322
  simp only [CollatzResearch.WordTrace]
  refine ⟨5245929305428531505014055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13989144814476084013370813 5245929305428531505014055)
  ·
    refine ⟨7868893958142797257521083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5245929305428531505014055 7868893958142797257521083)
    ·
      refine ⟨11803340937214195886281625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7868893958142797257521083 11803340937214195886281625)
      ·
        refine ⟨8852505702910646914711219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11803340937214195886281625 8852505702910646914711219)
        ·
          refine ⟨13278758554365970372066829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8852505702910646914711219 13278758554365970372066829)
          ·
            refine ⟨4979534457887238889525061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13278758554365970372066829 4979534457887238889525061)
            ·
              refine ⟨933662710853857291785949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4979534457887238889525061 933662710853857291785949)
              ·
                refine ⟨350123516570196484419731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 933662710853857291785949 350123516570196484419731)
                ·
                  refine ⟨525185274855294726629597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350123516570196484419731 525185274855294726629597)
                  ·
                    refine ⟨196944478070735522486099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 525185274855294726629597 196944478070735522486099)
                    ·
                      rfl

theorem cell22_575322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 1, 3].length) (baseStart_575322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575322 prefixEnd_575322 := by exact prefixLift 575322
  have htrace : WordTrace (prefixWord ++ tailWord_575322) baseStart_575322 baseEnd_575322 := by
    simpa [prefixWord, tailWord_575322, baseEnd_575322] using wordTrace_append hprefix tailTrace_575322
  have hstable : (prefixWord ++ tailWord_575322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575322).length < 2 ^ (prefixWord ++ tailWord_575322).sum := by decide
  have hdescent : baseEnd_575322 < baseStart_575322 := by decide
  rcases family_descends (prefixWord ++ tailWord_575322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575363 : List Nat := [1, 1, 1, 3, 4, 2, 2, 2, 6]
def baseStart_575363 : Nat := 118140960795 + 575363 * 2 ^ 59
def prefixEnd_575363 : Nat := 4983230072969 + 3 ^ 40 * 575363 * 2
def baseEnd_575363 : Nat := 65652837736208360736991

theorem tailTrace_575363 : CollatzResearch.WordTrace tailWord_575363 prefixEnd_575363 65652837736208360736991 := by
  unfold tailWord_575363
  simp only [CollatzResearch.WordTrace]
  refine ⟨20985212614565590022298743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13990141743043726681532495 20985212614565590022298743)
  ·
    refine ⟨31477818921848385033448115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20985212614565590022298743 31477818921848385033448115)
    ·
      refine ⟨47216728382772577550172173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31477818921848385033448115 47216728382772577550172173)
      ·
        refine ⟨17706273143539716581314565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47216728382772577550172173 17706273143539716581314565)
        ·
          refine ⟨3319926214413696858996481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17706273143539716581314565 3319926214413696858996481)
          ·
            refine ⟨2489944660810272644247361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3319926214413696858996481 2489944660810272644247361)
            ·
              refine ⟨1867458495607704483185521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2489944660810272644247361 1867458495607704483185521)
              ·
                refine ⟨1400593871705778362389141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1867458495607704483185521 1400593871705778362389141)
                ·
                  refine ⟨65652837736208360736991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1400593871705778362389141 65652837736208360736991)
                  ·
                    rfl

theorem cell22_575363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 6].length) (baseStart_575363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575363 prefixEnd_575363 := by exact prefixLift 575363
  have htrace : WordTrace (prefixWord ++ tailWord_575363) baseStart_575363 baseEnd_575363 := by
    simpa [prefixWord, tailWord_575363, baseEnd_575363] using wordTrace_append hprefix tailTrace_575363
  have hstable : (prefixWord ++ tailWord_575363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575363).length < 2 ^ (prefixWord ++ tailWord_575363).sum := by decide
  have hdescent : baseEnd_575363 < baseStart_575363 := by decide
  rcases family_descends (prefixWord ++ tailWord_575363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575365 : List Nat := [1, 3, 1, 1, 3, 2, 4, 2, 1, 4]
def baseStart_575365 : Nat := 118140960795 + 575365 * 2 ^ 59
def prefixEnd_575365 : Nat := 4983230072969 + 3 ^ 40 * 575365 * 2
def baseEnd_575365 : Nat := 196959197849497743660967

theorem tailTrace_575365 : CollatzResearch.WordTrace tailWord_575365 prefixEnd_575365 196959197849497743660967 := by
  unfold tailWord_575365
  simp only [CollatzResearch.WordTrace]
  refine ⟨20985285560558344363871549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13990190373705562909247699 20985285560558344363871549)
  ·
    refine ⟨7869482085209379136451831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20985285560558344363871549 7869482085209379136451831)
    ·
      refine ⟨11804223127814068704677747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7869482085209379136451831 11804223127814068704677747)
      ·
        refine ⟨17706334691721103057016621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11804223127814068704677747 17706334691721103057016621)
        ·
          refine ⟨6639875509395413646381233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17706334691721103057016621 6639875509395413646381233)
          ·
            refine ⟨4979906632046560234785925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6639875509395413646381233 4979906632046560234785925)
            ·
              refine ⟨933732493508730044022361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4979906632046560234785925 933732493508730044022361)
              ·
                refine ⟨700299370131547533016771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 933732493508730044022361 700299370131547533016771)
                ·
                  refine ⟨1050449055197321299525157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700299370131547533016771 1050449055197321299525157)
                  ·
                    refine ⟨196959197849497743660967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1050449055197321299525157 196959197849497743660967)
                    ·
                      rfl

theorem cell22_575365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_575365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575365 prefixEnd_575365 := by exact prefixLift 575365
  have htrace : WordTrace (prefixWord ++ tailWord_575365) baseStart_575365 baseEnd_575365 := by
    simpa [prefixWord, tailWord_575365, baseEnd_575365] using wordTrace_append hprefix tailTrace_575365
  have hstable : (prefixWord ++ tailWord_575365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575365).length < 2 ^ (prefixWord ++ tailWord_575365).sum := by decide
  have hdescent : baseEnd_575365 < baseStart_575365 := by decide
  rcases family_descends (prefixWord ++ tailWord_575365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575395 : List Nat := [1, 1, 1, 4, 1, 2, 1, 6, 2, 3]
def baseStart_575395 : Nat := 118140960795 + 575395 * 2 ^ 59
def prefixEnd_575395 : Nat := 4983230072969 + 3 ^ 40 * 575395 * 2
def baseEnd_575395 : Nat := 196969467462587665410875

theorem tailTrace_575395 : CollatzResearch.WordTrace tailWord_575395 prefixEnd_575395 196969467462587665410875 := by
  unfold tailWord_575395
  simp only [CollatzResearch.WordTrace]
  refine ⟨20986379750449659487463639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13990919833633106324975759 20986379750449659487463639)
  ·
    refine ⟨31479569625674489231195459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20986379750449659487463639 31479569625674489231195459)
    ·
      refine ⟨47219354438511733846793189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31479569625674489231195459 47219354438511733846793189)
      ·
        refine ⟨8853628957220950096273723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47219354438511733846793189 8853628957220950096273723)
        ·
          refine ⟨13280443435831425144410585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8853628957220950096273723 13280443435831425144410585)
          ·
            refine ⟨9960332576873568858307939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13280443435831425144410585 9960332576873568858307939)
            ·
              refine ⟨14940498865310353287461909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9960332576873568858307939 14940498865310353287461909)
              ·
                refine ⟨700335884311422810349777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14940498865310353287461909 700335884311422810349777)
                ·
                  refine ⟨525251913233567107762333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 700335884311422810349777 525251913233567107762333)
                  ·
                    refine ⟨196969467462587665410875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 525251913233567107762333 196969467462587665410875)
                    ·
                      rfl

theorem cell22_575395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 3].length) (baseStart_575395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575395 prefixEnd_575395 := by exact prefixLift 575395
  have htrace : WordTrace (prefixWord ++ tailWord_575395) baseStart_575395 baseEnd_575395 := by
    simpa [prefixWord, tailWord_575395, baseEnd_575395] using wordTrace_append hprefix tailTrace_575395
  have hstable : (prefixWord ++ tailWord_575395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575395).length < 2 ^ (prefixWord ++ tailWord_575395).sum := by decide
  have hdescent : baseEnd_575395 < baseStart_575395 := by decide
  rcases family_descends (prefixWord ++ tailWord_575395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575446 : List Nat := [5, 2, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_575446 : Nat := 118140960795 + 575446 * 2 ^ 59
def prefixEnd_575446 : Nat := 4983230072969 + 3 ^ 40 * 575446 * 2
def baseEnd_575446 : Nat := 196986925804840532385719

theorem tailTrace_575446 : CollatzResearch.WordTrace tailWord_575446 prefixEnd_575446 196986925804840532385719 := by
  unfold tailWord_575446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1311764992079055949848137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13992159915509930131713461 1311764992079055949848137)
  ·
    refine ⟨983823744059291962386103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1311764992079055949848137 983823744059291962386103)
    ·
      refine ⟨1475735616088937943579155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 983823744059291962386103 1475735616088937943579155)
      ·
        refine ⟨2213603424133406915368733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1475735616088937943579155 2213603424133406915368733)
        ·
          refine ⟨830101284050027593263275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2213603424133406915368733 830101284050027593263275)
          ·
            refine ⟨1245151926075041389894913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830101284050027593263275 1245151926075041389894913)
            ·
              refine ⟨933863944556281042421185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1245151926075041389894913 933863944556281042421185)
              ·
                refine ⟨700397958417210781815889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 933863944556281042421185 700397958417210781815889)
                ·
                  refine ⟨525298468812908086361917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 700397958417210781815889 525298468812908086361917)
                  ·
                    refine ⟨196986925804840532385719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 525298468812908086361917 196986925804840532385719)
                    ·
                      rfl

theorem cell22_575446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_575446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575446 prefixEnd_575446 := by exact prefixLift 575446
  have htrace : WordTrace (prefixWord ++ tailWord_575446) baseStart_575446 baseEnd_575446 := by
    simpa [prefixWord, tailWord_575446, baseEnd_575446] using wordTrace_append hprefix tailTrace_575446
  have hstable : (prefixWord ++ tailWord_575446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575446).length < 2 ^ (prefixWord ++ tailWord_575446).sum := by decide
  have hdescent : baseEnd_575446 < baseStart_575446 := by decide
  rcases family_descends (prefixWord ++ tailWord_575446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575534 : List Nat := [4, 1, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_575534 : Nat := 118140960795 + 575534 * 2 ^ 59
def prefixEnd_575534 : Nat := 4983230072969 + 3 ^ 40 * 575534 * 2
def baseEnd_575534 : Nat := 197017050003237636185449

theorem tailTrace_575534 : CollatzResearch.WordTrace tailWord_575534 prefixEnd_575534 197017050003237636185449 := by
  unfold tailWord_575534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2623931187118260778346707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13994299664630724151182437 2623931187118260778346707)
  ·
    refine ⟨3935896780677391167520061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2623931187118260778346707 3935896780677391167520061)
    ·
      refine ⟨1475961292754021687820023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3935896780677391167520061 1475961292754021687820023)
      ·
        refine ⟨2213941939131032531730035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1475961292754021687820023 2213941939131032531730035)
        ·
          refine ⟨3320912908696548797595053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2213941939131032531730035 3320912908696548797595053)
          ·
            refine ⟨1245342340761205799098145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3320912908696548797595053 1245342340761205799098145)
            ·
              refine ⟨934006755570904349323609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1245342340761205799098145 934006755570904349323609)
              ·
                refine ⟨700505066678178261992707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 934006755570904349323609 700505066678178261992707)
                ·
                  refine ⟨1050757600017267392989061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700505066678178261992707 1050757600017267392989061)
                  ·
                    refine ⟨197017050003237636185449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1050757600017267392989061 197017050003237636185449)
                    ·
                      rfl

theorem cell22_575534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_575534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575534 prefixEnd_575534 := by exact prefixLift 575534
  have htrace : WordTrace (prefixWord ++ tailWord_575534) baseStart_575534 baseEnd_575534 := by
    simpa [prefixWord, tailWord_575534, baseEnd_575534] using wordTrace_append hprefix tailTrace_575534
  have hstable : (prefixWord ++ tailWord_575534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575534).length < 2 ^ (prefixWord ++ tailWord_575534).sum := by decide
  have hdescent : baseEnd_575534 < baseStart_575534 := by decide
  rcases family_descends (prefixWord ++ tailWord_575534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575581 : List Nat := [1, 4, 4, 1, 1, 2, 1, 3, 2, 3]
def baseStart_575581 : Nat := 118140960795 + 575581 * 2 ^ 59
def prefixEnd_575581 : Nat := 4983230072969 + 3 ^ 40 * 575581 * 2
def baseEnd_575581 : Nat := 197033139063745180260305

theorem tailTrace_575581 : CollatzResearch.WordTrace tailWord_575581 prefixEnd_575581 197033139063745180260305 := by
  unfold tailWord_575581
  simp only [CollatzResearch.WordTrace]
  refine ⟨20993163727775813253734597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13995442485183875502489731 20993163727775813253734597)
  ·
    refine ⟨3936218198957964985075237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20993163727775813253734597 3936218198957964985075237)
    ·
      refine ⟨738040912304618434701607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3936218198957964985075237 738040912304618434701607)
      ·
        refine ⟨1107061368456927652052411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 738040912304618434701607 1107061368456927652052411)
        ·
          refine ⟨1660592052685391478078617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107061368456927652052411 1660592052685391478078617)
          ·
            refine ⟨1245444039514043608558963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1660592052685391478078617 1245444039514043608558963)
            ·
              refine ⟨1868166059271065412838445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1245444039514043608558963 1868166059271065412838445)
              ·
                refine ⟨700562272226649529814417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1868166059271065412838445 700562272226649529814417)
                ·
                  refine ⟨525421704169987147360813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 700562272226649529814417 525421704169987147360813)
                  ·
                    refine ⟨197033139063745180260305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 525421704169987147360813 197033139063745180260305)
                    ·
                      rfl

theorem cell22_575581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_575581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575581 prefixEnd_575581 := by exact prefixLift 575581
  have htrace : WordTrace (prefixWord ++ tailWord_575581) baseStart_575581 baseEnd_575581 := by
    simpa [prefixWord, tailWord_575581, baseEnd_575581] using wordTrace_append hprefix tailTrace_575581
  have hstable : (prefixWord ++ tailWord_575581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575581).length < 2 ^ (prefixWord ++ tailWord_575581).sum := by decide
  have hdescent : baseEnd_575581 < baseStart_575581 := by decide
  rcases family_descends (prefixWord ++ tailWord_575581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575626 : List Nat := [3, 1, 2, 3, 1, 3, 1, 4, 1, 3]
def baseStart_575626 : Nat := 118140960795 + 575626 * 2 ^ 59
def prefixEnd_575626 : Nat := 4983230072969 + 3 ^ 40 * 575626 * 2
def baseEnd_575626 : Nat := 197048543483380062885167

theorem tailTrace_575626 : CollatzResearch.WordTrace tailWord_575626 prefixEnd_575626 197048543483380062885167 := by
  unfold tailWord_575626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5248701253153196484780683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13996536675075190626081821 5248701253153196484780683)
  ·
    refine ⟨7873051879729794727171025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5248701253153196484780683 7873051879729794727171025)
    ·
      refine ⟨5904788909797346045378269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7873051879729794727171025 5904788909797346045378269)
      ·
        refine ⟨2214295841174004767016851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5904788909797346045378269 2214295841174004767016851)
        ·
          refine ⟨3321443761761007150525277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2214295841174004767016851 3321443761761007150525277)
          ·
            refine ⟨1245541410660377681446979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3321443761761007150525277 1245541410660377681446979)
            ·
              refine ⟨1868312115990566522170469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1245541410660377681446979 1868312115990566522170469)
              ·
                refine ⟨350308521748231222906963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1868312115990566522170469 350308521748231222906963)
                ·
                  refine ⟨525462782622346834360445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350308521748231222906963 525462782622346834360445)
                  ·
                    refine ⟨197048543483380062885167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 525462782622346834360445 197048543483380062885167)
                    ·
                      rfl

theorem cell22_575626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_575626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575626 prefixEnd_575626 := by exact prefixLift 575626
  have htrace : WordTrace (prefixWord ++ tailWord_575626) baseStart_575626 baseEnd_575626 := by
    simpa [prefixWord, tailWord_575626, baseEnd_575626] using wordTrace_append hprefix tailTrace_575626
  have hstable : (prefixWord ++ tailWord_575626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575626).length < 2 ^ (prefixWord ++ tailWord_575626).sum := by decide
  have hdescent : baseEnd_575626 < baseStart_575626 := by decide
  rcases family_descends (prefixWord ++ tailWord_575626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575684 : List Nat := [2, 3, 3, 1, 2, 2, 2, 1, 6]
def baseStart_575684 : Nat := 118140960795 + 575684 * 2 ^ 59
def prefixEnd_575684 : Nat := 4983230072969 + 3 ^ 40 * 575684 * 2
def baseEnd_575684 : Nat := 65689466022895748311663

theorem tailTrace_575684 : CollatzResearch.WordTrace tailWord_575684 prefixEnd_575684 65689466022895748311663 := by
  unfold tailWord_575684
  simp only [CollatzResearch.WordTrace]
  refine ⟨10498460223201330922367053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13997946964268441229822737 10498460223201330922367053)
  ·
    refine ⟨3936922583700499095887645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10498460223201330922367053 3936922583700499095887645)
    ·
      refine ⟨1476345968887687160957867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3936922583700499095887645 1476345968887687160957867)
      ·
        refine ⟨2214518953331530741436801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1476345968887687160957867 2214518953331530741436801)
        ·
          refine ⟨1660889214998648056077601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2214518953331530741436801 1660889214998648056077601)
          ·
            refine ⟨1245666911248986042058201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1660889214998648056077601 1245666911248986042058201)
            ·
              refine ⟨934250183436739531543651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1245666911248986042058201 934250183436739531543651)
              ·
                refine ⟨1401375275155109297315477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934250183436739531543651 1401375275155109297315477)
                ·
                  refine ⟨65689466022895748311663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1401375275155109297315477 65689466022895748311663)
                  ·
                    rfl

theorem cell22_575684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_575684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575684 prefixEnd_575684 := by exact prefixLift 575684
  have htrace : WordTrace (prefixWord ++ tailWord_575684) baseStart_575684 baseEnd_575684 := by
    simpa [prefixWord, tailWord_575684, baseEnd_575684] using wordTrace_append hprefix tailTrace_575684
  have hstable : (prefixWord ++ tailWord_575684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575684).length < 2 ^ (prefixWord ++ tailWord_575684).sum := by decide
  have hdescent : baseEnd_575684 < baseStart_575684 := by decide
  rcases family_descends (prefixWord ++ tailWord_575684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575695 : List Nat := [1, 1, 2, 1, 1, 3, 4, 9]
def baseStart_575695 : Nat := 118140960795 + 575695 * 2 ^ 59
def prefixEnd_575695 : Nat := 4983230072969 + 3 ^ 40 * 575695 * 2
def baseEnd_575695 : Nat := 21896907065942986989995

theorem tailTrace_575695 : CollatzResearch.WordTrace tailWord_575695 prefixEnd_575695 21896907065942986989995 := by
  unfold tailWord_575695
  simp only [CollatzResearch.WordTrace]
  refine ⟨20997321649362810723384539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13998214432908540482256359 20997321649362810723384539)
  ·
    refine ⟨31495982474044216085076809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20997321649362810723384539 31495982474044216085076809)
    ·
      refine ⟨23621986855533162063807607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31495982474044216085076809 23621986855533162063807607)
      ·
        refine ⟨35432980283299743095711411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23621986855533162063807607 35432980283299743095711411)
        ·
          refine ⟨53149470424949614643567117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35432980283299743095711411 53149470424949614643567117)
          ·
            refine ⟨19931051409356105491337669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53149470424949614643567117 19931051409356105491337669)
            ·
              refine ⟨3737072139254269779625813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19931051409356105491337669 3737072139254269779625813)
              ·
                refine ⟨21896907065942986989995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3737072139254269779625813 21896907065942986989995)
                ·
                  rfl

theorem cell22_575695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 9].length) (baseStart_575695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575695 prefixEnd_575695 := by exact prefixLift 575695
  have htrace : WordTrace (prefixWord ++ tailWord_575695) baseStart_575695 baseEnd_575695 := by
    simpa [prefixWord, tailWord_575695, baseEnd_575695] using wordTrace_append hprefix tailTrace_575695
  have hstable : (prefixWord ++ tailWord_575695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575695).length < 2 ^ (prefixWord ++ tailWord_575695).sum := by decide
  have hdescent : baseEnd_575695 < baseStart_575695 := by decide
  rcases family_descends (prefixWord ++ tailWord_575695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575744 : List Nat := [2, 1, 1, 2, 1, 1, 7, 1, 3, 3]
def baseStart_575744 : Nat := 118140960795 + 575744 * 2 ^ 59
def prefixEnd_575744 : Nat := 4983230072969 + 3 ^ 40 * 575744 * 2
def baseEnd_575744 : Nat := 197088937294867088434805

theorem tailTrace_575744 : CollatzResearch.WordTrace tailWord_575744 prefixEnd_575744 197088937294867088434805 := by
  unfold tailWord_575744
  simp only [CollatzResearch.WordTrace]
  refine ⟨10499554413092646045959143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13999405884123528061278857 10499554413092646045959143)
  ·
    refine ⟨15749331619638969068938715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10499554413092646045959143 15749331619638969068938715)
    ·
      refine ⟨23623997429458453603408073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15749331619638969068938715 23623997429458453603408073)
      ·
        refine ⟨17717998072093840202556055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23623997429458453603408073 17717998072093840202556055)
        ·
          refine ⟨26576997108140760303834083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17717998072093840202556055 26576997108140760303834083)
          ·
            refine ⟨39865495662211140455751125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26576997108140760303834083 39865495662211140455751125)
            ·
              refine ⟨934347554583073604431667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 39865495662211140455751125 934347554583073604431667)
              ·
                refine ⟨1401521331874610406647501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934347554583073604431667 1401521331874610406647501)
                ·
                  refine ⟨525570499452978902492813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1401521331874610406647501 525570499452978902492813)
                  ·
                    refine ⟨197088937294867088434805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 525570499452978902492813 197088937294867088434805)
                    ·
                      rfl

theorem cell22_575744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 3, 3].length) (baseStart_575744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575744 prefixEnd_575744 := by exact prefixLift 575744
  have htrace : WordTrace (prefixWord ++ tailWord_575744) baseStart_575744 baseEnd_575744 := by
    simpa [prefixWord, tailWord_575744, baseEnd_575744] using wordTrace_append hprefix tailTrace_575744
  have hstable : (prefixWord ++ tailWord_575744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575744).length < 2 ^ (prefixWord ++ tailWord_575744).sum := by decide
  have hdescent : baseEnd_575744 < baseStart_575744 := by decide
  rcases family_descends (prefixWord ++ tailWord_575744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575772 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 4, 5]
def baseStart_575772 : Nat := 118140960795 + 575772 * 2 ^ 59
def prefixEnd_575772 : Nat := 4983230072969 + 3 ^ 40 * 575772 * 2
def baseEnd_575772 : Nat := 197098522267084348734719

theorem tailTrace_575772 : CollatzResearch.WordTrace tailWord_575772 prefixEnd_575772 197098522267084348734719 := by
  unfold tailWord_575772
  simp only [CollatzResearch.WordTrace]
  refine ⟨10500065035041926436968785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14000086713389235249291713 10500065035041926436968785)
  ·
    refine ⟨7875048776281444827726589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10500065035041926436968785 7875048776281444827726589)
    ·
      refine ⟨2953143291105541810397471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7875048776281444827726589 2953143291105541810397471)
      ·
        refine ⟨4429714936658312715596207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2953143291105541810397471 4429714936658312715596207)
        ·
          refine ⟨6644572404987469073394311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4429714936658312715596207 6644572404987469073394311)
          ·
            refine ⟨9966858607481203610091467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6644572404987469073394311 9966858607481203610091467)
            ·
              refine ⟨14950287911221805415137201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9966858607481203610091467 14950287911221805415137201)
              ·
                refine ⟨11212715933416354061352901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14950287911221805415137201 11212715933416354061352901)
                ·
                  refine ⟨2102384237515566386503669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11212715933416354061352901 2102384237515566386503669)
                  ·
                    refine ⟨197098522267084348734719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2102384237515566386503669 197098522267084348734719)
                    ·
                      rfl

theorem cell22_575772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_575772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575772 prefixEnd_575772 := by exact prefixLift 575772
  have htrace : WordTrace (prefixWord ++ tailWord_575772) baseStart_575772 baseEnd_575772 := by
    simpa [prefixWord, tailWord_575772, baseEnd_575772] using wordTrace_append hprefix tailTrace_575772
  have hstable : (prefixWord ++ tailWord_575772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575772).length < 2 ^ (prefixWord ++ tailWord_575772).sum := by decide
  have hdescent : baseEnd_575772 < baseStart_575772 := by decide
  rcases family_descends (prefixWord ++ tailWord_575772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575834 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 4, 3]
def baseStart_575834 : Nat := 118140960795 + 575834 * 2 ^ 59
def prefixEnd_575834 : Nat := 4983230072969 + 3 ^ 40 * 575834 * 2
def baseEnd_575834 : Nat := 197119746134136853684529

theorem tailTrace_575834 : CollatzResearch.WordTrace tailWord_575834 prefixEnd_575834 197119746134136853684529 := by
  unfold tailWord_575834
  simp only [CollatzResearch.WordTrace]
  refine ⟨5250597848964809365673639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14001594263906158308463037 5250597848964809365673639)
  ·
    refine ⟨7875896773447214048510459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5250597848964809365673639 7875896773447214048510459)
    ·
      refine ⟨11813845160170821072765689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7875896773447214048510459 11813845160170821072765689)
      ·
        refine ⟨8860383870128115804574267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11813845160170821072765689 8860383870128115804574267)
        ·
          refine ⟨13290575805192173706861401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8860383870128115804574267 13290575805192173706861401)
          ·
            refine ⟨9967931853894130280146051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13290575805192173706861401 9967931853894130280146051)
            ·
              refine ⟨14951897780841195420219077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9967931853894130280146051 14951897780841195420219077)
              ·
                refine ⟨2803480833907724141291077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14951897780841195420219077 2803480833907724141291077)
                ·
                  refine ⟨525652656357698276492077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2803480833907724141291077 525652656357698276492077)
                  ·
                    refine ⟨197119746134136853684529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 525652656357698276492077 197119746134136853684529)
                    ·
                      rfl

theorem cell22_575834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_575834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575834 prefixEnd_575834 := by exact prefixLift 575834
  have htrace : WordTrace (prefixWord ++ tailWord_575834) baseStart_575834 baseEnd_575834 := by
    simpa [prefixWord, tailWord_575834, baseEnd_575834] using wordTrace_append hprefix tailTrace_575834
  have hstable : (prefixWord ++ tailWord_575834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575834).length < 2 ^ (prefixWord ++ tailWord_575834).sum := by decide
  have hdescent : baseEnd_575834 < baseStart_575834 := by decide
  rcases family_descends (prefixWord ++ tailWord_575834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575881 : List Nat := [1, 2, 1, 1, 6, 3, 2, 6]
def baseStart_575881 : Nat := 118140960795 + 575881 * 2 ^ 59
def prefixEnd_575881 : Nat := 4983230072969 + 3 ^ 40 * 575881 * 2
def baseEnd_575881 : Nat := 21903981688293821973265

theorem tailTrace_575881 : CollatzResearch.WordTrace tailWord_575881 prefixEnd_575881 21903981688293821973265 := by
  unfold tailWord_575881
  simp only [CollatzResearch.WordTrace]
  refine ⟨21004105626688964489655497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14002737084459309659770331 21004105626688964489655497)
  ·
    refine ⟨15753079220016723367241623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21004105626688964489655497 15753079220016723367241623)
    ·
      refine ⟨23629618830025085050862435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15753079220016723367241623 23629618830025085050862435)
      ·
        refine ⟨35444428245037627576293653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23629618830025085050862435 35444428245037627576293653)
        ·
          refine ⟨1661457573986138792638765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35444428245037627576293653 1661457573986138792638765)
          ·
            refine ⟨623046590244802047239537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1661457573986138792638765 623046590244802047239537)
            ·
              refine ⟨467284942683601535429653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 623046590244802047239537 467284942683601535429653)
              ·
                refine ⟨21903981688293821973265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 467284942683601535429653 21903981688293821973265)
                ·
                  rfl

theorem cell22_575881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 6].length) (baseStart_575881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575881 prefixEnd_575881 := by exact prefixLift 575881
  have htrace : WordTrace (prefixWord ++ tailWord_575881) baseStart_575881 baseEnd_575881 := by
    simpa [prefixWord, tailWord_575881, baseEnd_575881] using wordTrace_append hprefix tailTrace_575881
  have hstable : (prefixWord ++ tailWord_575881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575881).length < 2 ^ (prefixWord ++ tailWord_575881).sum := by decide
  have hdescent : baseEnd_575881 < baseStart_575881 := by decide
  rcases family_descends (prefixWord ++ tailWord_575881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575909 : List Nat := [1, 3, 1, 2, 1, 1, 4, 4, 5]
def baseStart_575909 : Nat := 118140960795 + 575909 * 2 ^ 59
def prefixEnd_575909 : Nat := 4983230072969 + 3 ^ 40 * 575909 * 2
def baseEnd_575909 : Nat := 65715140055620552686433

theorem tailTrace_575909 : CollatzResearch.WordTrace tailWord_575909 prefixEnd_575909 65715140055620552686433 := by
  unfold tailWord_575909
  simp only [CollatzResearch.WordTrace]
  refine ⟨21005126870587525271674781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14003417913725016847783187 21005126870587525271674781)
  ·
    refine ⟨7876922576470321976878043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21005126870587525271674781 7876922576470321976878043)
    ·
      refine ⟨11815383864705482965317065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7876922576470321976878043 11815383864705482965317065)
      ·
        refine ⟨8861537898529112223987799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11815383864705482965317065 8861537898529112223987799)
        ·
          refine ⟨13292306847793668335981699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8861537898529112223987799 13292306847793668335981699)
          ·
            refine ⟨19938460271690502503972549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13292306847793668335981699 19938460271690502503972549)
            ·
              refine ⟨3738461300941969219494853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19938460271690502503972549 3738461300941969219494853)
              ·
                refine ⟨700961493926619228655285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3738461300941969219494853 700961493926619228655285)
                ·
                  refine ⟨65715140055620552686433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 700961493926619228655285 65715140055620552686433)
                  ·
                    rfl

theorem cell22_575909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_575909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575909 prefixEnd_575909 := by exact prefixLift 575909
  have htrace : WordTrace (prefixWord ++ tailWord_575909) baseStart_575909 baseEnd_575909 := by
    simpa [prefixWord, tailWord_575909, baseEnd_575909] using wordTrace_append hprefix tailTrace_575909
  have hstable : (prefixWord ++ tailWord_575909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575909).length < 2 ^ (prefixWord ++ tailWord_575909).sum := by decide
  have hdescent : baseEnd_575909 < baseStart_575909 := by decide
  rcases family_descends (prefixWord ++ tailWord_575909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575969 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 3, 5]
def baseStart_575969 : Nat := 118140960795 + 575969 * 2 ^ 59
def prefixEnd_575969 : Nat := 4983230072969 + 3 ^ 40 * 575969 * 2
def baseEnd_575969 : Nat := 197165959393041501559115

theorem tailTrace_575969 : CollatzResearch.WordTrace tailWord_575969 prefixEnd_575969 197165959393041501559115 := by
  unfold tailWord_575969
  simp only [CollatzResearch.WordTrace]
  refine ⟨21007315250370155518858961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14004876833580103679239307 21007315250370155518858961)
  ·
    refine ⟨15755486437777616639144221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21007315250370155518858961 15755486437777616639144221)
    ·
      refine ⟨5908307414166606239679083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15755486437777616639144221 5908307414166606239679083)
      ·
        refine ⟨8862461121249909359518625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5908307414166606239679083 8862461121249909359518625)
        ·
          refine ⟨6646845840937432019638969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8862461121249909359518625 6646845840937432019638969)
          ·
            refine ⟨4985134380703074014729227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6646845840937432019638969 4985134380703074014729227)
            ·
              refine ⟨7477701571054611022093841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4985134380703074014729227 7477701571054611022093841)
              ·
                refine ⟨5608276178290958266570381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7477701571054611022093841 5608276178290958266570381)
                ·
                  refine ⟨2103103566859109349963893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5608276178290958266570381 2103103566859109349963893)
                  ·
                    refine ⟨197165959393041501559115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2103103566859109349963893 197165959393041501559115)
                    ·
                      rfl

theorem cell22_575969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_575969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575969 prefixEnd_575969 := by exact prefixLift 575969
  have htrace : WordTrace (prefixWord ++ tailWord_575969) baseStart_575969 baseEnd_575969 := by
    simpa [prefixWord, tailWord_575969, baseEnd_575969] using wordTrace_append hprefix tailTrace_575969
  have hstable : (prefixWord ++ tailWord_575969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575969).length < 2 ^ (prefixWord ++ tailWord_575969).sum := by decide
  have hdescent : baseEnd_575969 < baseStart_575969 := by decide
  rcases family_descends (prefixWord ++ tailWord_575969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575984 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 1, 6]
def baseStart_575984 : Nat := 118140960795 + 575984 * 2 ^ 59
def prefixEnd_575984 : Nat := 4983230072969 + 3 ^ 40 * 575984 * 2
def baseEnd_575984 : Nat := 197171094199586462434069

theorem tailTrace_575984 : CollatzResearch.WordTrace tailWord_575984 prefixEnd_575984 197171094199586462434069 := by
  unfold tailWord_575984
  simp only [CollatzResearch.WordTrace]
  refine ⟨10503931172657906540327503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14005241563543875387103337 10503931172657906540327503)
  ·
    refine ⟨15755896758986859810491255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10503931172657906540327503 15755896758986859810491255)
    ·
      refine ⟨23633845138480289715736883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15755896758986859810491255 23633845138480289715736883)
      ·
        refine ⟨35450767707720434573605325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23633845138480289715736883 35450767707720434573605325)
        ·
          refine ⟨13294037890395162965101997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35450767707720434573605325 13294037890395162965101997)
          ·
            refine ⟨4985264208898186111913249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13294037890395162965101997 4985264208898186111913249)
            ·
              refine ⟨3738948156673639583934937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4985264208898186111913249 3738948156673639583934937)
              ·
                refine ⟨2804211117505229687951203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3738948156673639583934937 2804211117505229687951203)
                ·
                  refine ⟨4206316676257844531926805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2804211117505229687951203 4206316676257844531926805)
                  ·
                    refine ⟨197171094199586462434069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4206316676257844531926805 197171094199586462434069)
                    ·
                      rfl

theorem cell22_575984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_575984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_575984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_575984 prefixEnd_575984 := by exact prefixLift 575984
  have htrace : WordTrace (prefixWord ++ tailWord_575984) baseStart_575984 baseEnd_575984 := by
    simpa [prefixWord, tailWord_575984, baseEnd_575984] using wordTrace_append hprefix tailTrace_575984
  have hstable : (prefixWord ++ tailWord_575984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575984).length < 2 ^ (prefixWord ++ tailWord_575984).sum := by decide
  have hdescent : baseEnd_575984 < baseStart_575984 := by decide
  rcases family_descends (prefixWord ++ tailWord_575984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576001 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 1, 6]
def baseStart_576001 : Nat := 118140960795 + 576001 * 2 ^ 59
def prefixEnd_576001 : Nat := 4983230072969 + 3 ^ 40 * 576001 * 2
def baseEnd_576001 : Nat := 197176913647004084759017

theorem tailTrace_576001 : CollatzResearch.WordTrace tailWord_576001 prefixEnd_576001 197176913647004084759017 := by
  unfold tailWord_576001
  simp only [CollatzResearch.WordTrace]
  refine ⟨21008482386254224984023857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14005654924169483322682571 21008482386254224984023857)
  ·
    refine ⟨15756361789690668738017893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21008482386254224984023857 15756361789690668738017893)
    ·
      refine ⟨2954317835567000388378355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15756361789690668738017893 2954317835567000388378355)
      ·
        refine ⟨4431476753350500582567533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2954317835567000388378355 4431476753350500582567533)
        ·
          refine ⟨1661803782506437718462825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4431476753350500582567533 1661803782506437718462825)
          ·
            refine ⟨1246352836879828288847119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1661803782506437718462825 1246352836879828288847119)
            ·
              refine ⟨1869529255319742433270679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1246352836879828288847119 1869529255319742433270679)
              ·
                refine ⟨2804293882979613649906019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1869529255319742433270679 2804293882979613649906019)
                ·
                  refine ⟨4206440824469420474859029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2804293882979613649906019 4206440824469420474859029)
                  ·
                    refine ⟨197176913647004084759017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4206440824469420474859029 197176913647004084759017)
                    ·
                      rfl

theorem cell22_576001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_576001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576001 prefixEnd_576001 := by exact prefixLift 576001
  have htrace : WordTrace (prefixWord ++ tailWord_576001) baseStart_576001 baseEnd_576001 := by
    simpa [prefixWord, tailWord_576001, baseEnd_576001] using wordTrace_append hprefix tailTrace_576001
  have hstable : (prefixWord ++ tailWord_576001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576001).length < 2 ^ (prefixWord ++ tailWord_576001).sum := by decide
  have hdescent : baseEnd_576001 < baseStart_576001 := by decide
  rcases family_descends (prefixWord ++ tailWord_576001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576007 : List Nat := [1, 1, 4, 3, 4, 1, 2, 1, 1, 4]
def baseStart_576007 : Nat := 118140960795 + 576007 * 2 ^ 59
def prefixEnd_576007 : Nat := 4983230072969 + 3 ^ 40 * 576007 * 2
def baseEnd_576007 : Nat := 197178967569622069108999

theorem tailTrace_576007 : CollatzResearch.WordTrace tailWord_576007 prefixEnd_576007 197178967569622069108999 := by
  unfold tailWord_576007
  simp only [CollatzResearch.WordTrace]
  refine ⟨21008701224232488008742275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14005800816154992005828183 21008701224232488008742275)
  ·
    refine ⟨31513051836348732013113413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21008701224232488008742275 31513051836348732013113413)
    ·
      refine ⟨5908697219315387252458765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31513051836348732013113413 5908697219315387252458765)
      ·
        refine ⟨2215761457243270219672037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5908697219315387252458765 2215761457243270219672037)
        ·
          refine ⟨415455273233113166188507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2215761457243270219672037 415455273233113166188507)
          ·
            refine ⟨623182909849669749282761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415455273233113166188507 623182909849669749282761)
            ·
              refine ⟨467387182387252311962071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 623182909849669749282761 467387182387252311962071)
              ·
                refine ⟨701080773580878467943107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 467387182387252311962071 701080773580878467943107)
                ·
                  refine ⟨1051621160371317701914661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701080773580878467943107 1051621160371317701914661)
                  ·
                    refine ⟨197178967569622069108999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1051621160371317701914661 197178967569622069108999)
                    ·
                      rfl

theorem cell22_576007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_576007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576007 prefixEnd_576007 := by exact prefixLift 576007
  have htrace : WordTrace (prefixWord ++ tailWord_576007) baseStart_576007 baseEnd_576007 := by
    simpa [prefixWord, tailWord_576007, baseEnd_576007] using wordTrace_append hprefix tailTrace_576007
  have hstable : (prefixWord ++ tailWord_576007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576007).length < 2 ^ (prefixWord ++ tailWord_576007).sum := by decide
  have hdescent : baseEnd_576007 < baseStart_576007 := by decide
  rcases family_descends (prefixWord ++ tailWord_576007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576020 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_576020 : Nat := 118140960795 + 576020 * 2 ^ 59
def prefixEnd_576020 : Nat := 4983230072969 + 3 ^ 40 * 576020 * 2
def baseEnd_576020 : Nat := 197183417735294368533959

theorem tailTrace_576020 : CollatzResearch.WordTrace tailWord_576020 prefixEnd_576020 197183417735294368533959 := by
  unfold tailWord_576020
  simp only [CollatzResearch.WordTrace]
  refine ⟨10504587686592695614482757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14006116915456927485977009 10504587686592695614482757)
  ·
    refine ⟨1969610191236130427715517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10504587686592695614482757 1969610191236130427715517)
    ·
      refine ⟨738603821713548910393319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1969610191236130427715517 738603821713548910393319)
      ·
        refine ⟨1107905732570323365589979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 738603821713548910393319 1107905732570323365589979)
        ·
          refine ⟨1661858598855485048384969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107905732570323365589979 1661858598855485048384969)
          ·
            refine ⟨1246393949141613786288727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1661858598855485048384969 1246393949141613786288727)
            ·
              refine ⟨1869590923712420679433091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1246393949141613786288727 1869590923712420679433091)
              ·
                refine ⟨2804386385568631019149637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1869590923712420679433091 2804386385568631019149637)
                ·
                  refine ⟨525822447294118316090557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2804386385568631019149637 525822447294118316090557)
                  ·
                    refine ⟨197183417735294368533959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 525822447294118316090557 197183417735294368533959)
                    ·
                      rfl

theorem cell22_576020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_576020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_576020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_576020 prefixEnd_576020 := by exact prefixLift 576020
  have htrace : WordTrace (prefixWord ++ tailWord_576020) baseStart_576020 baseEnd_576020 := by
    simpa [prefixWord, tailWord_576020, baseEnd_576020] using wordTrace_append hprefix tailTrace_576020
  have hstable : (prefixWord ++ tailWord_576020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576020).length < 2 ^ (prefixWord ++ tailWord_576020).sum := by decide
  have hdescent : baseEnd_576020 < baseStart_576020 := by decide
  rcases family_descends (prefixWord ++ tailWord_576020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
